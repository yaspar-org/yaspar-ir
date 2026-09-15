// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! This module handles expansions of global definitions.
//!
//! A global substitution operation expands global definitions, invoking local substitution
//! whenever necessary. The [`GlobalSubst`] trait provides the main entry point via
//! `.gsubst(names, context)`, which expands the specified global definitions on the fly.
//!
//! # Depth
//!
//! Two things nest here, and neither is bounded in machine-generated input: a term nests in its
//! sub-terms, and a definition nests in the definitions its body mentions. `gsubst_term` and
//! `expand_def` are therefore members of one `#[stack_safe]` group, so a call from either into the
//! other is a step of the same driver and costs no native frame. A chain of a million `define-fun`s
//! expands on any stack.
//!
//! # The cache
//!
//! A definition is expanded once and kept, so its uses cost a substitution rather than a walk.
//! Unfolding a body pushes a `GlobalDef`, which carries the names that body may not expand — its
//! recursive dependencies — together with a memo of the sub-terms already substituted while unfolding
//! it. The memo belongs to that entry rather than to the substituter, because a blocked name changes
//! what a sub-term substitutes to.

use crate::allocator::{SortAllocator, TermAllocator};
use crate::ast::alg::VarBinding;
use crate::ast::subst::Substitute;
use crate::ast::{
    ATerm, Arena, Attribute, Context, FetchSort, FunctionDef, FunctionMetaDefined, HasArena,
    Monomorphization, PatternArm, Sort, Str, Substitution, Term,
};
use crate::raw::alg::rec::Bottom;
use crate::raw::tc::unif::{empty_subst, instantiate_subst};
use crate::traits::{AllocatableString, HasMutRef, Repr};
use std::collections::{HashMap, HashSet};
use std::ops::DerefMut;
use yaspar_macros::stack_safe;

/// Expand global names with their definitions in `Self`.
///
/// This trait implements substitutions by expanding the bodies of names during substitutions.
pub trait GlobalSubst<E> {
    /// The type produced by the substitution.
    type Out;

    /// Apply global substitutions with an iterable of specific names of global definitions to expand.
    fn gsubst<S>(&self, global_names: impl IntoIterator<Item = S>, env: &mut E) -> Self::Out
    where
        S: AllocatableString<Arena>;

    /// Like [`gsubst`](Self::gsubst), but accepts a pre-allocated set of names.
    fn gsubst_with_names(&self, global_names: &HashSet<Str>, env: &mut E) -> Self::Out;

    /// Apply global substitutions to all global definitions
    ///
    /// Resolving the set of defined symbols costs a scan of the whole symbol table, so it is
    /// proportional to the number of *declared* symbols however few are defined. With the `cache`
    /// feature the set is memoized until the symbol table is next written to, which is what keeps
    /// a loop of per-term calls from being quadratic in script size; without it every call pays
    /// the scan. Calling this once on a `&[Term]` is better still, since a batch also shares one
    /// term memoization cache.
    fn gsubst_all(&self, env: &mut E) -> Self::Out;
}

impl<Ctx> GlobalSubst<Ctx> for [Term]
where
    Ctx: HasMutRef<Context>,
{
    type Out = Vec<Term>;

    fn gsubst<S>(&self, global_names: impl IntoIterator<Item = S>, env: &mut Ctx) -> Self::Out
    where
        S: AllocatableString<Arena>,
    {
        let mut rf = env.ref_mut();
        let global_names = {
            global_names
                .into_iter()
                .map(|s| s.allocate(rf.arena()))
                .collect::<HashSet<_>>()
        };
        let mut cache = HashMap::new();
        let block = HashSet::new();
        let mut gsubster =
            GlobalSubstituter::create(rf.deref_mut(), &global_names, &block, &mut cache);
        self.iter().map(|t| gsubster.run(t)).collect()
    }

    fn gsubst_with_names(&self, global_names: &HashSet<Str>, env: &mut Ctx) -> Self::Out {
        let mut cache = HashMap::new();
        let block = HashSet::new();
        let mut rf = env.ref_mut();
        let mut gsubster =
            GlobalSubstituter::create(rf.deref_mut(), global_names, &block, &mut cache);
        self.iter().map(|t| gsubster.run(t)).collect()
    }

    fn gsubst_all(&self, env: &mut Ctx) -> Self::Out {
        let block = HashSet::new();
        let mut rf = env.ref_mut();
        let global_names = rf.defined_symbols();
        #[cfg(feature = "cache")]
        {
            let mut cache = std::mem::take(&mut rf.caches.global_def_cache);
            let mut gsubster =
                GlobalSubstituter::create(rf.deref_mut(), &global_names, &block, &mut cache);
            let r = self.iter().map(|t| gsubster.run(t)).collect();
            rf.caches.global_def_cache = cache;
            r
        }
        #[cfg(not(feature = "cache"))]
        {
            let mut cache = HashMap::new();
            let mut gsubster =
                GlobalSubstituter::create(rf.deref_mut(), &global_names, &block, &mut cache);
            self.iter().map(|t| gsubster.run(t)).collect()
        }
    }
}

impl<Ctx> GlobalSubst<Ctx> for Term
where
    Ctx: HasMutRef<Context>,
{
    type Out = Term;

    fn gsubst<S>(&self, global_names: impl IntoIterator<Item = S>, env: &mut Ctx) -> Self::Out
    where
        S: AllocatableString<Arena>,
    {
        std::slice::from_ref(self)
            .gsubst(global_names, env)
            .pop()
            .unwrap()
    }

    fn gsubst_with_names(&self, global_names: &HashSet<Str>, env: &mut Ctx) -> Self::Out {
        std::slice::from_ref(self)
            .gsubst_with_names(global_names, env)
            .pop()
            .unwrap()
    }

    fn gsubst_all(&self, env: &mut Ctx) -> Self::Out {
        std::slice::from_ref(self).gsubst_all(env).pop().unwrap()
    }
}

/// A global definition being unfolded: the names its body may not expand, and what it has already
/// substituted.
///
/// The outermost one stands for the call itself rather than a definition, and blocks whatever the
/// caller asked to block.
struct GlobalDef {
    /// The recursive dependencies of the definition being unfolded, which stay unexpanded.
    blocked: HashSet<Str>,
    /// Sub-terms already substituted while unfolding it.
    memo: HashMap<Term, Term>,
}

/// A global definition expander. Use [`GlobalSubstituter::create`] to construct.
///
/// Expands global definitions (from `define-fun` and friends) by inlining their bodies, applying
/// monomorphization for a parametric definition.
pub struct GlobalSubstituter<'a> {
    /// Where terms are built, and where definitions are looked up.
    arena: &'a mut Context,
    /// The names to expand.
    global_names: &'a HashSet<Str>,
    /// The definitions expanded so far, shared across scopes.
    global_def_cache: &'a mut HashMap<Str, FunctionDef>,
    /// One entry per global definition being unfolded, innermost last. Never empty.
    unfolding: Vec<GlobalDef>,
}

impl<'a> GlobalSubstituter<'a> {
    /// Create a new global substituter.
    ///
    /// - `ctx`: the context holding global definitions.
    /// - `global_names`: the set of names to expand.
    /// - `block`: names to block from expansion (e.g. to prevent infinite recursion).
    /// - `global_def_cache`: shared cache for resolved function definitions.
    pub fn create(
        ctx: &'a mut Context,
        global_names: &'a HashSet<Str>,
        block: &'a HashSet<Str>,
        global_def_cache: &'a mut HashMap<Str, FunctionDef>,
    ) -> Self {
        Self {
            arena: ctx,
            global_names,
            global_def_cache,
            unfolding: vec![GlobalDef {
                blocked: block.clone(),
                memo: HashMap::new(),
            }],
        }
    }

    /// Expand the global definitions in `t`.
    pub fn run(&mut self, t: &Term) -> Term {
        gsubst_term(t, self)
    }

    /// [`Self::run`], under the name the [`TermRecursor`](crate::ast::TermRecursor) driver gave it.
    ///
    /// The descent is its own driver now, so this is no longer a recursion the trait runs.
    #[deprecated(note = "the descent is not a `TermRecursor` any more, so use `run`")]
    pub fn recurse_on_term_no_err(&mut self, t: &Term) -> Term {
        self.run(t)
    }

    /// [`Self::run`], under the name the [`TermRecursor`](crate::ast::TermRecursor) driver gave it. Expansion cannot fail, so
    /// the answer is always `Ok`.
    #[deprecated(note = "the descent is not a `TermRecursor` any more, so use `run`")]
    pub fn recurse_on_term(&mut self, t: &Term) -> Result<Term, Bottom> {
        Ok(self.run(t))
    }

    /// Whether `sym` is one of the names to expand, here.
    fn expandable(&self, sym: &Str) -> bool {
        self.global_names.contains(sym) && !self.innermost().blocked.contains(sym)
    }

    /// The definition being unfolded, i.e. the one a term is being substituted for.
    fn innermost(&self) -> &GlobalDef {
        self.unfolding.last().expect("the outermost entry")
    }

    /// The definition being unfolded, to record a substitution in.
    fn innermost_mut(&mut self) -> &mut GlobalDef {
        self.unfolding.last_mut().expect("the outermost entry")
    }

    /// What `t` substituted to while unfolding this definition, if it has already been asked for.
    fn memoized(&self, t: &Term) -> Option<Term> {
        self.innermost().memo.get(t).cloned()
    }

    /// Record what `t` substituted to while unfolding this definition.
    fn memoize(&mut self, t: Term, r: Term) {
        self.innermost_mut().memo.insert(t, r);
    }

    /// Start unfolding a definition, blocking the names its body recurses through.
    ///
    /// A memo only answers for the names blocked where it was filled, which is why a body that
    /// blocks something gets its own. A body that blocks nothing new answers the same as its caller,
    /// so it keeps the caller's memo and shares the work — most definitions are not recursive.
    ///
    /// Returns whether an entry was pushed, i.e. whether [`Self::finish_unfolding`] has to pop one.
    fn start_unfolding(&mut self, blocked: HashSet<Str>) -> bool {
        if blocked.is_subset(&self.innermost().blocked) {
            return false;
        }
        let blocked = self.innermost().blocked.union(&blocked).cloned().collect();
        self.unfolding.push(GlobalDef {
            blocked,
            memo: HashMap::new(),
        });
        true
    }

    /// Finish unfolding a definition, dropping what its body memoized.
    fn finish_unfolding(&mut self, pushed: bool) {
        if pushed {
            self.unfolding.pop();
        }
    }
}

/// The substituter used to be a `Memoize` wrapper around an inner recursor; the memo now lives in
/// the substituter itself, so both names say the same thing.
#[deprecated(note = "the memo lives in the substituter now, so use `GlobalSubstituter` directly")]
pub type GlobalSubstituterInner<'a> = GlobalSubstituter<'a>;

impl HasArena for GlobalSubstituter<'_> {
    #[inline]
    fn arena(&mut self) -> &mut Arena {
        self.arena.arena()
    }
}

/// The descent, i.e. the cycle a term and a definition form.
///
/// A term's sub-terms are walked here, and a definition met on the way is expanded by
/// [`expand_def`] — which walks its body, which may mention further definitions. Both directions are
/// members of one group, so the whole descent shares one driver.
#[stack_safe(data_in_frame)]
mod descent {
    use super::*;

    /// Expand the global definitions in `t`.
    ///
    /// A sub-term is reached through the node it sits in, so what travels in a frame is a reference
    /// into the arena rather than anything the driver owns.
    pub fn gsubst_term<'a>(t: &Term, env: &mut GlobalSubstituter<'a>) -> Term {
        if let Some(r) = env.memoized(t) {
            return r;
        }
        let out = match t.repr() {
            ATerm::Constant(..) | ATerm::Local(_) => t.clone(),
            ATerm::Global(qid, sort) => {
                let sym = qid.id_str().clone();
                let sort: Sort = sort.clone().expect("type invariant violation!");
                if env.expandable(&sym) && expand_def(sym.clone(), env) {
                    expand_global(&sym, sort, env)
                } else {
                    t.clone()
                }
            }
            ATerm::App(f, args, sort) => {
                let f = f.clone();
                let sort: Sort = sort.clone().expect("type invariant violation!");
                let recs = gsubst_all_of(args, env);
                let sym = f.id_str().clone();
                if env.expandable(&sym) && expand_def(sym.clone(), env) {
                    expand_app(&sym, recs, sort, env)
                } else {
                    env.arena.app(f, recs, Some(sort))
                }
            }
            ATerm::Eq(a, b) => {
                let a = gsubst_term(a, env);
                let b = gsubst_term(b, env);
                env.arena.eq(a, b)
            }
            ATerm::Not(x) => {
                let x = gsubst_term(x, env);
                env.arena.not(x)
            }
            ATerm::Ite(c, x, y) => {
                let c = gsubst_term(c, env);
                let x = gsubst_term(x, env);
                let y = gsubst_term(y, env);
                env.arena.ite(c, x, y)
            }
            ATerm::Distinct(ts) => {
                let recs = gsubst_all_of(ts, env);
                env.arena.distinct(recs)
            }
            ATerm::And(ts) => {
                let recs = gsubst_all_of(ts, env);
                env.arena.and(recs)
            }
            ATerm::Or(ts) => {
                let recs = gsubst_all_of(ts, env);
                env.arena.or(recs)
            }
            ATerm::Xor(ts) => {
                let recs = gsubst_all_of(ts, env);
                env.arena.xor(recs)
            }
            ATerm::Implies(ps, c) => {
                let recs = gsubst_all_of(ps, env);
                let c = gsubst_term(c, env);
                env.arena.implies(recs, c)
            }
            ATerm::Let(vs, body) => {
                let count: usize = vs.len();
                let mut bindings: Vec<VarBinding<Str, Term>> = Vec::with_capacity(count);
                let mut i = 0usize;
                while i < count {
                    let bs: &[VarBinding<Str, Term>] = vs;
                    let (name, id) = (bs[i].0.clone(), bs[i].1);
                    let bound = gsubst_term(&bs[i].2, env);
                    bindings.push(VarBinding(name, id, bound));
                    i += 1;
                }
                let body = gsubst_term(body, env);
                env.arena.let_term(bindings, body)
            }
            ATerm::Exists(vs, body) => {
                let vs: Vec<VarBinding<Str, Sort>> = vs.clone();
                let body = gsubst_term(body, env);
                env.arena.exists(vs, body)
            }
            ATerm::Forall(vs, body) => {
                let vs: Vec<VarBinding<Str, Sort>> = vs.clone();
                let body = gsubst_term(body, env);
                env.arena.forall(vs, body)
            }
            ATerm::Matching(scrutinee, arms) => {
                let count: usize = arms.len();
                let scrutinee = gsubst_term(scrutinee, env);
                let mut cases: Vec<PatternArm> = Vec::with_capacity(count);
                let mut i = 0usize;
                while i < count {
                    let cs: &[PatternArm] = arms;
                    let pattern = cs[i].pattern.clone();
                    let body = gsubst_term(&cs[i].body, env);
                    cases.push(PatternArm { pattern, body });
                    i += 1;
                }
                env.arena.matching(scrutinee, cases)
            }
            ATerm::Annotated(inner, anns) => {
                let count: usize = anns.len();
                let inner = gsubst_term(inner, env);
                let mut attrs: Vec<Attribute> = Vec::with_capacity(count);
                let mut i = 0usize;
                while i < count {
                    let ats: &[Attribute] = anns;
                    // only the trigger forms hold terms; the rest carry nothing to expand
                    match &ats[i] {
                        Attribute::Pattern(ts) => {
                            let recs = gsubst_all_of(ts, env);
                            attrs.push(Attribute::Pattern(recs));
                        }
                        #[cfg(feature = "no-pattern")]
                        Attribute::NoPattern(x) => {
                            let rec = gsubst_term(x, env);
                            attrs.push(Attribute::NoPattern(rec));
                        }
                        leaf => attrs.push(leaf.clone()),
                    }
                    i += 1;
                }
                env.arena.annotated(inner, attrs)
            }
        };
        env.memoize(t.clone(), out.clone());
        out
    }

    /// Expand the global definitions in each of `ts`.
    pub fn gsubst_all_of<'a>(ts: &[Term], env: &mut GlobalSubstituter<'a>) -> Vec<Term> {
        let count: usize = ts.len();
        let mut recs: Vec<Term> = Vec::with_capacity(count);
        let mut i = 0usize;
        while i < count {
            let xs: &[Term] = ts;
            recs.push(gsubst_term(&xs[i], env));
            i += 1;
        }
        recs
    }

    /// Put the expansion of `sym`'s definition in the cache, if it has one.
    ///
    /// Returns whether it does. The body is expanded under a scope that blocks the definition's
    /// recursive dependencies, which is what stops a recursive definition from unfolding forever.
    pub fn expand_def<'a>(sym: Str, env: &mut GlobalSubstituter<'a>) -> bool {
        if env.global_def_cache.contains_key(&sym) {
            return true;
        }
        let found = env.arena.get_definition(&sym).cloned();
        if found.is_none() {
            return false;
        }
        // a plain `let` that says its type, so the body can be lent while the rest of it is kept
        let def: FunctionMetaDefined = found.expect("just checked");
        let name = def.def.name.clone();
        let pushed = env.start_unfolding(def.rec_deps.clone());
        let expanded = gsubst_term(&def.def.body, env);
        env.finish_unfolding(pushed);
        env.global_def_cache.insert(
            name,
            FunctionDef {
                body: expanded,
                ..def.def
            },
        );
        true
    }
}

/// Inline a nullary definition, i.e. what `sym` stands for at the given sort.
///
/// A parametric definition is monomorphized first, which is why the use site's sort is needed.
fn expand_global(sym: &Str, sort: Sort, env: &mut GlobalSubstituter<'_>) -> Term {
    let def = env
        .global_def_cache
        .get(sym)
        .expect("just expanded")
        .clone();
    if def.sort_params.is_empty() {
        def.body
    } else {
        // instantiate the signature's sort against the use site's, and propagate that through
        let mut subst = empty_subst(&def.sort_params);
        instantiate_subst(&mut subst, [(&def.out_sort, &sort)]).unwrap();
        def.body.monomorphize(&subst, env)
    }
}

/// Inline an application of a definition to `recs`, i.e. substitute them for its variables.
fn expand_app(sym: &Str, recs: Vec<Term>, sort: Sort, env: &mut GlobalSubstituter<'_>) -> Term {
    let def = env
        .global_def_cache
        .get(sym)
        .expect("just expanded")
        .clone();
    let sorts: Vec<Sort> = recs.iter().map(|t| t.get_sort(env)).collect();
    let subst = Substitution::new(def.vars.iter().map(|v| v.clone().into()).zip(recs));
    if def.sort_params.is_empty() {
        def.body.subst(&subst, env)
    } else {
        // the sorts of the arguments and of the result together pin the sort parameters
        let mut sort_subst = empty_subst(&def.sort_params);
        let sort_params: Vec<Sort> = def
            .sort_params
            .iter()
            .map(|s| env.sort0(s.clone()))
            .collect();
        instantiate_subst(
            &mut sort_subst,
            sort_params
                .iter()
                .zip(sorts.iter())
                .chain([(&def.out_sort, &sort)]),
        )
        .unwrap();
        def.body.monomorphize(&sort_subst, env).subst(&subst, env)
    }
}

#[cfg(test)]
mod stack_safety {
    use crate::allocator::TermAllocator;
    use crate::ast::{ACommand, ATerm, Context, GlobalSubst, Repr, Term, Typecheck};
    use crate::traits::Contains;
    use crate::untyped::UntypedAst;

    /// Depth the expansion is expected to survive, and a stack far too small to hold that many
    /// native frames: the descent is only flat if it never grows one per level.
    const DEEP: usize = 20_000;
    const SMALL_STACK: usize = 256 * 1024;

    /// A script whose `n`th definition is written in terms of the one before it.
    ///
    /// Expanding `f{n}` expands the whole chain, which is what used to cost a native frame per link:
    /// a driver was started for each definition body, so a chain of 5 000 overflowed 8 MB.
    fn chain(n: usize) -> String {
        let mut s =
            String::from("(set-logic ALL)\n(declare-const x Int)\n(define-fun f0 () Int x)\n");
        for i in 1..=n {
            s.push_str(&format!("(define-fun f{i} () Int (+ f{} 1))\n", i - 1));
        }
        s.push_str(&format!("(assert (= f{n} 0))\n"));
        s
    }

    /// Run `f` where a per-level native frame cannot fit.
    fn on_small_stack<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
        std::thread::Builder::new()
            .stack_size(SMALL_STACK)
            .spawn(f)
            .expect("spawn")
            .join()
            .expect("the expansion overflowed the stack")
    }

    /// How deep a chain of applications of `head` a term is, walked iteratively: on this branch
    /// printing one recurses, so the shape is read rather than rendered.
    fn nesting(t: &Term, head: &str) -> usize {
        let mut depth = 0usize;
        let mut cur = t.clone();
        loop {
            let next = match cur.repr() {
                ATerm::App(f, args, _) if f.id_str().inner() == head && !args.is_empty() => {
                    args[0].clone()
                }
                ATerm::Not(inner) if head == "not" => inner.clone(),
                _ => return depth,
            };
            depth += 1;
            cur = next;
        }
    }

    /// Parse and type-check `script`, and hand back its one assertion with the context it needs.
    fn assertion(script: &str) -> (Context, Term) {
        let mut context = Context::new();
        let typed = UntypedAst
            .parse_script_str(script)
            .expect("parse")
            .type_check(&mut context)
            .expect("typecheck");
        let term = typed
            .iter()
            .find_map(|c| match c.repr() {
                ACommand::Assert(t) => Some(t.clone()),
                _ => None,
            })
            .expect("the assertion");
        std::mem::forget(typed);
        (context, term)
    }

    /// A chain of definitions expands on a stack that could not hold a frame per link.
    #[test]
    fn a_deep_definition_chain_is_flat() {
        let (context, term) = assertion(&chain(DEEP));
        let depth = on_small_stack(move || {
            let mut context = context;
            let expanded = term.gsubst_all(&mut context);
            // `(= (+ (+ … x 1) 1) 0)`, i.e. every definition inlined
            let inlined = match expanded.repr() {
                ATerm::Eq(lhs, _) => lhs.clone(),
                _ => panic!("an equation"),
            };
            let depth = nesting(&inlined, "+");
            std::mem::forget((expanded, inlined, term, context));
            depth
        });
        assert_eq!(depth, DEEP);
    }

    /// A deep *term* is flat too, which is the other direction the descent recurses in.
    #[test]
    fn a_deep_term_is_flat() {
        let (mut context, _) =
            assertion("(set-logic ALL)(declare-const p Bool)(define-fun q () Bool p)(assert q)");
        let q = UntypedAst
            .parse_term_str("q")
            .expect("parse")
            .type_check(&mut context)
            .expect("typecheck");
        let depth = on_small_stack(move || {
            let mut context = context;
            let mut t = q.clone();
            for _ in 0..DEEP {
                t = context.not(t);
            }
            let expanded = t.gsubst_all(&mut context);
            let depth = nesting(&expanded, "not");
            std::mem::forget((expanded, t, q, context));
            depth
        });
        assert_eq!(depth, DEEP);
    }
}
