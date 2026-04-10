// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! This module handles expansions of global definitions.
//!
//! A global substitution operation expands global definitions, invoking [`Substitute::subst`]
//! whenever necessary. The [`GlobalSubst`] trait provides the main entry point via
//! `.gsubst(names, context)`, which expands the specified global definitions on the fly.

use crate::allocator::{SortAllocator, TermAllocator};
use crate::ast::alg::{PatternArm, VarBinding};
use crate::ast::subst::{Substitute, Substitution};
use crate::ast::{
    ATerm, Arena, Attribute, Context, FetchSort, FunctionDef, HasArena, Monomorphization, Sort,
    Str, Term,
};
use crate::raw::tc::unif::{empty_subst, instantiate_subst};
use crate::traits::{AllocatableString, Repr};
use std::collections::{HashMap, HashSet};

/// Expand global names with their definitions in `Self`.
///
/// This trait implements substitutions by expanding the bodies of names during substitutions.
pub trait GlobalSubst<E> {
    fn gsubst<S>(&self, global_names: impl IntoIterator<Item = S>, env: &mut E) -> Self
    where
        S: AllocatableString<Arena>;

    fn gsubst_with_names(&self, global_names: &HashSet<Str>, env: &mut E) -> Self;
}

impl<T, E> GlobalSubst<E> for T
where
    T: GlobalSubstImpl<E>,
    E: HasArena,
{
    fn gsubst<S>(&self, global_names: impl IntoIterator<Item = S>, env: &mut E) -> Self
    where
        S: AllocatableString<Arena>,
    {
        {
            let global_names = global_names
                .into_iter()
                .map(|s| s.allocate(env.arena()))
                .collect::<HashSet<_>>();
            self.gsubst_with_names(&global_names, env)
        }
    }

    fn gsubst_with_names(&self, global_names: &HashSet<Str>, env: &mut E) -> Self {
        let mut cache = HashMap::new();
        self.gsubst_impl(global_names, &HashSet::new(), env, &mut cache)
    }
}

trait GlobalSubstImpl<E> {
    fn gsubst_impl(
        &self,
        global_names: &HashSet<Str>,
        block: &HashSet<Str>,
        env: &mut E,
        cache: &mut HashMap<Str, FunctionDef>,
    ) -> Self;
}

impl<T, E> GlobalSubstImpl<E> for Vec<T>
where
    T: GlobalSubstImpl<E>,
{
    fn gsubst_impl(
        &self,
        global_names: &HashSet<Str>,
        block: &HashSet<Str>,
        env: &mut E,
        cache: &mut HashMap<Str, FunctionDef>,
    ) -> Self {
        self.iter()
            .map(|v| v.gsubst_impl(global_names, block, env, cache))
            .collect()
    }
}

impl GlobalSubstImpl<Context> for Attribute {
    fn gsubst_impl(
        &self,
        global_names: &HashSet<Str>,
        block: &HashSet<Str>,
        env: &mut Context,
        cache: &mut HashMap<Str, FunctionDef>,
    ) -> Self {
        if let Attribute::Pattern(ts) = self {
            Attribute::Pattern(ts.gsubst_impl(global_names, block, env, cache))
        } else {
            self.clone()
        }
    }
}

fn populate_cache(
    sym: &Str,
    global_names: &HashSet<Str>,
    env: &mut Context,
    cache: &mut HashMap<Str, FunctionDef>,
) -> bool {
    if !cache.contains_key(sym) {
        if let Some(def) = env.get_definition(sym).cloned() {
            let ret = def
                .def
                .body
                .gsubst_impl(global_names, &def.rec_deps, env, cache);
            // the only possible case is a parametric function

            cache.insert(
                def.def.name.clone(),
                FunctionDef {
                    body: ret.clone(),
                    ..def.def
                },
            );
            true
        } else {
            false
        }
    } else {
        true
    }
}

impl GlobalSubstImpl<Context> for Term {
    fn gsubst_impl(
        &self,
        global_names: &HashSet<Str>,
        block: &HashSet<Str>,
        env: &mut Context,
        cache: &mut HashMap<Str, FunctionDef>,
    ) -> Self {
        match self.repr() {
            ATerm::Constant(_, _) | ATerm::Local(_) => self.clone(),
            ATerm::Global(qid, sort) => {
                let sort = sort.as_ref().expect("type invariant violation!").clone();
                let sym = qid.id_str();
                if global_names.contains(sym) && !block.contains(sym) {
                    if !populate_cache(sym, global_names, env, cache) {
                        return self.clone();
                    }
                    // The cache was just populated
                    let def = cache.get(sym).unwrap();
                    if def.sort_params.is_empty() {
                        def.body.clone()
                    } else {
                        // We instantiate a substitution with the sort in the signature
                        // with the overall sort, and use that to propagate the sort information to
                        // obtain the final overall term
                        let mut subst = empty_subst(&def.sort_params);
                        instantiate_subst(&mut subst, [(&def.out_sort, &sort)]).unwrap();
                        def.body.monomorphize(&subst, env)
                    }
                } else {
                    self.clone()
                }
            }
            ATerm::App(f, args, sort) => {
                let sort = sort.as_ref().expect("type invariant violation!").clone();
                let nargs: Vec<Term> = args
                    .iter()
                    .map(|a| a.gsubst_impl(global_names, block, env, cache))
                    .collect();
                let sym = f.id_str();
                if global_names.contains(sym) && !block.contains(sym) {
                    if !populate_cache(sym, global_names, env, cache) {
                        return self.clone();
                    }
                    // The cache was just populated
                    let def = cache.get(sym).unwrap();
                    let sorts: Vec<Sort> = nargs.iter().map(|t| t.get_sort(env)).collect();
                    let subst =
                        Substitution::new_str(def.vars.iter().map(|v| v.0.clone()).zip(nargs));
                    if def.sort_params.is_empty() {
                        def.body.subst(&subst, env)
                    } else {
                        // We instantiate a substitution with the sort in the signature
                        // with the overall sort, and use that to propagate the sort information to
                        // obtain the final overall term
                        let mut sort_subst = empty_subst(&def.sort_params);
                        let sort_params: Vec<_> = def
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
                } else {
                    env.arena.app(f.clone(), nargs, Some(sort.clone()))
                }
            }
            ATerm::Let(bindings, body) => {
                let nbindings = bindings
                    .iter()
                    .map(|b| {
                        VarBinding(
                            b.0.clone(),
                            b.1,
                            b.2.gsubst_impl(global_names, block, env, cache),
                        )
                    })
                    .collect();
                let nbody = body.gsubst_impl(global_names, block, env, cache);
                env.let_term(nbindings, nbody)
            }
            ATerm::Exists(vs, body) => {
                let nbody = body.gsubst_impl(global_names, block, env, cache);
                env.exists(vs.clone(), nbody)
            }
            ATerm::Forall(vs, body) => {
                let nbody = body.gsubst_impl(global_names, block, env, cache);
                env.forall(vs.clone(), nbody)
            }
            ATerm::Matching(t, cases) => {
                let nt = t.gsubst_impl(global_names, block, env, cache);
                let ncases = cases
                    .iter()
                    .map(|c| PatternArm {
                        pattern: c.pattern.clone(),
                        body: c.body.gsubst_impl(global_names, block, env, cache),
                    })
                    .collect();
                env.matching(nt, ncases)
            }
            ATerm::Annotated(t, annos) => {
                let nt = t.gsubst_impl(global_names, block, env, cache);
                let nannos = annos.gsubst_impl(global_names, block, env, cache);
                env.annotated(nt, nannos)
            }
            ATerm::Eq(a, b) => {
                let na = a.gsubst_impl(global_names, block, env, cache);
                let nb = b.gsubst_impl(global_names, block, env, cache);
                env.eq(na, nb)
            }
            ATerm::Distinct(ts) => {
                let nts = ts.gsubst_impl(global_names, block, env, cache);
                env.distinct(nts)
            }
            ATerm::And(ts) => {
                let nts = ts.gsubst_impl(global_names, block, env, cache);
                env.and(nts)
            }
            ATerm::Or(ts) => {
                let nts = ts.gsubst_impl(global_names, block, env, cache);
                env.or(nts)
            }
            ATerm::Xor(ts) => {
                let nts = ts.gsubst_impl(global_names, block, env, cache);
                env.xor(nts)
            }
            ATerm::Implies(ts, concl) => {
                let nts = ts.gsubst_impl(global_names, block, env, cache);
                let nconcl = concl.gsubst_impl(global_names, block, env, cache);
                env.implies(nts, nconcl)
            }
            ATerm::Not(t) => {
                let nt = t.gsubst_impl(global_names, block, env, cache);
                env.not(nt)
            }
            ATerm::Ite(c, t, e) => {
                let nc = c.gsubst_impl(global_names, block, env, cache);
                let nt = t.gsubst_impl(global_names, block, env, cache);
                let ne = e.gsubst_impl(global_names, block, env, cache);
                env.ite(nc, nt, ne)
            }
        }
    }
}

use crate::ast::{TermRecursor, TypedTermRecursor};
use crate::raw::alg::rec::Bottom;
use crate::raw::alg::{Constant, Local, QualifiedIdentifier};
use crate::raw::instance;
use yaspar::ast::Keyword;

/// Stack-safe global definition expansion using [`TermRecursor`].
///
/// Expands global definitions (from `define-fun`, `define-const`, etc.) by inlining their
/// bodies. For parametric definitions, applies monomorphization. Uses a cache to avoid
/// re-expanding the same definition multiple times.
pub struct GlobalSubstituter<'a> {
    ctx: &'a mut Context,
    global_names: &'a HashSet<Str>,
    cache: HashMap<Str, FunctionDef>,
}

impl<'a> GlobalSubstituter<'a> {
    pub fn new(ctx: &'a mut Context, global_names: &'a HashSet<Str>) -> Self {
        Self {
            ctx,
            global_names,
            cache: HashMap::new(),
        }
    }

    /// Populate the cache for a symbol if not already present. Returns true if the definition
    /// exists and was cached (or was already cached).
    fn populate_cache(&mut self, sym: &Str) -> bool {
        populate_cache(sym, self.global_names, self.ctx, &mut self.cache)
    }

    fn arena(&mut self) -> &mut Arena {
        &mut self.ctx.arena
    }
}

impl TermRecursor<Str, Sort, Term> for GlobalSubstituter<'_> {
    type Out = Term;
    type Attr = instance::Attribute;
    type Binding = Term;
    type Pattern = ();
    type Arm = instance::PatternArm;
    type Err = Bottom;

    fn on_constant(
        &mut self,
        current: &Term,
        _: &Constant<Str>,
        _: &Option<Sort>,
    ) -> Result<Term, Bottom> {
        Ok(current.clone())
    }

    /// Expand a global symbol if it's in the expansion set and has a nullary definition.
    fn on_global(
        &mut self,
        current: &Term,
        qid: &QualifiedIdentifier<Str, Sort>,
        sort: &Option<Sort>,
    ) -> Result<Term, Bottom> {
        let sort = sort.as_ref().expect("type invariant violation!").clone();
        let sym = qid.id_str();
        if self.global_names.contains(sym) {
            if !self.populate_cache(sym) {
                return Ok(current.clone());
            }
            let def = self.cache.get(sym).unwrap();
            if def.sort_params.is_empty() {
                Ok(def.body.clone())
            } else {
                let mut subst = empty_subst(&def.sort_params);
                instantiate_subst(&mut subst, [(&def.out_sort, &sort)]).unwrap();
                Ok(def.body.monomorphize(&subst, self.ctx))
            }
        } else {
            Ok(current.clone())
        }
    }

    fn on_local(&mut self, current: &Term, _: &Local<Str, Sort>) -> Result<Term, Bottom> {
        Ok(current.clone())
    }

    /// Expand a function application if the head symbol is in the expansion set.
    fn on_app(
        &mut self,
        _current: &Term,
        f: &QualifiedIdentifier<Str, Sort>,
        _: &[Term],
        sort: &Option<Sort>,
        recs: Vec<Term>,
    ) -> Result<Term, Bottom> {
        let sort = sort.as_ref().expect("type invariant violation!").clone();
        let sym = f.id_str();
        if self.global_names.contains(sym) {
            if !self.populate_cache(sym) {
                return Ok(self.arena().app(f.clone(), recs, Some(sort)));
            }
            let def = self.cache.get(sym).unwrap();
            let sorts: Vec<Sort> = recs.iter().map(|t| t.get_sort(self.ctx)).collect();
            let subst = Substitution::new_str(def.vars.iter().map(|v| v.0.clone()).zip(recs));
            if def.sort_params.is_empty() {
                Ok(def.body.subst(&subst, self.ctx))
            } else {
                let mut sort_subst = empty_subst(&def.sort_params);
                let sort_params: Vec<_> = def
                    .sort_params
                    .iter()
                    .map(|s| self.ctx.sort0(s.clone()))
                    .collect();
                instantiate_subst(
                    &mut sort_subst,
                    sort_params
                        .iter()
                        .zip(sorts.iter())
                        .chain([(&def.out_sort, &sort)]),
                )
                .unwrap();
                Ok(def
                    .body
                    .monomorphize(&sort_subst, self.ctx)
                    .subst(&subst, self.ctx))
            }
        } else {
            Ok(self.arena().app(f.clone(), recs, Some(sort)))
        }
    }

    fn on_eq(&mut self, _: &Term, _: &Term, _: &Term, a: Term, b: Term) -> Result<Term, Bottom> {
        Ok(self.arena().eq(a, b))
    }

    fn on_distinct(&mut self, _: &Term, _: &[Term], recs: Vec<Term>) -> Result<Term, Bottom> {
        Ok(self.arena().distinct(recs))
    }

    fn on_and(&mut self, _: &Term, _: &[Term], recs: Vec<Term>) -> Result<Term, Bottom> {
        Ok(self.arena().and(recs))
    }

    fn on_or(&mut self, _: &Term, _: &[Term], recs: Vec<Term>) -> Result<Term, Bottom> {
        Ok(self.arena().or(recs))
    }

    fn on_xor(&mut self, _: &Term, _: &[Term], recs: Vec<Term>) -> Result<Term, Bottom> {
        Ok(self.arena().xor(recs))
    }

    fn on_not(&mut self, _: &Term, _: &Term, r: Term) -> Result<Term, Bottom> {
        Ok(self.arena().not(r))
    }

    fn on_implies(
        &mut self,
        _: &Term,
        _: &[Term],
        _: &Term,
        ps: Vec<Term>,
        c: Term,
    ) -> Result<Term, Bottom> {
        Ok(self.arena().implies(ps, c))
    }

    fn on_ite(
        &mut self,
        _: &Term,
        _: &Term,
        _: &Term,
        _: &Term,
        b: Term,
        t: Term,
        e: Term,
    ) -> Result<Term, Bottom> {
        Ok(self.arena().ite(b, t, e))
    }

    // --- Let ---

    fn on_let_binding(
        &mut self,
        _: &Term,
        _: &[VarBinding<Str, Term>],
        _: &Term,
        _: usize,
        rec: Term,
    ) -> Result<Term, Bottom> {
        Ok(rec)
    }

    fn setup_let_scope(
        &mut self,
        _: &Term,
        _: &[VarBinding<Str, Term>],
        _: &Term,
        _: &[Term],
    ) -> Result<(), Bottom> {
        Ok(())
    }

    fn on_let(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Term>],
        _: &Term,
        vs_rec: Vec<Term>,
        body: Term,
    ) -> Result<Term, Bottom> {
        let nbindings = vs
            .iter()
            .zip(vs_rec)
            .map(|(v, r)| VarBinding(v.0.clone(), v.1, r))
            .collect();
        Ok(self.arena().let_term(nbindings, body))
    }

    // --- Quantifiers ---

    fn setup_quantifier_scope(
        &mut self,
        _: &Term,
        _: &[VarBinding<Str, Sort>],
        _: &Term,
        _: bool,
    ) -> Result<(), Bottom> {
        Ok(())
    }

    fn on_forall(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Sort>],
        _: &Term,
        body: Term,
    ) -> Result<Term, Bottom> {
        Ok(self.arena().forall(vs.to_vec(), body))
    }

    fn on_exists(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Sort>],
        _: &Term,
        body: Term,
    ) -> Result<Term, Bottom> {
        Ok(self.arena().exists(vs.to_vec(), body))
    }

    // --- Match ---

    fn setup_match_case_scope(
        &mut self,
        _: &Term,
        _: &Term,
        _: &[instance::PatternArm],
        _: &Term,
        _: usize,
    ) -> Result<(), Bottom> {
        Ok(())
    }

    fn on_match_arm(
        &mut self,
        _: &Term,
        _: &Term,
        cases: &[instance::PatternArm],
        idx: usize,
        _: (),
        body: Term,
    ) -> Result<instance::PatternArm, Bottom> {
        Ok(instance::PatternArm {
            pattern: cases[idx].pattern.clone(),
            body,
        })
    }

    fn on_match(
        &mut self,
        _: &Term,
        _: &Term,
        _: &[instance::PatternArm],
        scrutinee: Term,
        arms: Vec<instance::PatternArm>,
    ) -> Result<Term, Bottom> {
        Ok(self.arena().matching(scrutinee, arms))
    }

    // --- Annotated ---

    fn on_annotated(
        &mut self,
        _: &Term,
        _: &Term,
        _: &[instance::Attribute],
        r: Term,
        anns: Vec<instance::Attribute>,
    ) -> Result<Term, Bottom> {
        Ok(self.arena().annotated(r, anns))
    }

    fn on_attribute_keyword(&mut self, kw: &Keyword) -> Result<instance::Attribute, Bottom> {
        Ok(instance::Attribute::Keyword(kw.clone()))
    }

    fn on_attribute_constant(
        &mut self,
        kw: &Keyword,
        c: &Constant<Str>,
    ) -> Result<instance::Attribute, Bottom> {
        Ok(instance::Attribute::Constant(kw.clone(), c.clone()))
    }

    fn on_attribute_symbol(
        &mut self,
        kw: &Keyword,
        s: &Str,
    ) -> Result<instance::Attribute, Bottom> {
        Ok(instance::Attribute::Symbol(kw.clone(), s.clone()))
    }

    fn on_attribute_named(&mut self, name: &Str) -> Result<instance::Attribute, Bottom> {
        Ok(instance::Attribute::Named(name.clone()))
    }

    fn on_attribute_pattern(
        &mut self,
        _: &[Term],
        recs: Vec<Term>,
    ) -> Result<instance::Attribute, Bottom> {
        Ok(instance::Attribute::Pattern(recs))
    }
}

impl TypedTermRecursor for GlobalSubstituter<'_> {}
