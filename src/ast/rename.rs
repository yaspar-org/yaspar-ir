// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Alpha renaming: making every bound name in a term distinct.
//!
//! A term built programmatically (or assembled from several sources) may bind the same *name*
//! more than once in nested scopes, e.g. `(forall ((x Int)) (exists ((x Int)) (p x)))`. Such a
//! term is well-formed — local variables are distinguished by their id, not their name — but it
//! prints ambiguously, and printing it out then re-parsing it does not round-trip to the same
//! term, because the inner `x` shadows the outer one.
//!
//! [`AlphaRename::alpha_rename`] gives *every* binder a freshly minted name, whether or not its
//! own name collided. So `(forall ((x Int)) (exists ((x Int)) (p x)))` becomes
//! `(forall ((x-0 Int)) (exists ((x-1 Int)) (p x-1)))`, and `(forall ((x Int)) (p x))` becomes
//! `(forall ((x-0 Int)) (p x-0))` even though it had nothing to resolve. Names come from the
//! arena's fresh-variable supply, so they cannot collide with anything the arena has seen —
//! including globals and free variables — at the cost of relabelling binders that were already
//! unambiguous.
//!
//! Ids are left untouched: only the [`Str`] labels change, so the result is alpha equivalent to
//! the input by construction.
//!
//! A new name keeps the original as its prefix, so `x` becomes `x-0`. Any `-N` trailer is stripped
//! first, so `x-0` becomes `x-1` rather than `x-0-1`.
//!
//! Renaming is therefore not idempotent: a second pass mints another round of names. The result is
//! still alpha equivalent and still clash free, it is just not the same term.
//!
//! Free local variables are left alone: they are bound by some enclosing structure that this
//! traversal cannot see, so renaming them would change what the term means.

use crate::allocator::TermAllocator;
use crate::ast::alg::VarBinding;
use crate::ast::{
    Attribute, Bottom, Constant, FreshVar, HasArena, Local, Pattern, PatternArm,
    QualifiedIdentifier, Sort, Str, Term, TermRecursor, TypedBuilder, TypedTermRecursor,
};
use crate::containers::Mapping;
use crate::raw::alg::rec_memo::{MemoizedRecursion, Memoizing};
use delegate::delegate;
use std::collections::{HashMap, HashSet};
use yaspar::ast::Keyword;

/// Rename bound variables in `Self` so that no two binders share a name.
///
/// Precondition: every local must occur inside its binder's scope.
/// Parsed and type-checked terms always satisfy this; a term can violate it if this term is built
/// through unchecked APIs, or a sub-term built inside a builder context is kept after that context is finalized.
pub trait AlphaRename<E> {
    fn alpha_rename(&self, env: &mut E) -> Self;
}

impl<E> AlphaRename<E> for Term
where
    E: HasArena,
{
    fn alpha_rename(&self, env: &mut E) -> Self {
        MemoizedRecursion(&mut RenameEnv::new(env)).recurse_on_term_no_err(self)
    }
}

/// Stack-safe alpha renaming using [`TermRecursor`], memoized on sub-terms.
struct RenameEnv<'a, E> {
    env: TypedBuilder<'a, E>,
    /// Scope stack mapping the id of a bound variable to the name it should carry.
    ///
    /// Each frame corresponds to one `let`, quantifier, or match arm. A lookup that misses means
    /// the variable is free, and so is left unrenamed.
    name_map: Vec<HashMap<usize, Str>>,
    /// Every name bound so far anywhere in the traversal.
    ///
    /// Names are never removed when a scope ends, since a later sibling scope reusing a name would
    /// still print ambiguously against the earlier one.
    seen: HashSet<Str>,
    /// Sub-term results already computed, so a shared sub-term is renamed once.
    cache: HashMap<Term, Term>,
}

fn find_prefix(sym: &str) -> &str {
    let mut cutoff = sym.len();
    for (i, c) in sym.char_indices().rev() {
        if c.is_ascii_digit() {
            cutoff = i;
        } else if c == '-' {
            cutoff = i;
            break;
        } else {
            break;
        }
    }
    &sym[..cutoff]
}

impl<'a, E> RenameEnv<'a, E>
where
    E: HasArena,
{
    fn new(env: &'a mut E) -> Self {
        Self {
            env: TypedBuilder::new(env),
            name_map: Vec::new(),
            seen: HashSet::new(),
            cache: HashMap::new(),
        }
    }

    /// Mint a fresh name for `name`, keeping it as the prefix.
    fn fresh_name(&mut self, name: &Str) -> Str {
        let prefix = find_prefix(name);
        self.env.fresh_var(prefix)
    }

    /// Decide the name a newly bound variable should carry, and record it as seen.
    ///
    /// A fresh name is always minted, so no binder keeps the name it came in with.
    fn bind_name(&mut self, name: &Str) -> Str {
        let chosen = self.fresh_name(name);
        self.seen.insert(chosen.clone());
        chosen
    }

    /// Look up the name chosen for the variable `id`, innermost scope first.
    fn lookup(&self, id: usize) -> Option<Str> {
        self.name_map.lookup(&id)
    }

    /// Choose names for each of `ids` and push them as a new scope.
    fn push_scope(&mut self, ids: impl IntoIterator<Item = (usize, Str)>) {
        let frame = ids
            .into_iter()
            .map(|(id, name)| {
                let chosen = self.bind_name(&name);
                (id, chosen)
            })
            .collect();
        self.name_map.push(frame);
    }

    /// Re-label the variables a match pattern binds, returning the updated pattern.
    ///
    /// The pattern's own scope must already be on the stack, since the names come from it.
    fn rename_pattern(&self, pattern: &Pattern) -> Pattern {
        // a bound pattern variable is always in the scope just pushed, so `lookup` cannot miss;
        // fall back to the original name rather than panicking if it somehow does
        let rename =
            |(name, id): &(Str, usize)| (self.lookup(*id).unwrap_or_else(|| name.clone()), *id);
        match pattern {
            Pattern::Wildcard(None) => Pattern::Wildcard(None),
            Pattern::Wildcard(Some(v)) => Pattern::Wildcard(Some(rename(v))),
            Pattern::Ctor(ctor) => Pattern::Ctor(ctor.clone()),
            Pattern::Applied { ctor, arguments } => Pattern::Applied {
                ctor: ctor.clone(),
                arguments: arguments.iter().map(|a| a.as_ref().map(rename)).collect(),
            },
        }
    }

    /// Pop a quantifier scope and re-label its bindings with the names chosen for them.
    fn pop_quantifier_bindings(
        &mut self,
        vs: &[VarBinding<Str, Sort>],
    ) -> Vec<VarBinding<Str, Sort>> {
        let frame = self
            .name_map
            .pop()
            .expect("fatal management: scope unbalanced; quantifier scope must have been pushed");
        vs.iter()
            .map(|VarBinding(name, id, sort)| {
                VarBinding(
                    frame.get(id).cloned().unwrap_or(name.clone()),
                    *id,
                    sort.clone(),
                )
            })
            .collect()
    }
}

impl<E> TermRecursor<Str, Sort, Term> for RenameEnv<'_, E>
where
    E: HasArena,
{
    type Out = Term;
    type Attr = Attribute;
    type Binding = VarBinding<Str, Term>;
    type Pattern = Pattern;
    type Arm = PatternArm;
    type Err = Bottom;

    // Renaming only touches binders and the variables that refer to them, so every other
    // callback is the plain identity rebuild.
    delegate! {
        to self.env {
            fn on_constant(&mut self, current: &Term, constant: &Constant, sort: &Option<Sort>) -> Result<Term, Bottom>;
            fn on_global(&mut self, current: &Term, id: &QualifiedIdentifier, sort: &Option<Sort>) -> Result<Term, Bottom>;
            fn on_app(&mut self, current: &Term, id: &QualifiedIdentifier, ts: &[Term], s: &Option<Sort>, recs: Vec<Term>) -> Result<Term, Bottom>;
            fn on_match(&mut self, current: &Term, scrutinee: &Term, cases: &[PatternArm], scrutinee_rec: Self::Out, cases_rec: Vec<Self::Arm>) -> Result<Term, Bottom>;
            fn on_annotated(&mut self, current: &Term, t: &Term, anns: &[Attribute], t_rec: Term, anns_rec: Vec<Attribute>) -> Result<Term, Bottom>;
            fn on_attribute_keyword(&mut self, keyword: &Keyword) -> Result<Attribute, Bottom>;
            fn on_attribute_constant(&mut self, keyword: &Keyword, constant: &Constant) -> Result<Attribute, Bottom>;
            fn on_attribute_symbol(&mut self, keyword: &Keyword, symbol: &Str) -> Result<Attribute, Bottom>;
            fn on_attribute_named(&mut self, name: &Str) -> Result<Attribute, Bottom>;
            fn on_attribute_pattern(&mut self, patterns: &[Term], patterns_rec: Vec<Term>) -> Result<Attribute, Bottom>;
            #[cfg(feature = "no-pattern")]
            fn on_attribute_no_pattern(&mut self, pattern: &Term, pattern_rec: Term) -> Result<Attribute, Bottom>;
            fn on_eq(&mut self, current: &Term, a: &Term, b: &Term, a_rec: Term, b_rec: Term) -> Result<Term, Bottom>;
            fn on_distinct(&mut self, current: &Term, ts: &[Term], ts_rec: Vec<Term>) -> Result<Term, Bottom>;
            fn on_and(&mut self, current: &Term, ts: &[Term], ts_rec: Vec<Term>) -> Result<Term, Bottom>;
            fn on_or(&mut self, current: &Term, ts: &[Term], ts_rec: Vec<Term>) -> Result<Term, Bottom>;
            fn on_xor(&mut self, current: &Term, ts: &[Term], ts_rec: Vec<Term>) -> Result<Term, Bottom>;
            fn on_not(&mut self, current: &Term, t: &Term, t_rec: Term) -> Result<Term, Bottom>;
            fn on_implies(&mut self, current: &Term, ts: &[Term], t: &Term, ts_rec: Vec<Term>, t_rec: Term) -> Result<Term, Bottom>;
            fn on_ite(&mut self, current: &Term, b: &Term, t: &Term, e: &Term, b_rec: Term, t_rec: Term, e_rec: Term) -> Result<Term, Bottom>;
        }
    }

    /// Re-label a variable with the name chosen by its binder, keeping its id.
    ///
    /// A variable with no binder in scope is free, and so is left as it is.
    fn on_local(&mut self, current: &Term, id: &Local) -> Result<Term, Bottom> {
        match self.lookup(id.id) {
            // the name already matches, so there is nothing to rebuild
            Some(symbol) if symbol == id.symbol => Ok(current.clone()),
            Some(symbol) => {
                let local = Local {
                    id: id.id,
                    symbol,
                    sort: id.sort.clone(),
                };
                Ok(self.env.local(local))
            }
            None => Ok(current.clone()),
        }
    }

    // --- Let ---

    /// Keep the recursed right-hand side; the binder's name is chosen in
    /// [`setup_let_scope`](Self::setup_let_scope), once every right-hand side has been visited.
    fn on_let_binding(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Term>],
        _body: &Term,
        binding_idx: usize,
        binding_rec: Term,
    ) -> Result<Self::Binding, Bottom> {
        let v = &vs[binding_idx];
        Ok(VarBinding(v.0.clone(), v.1, binding_rec))
    }

    /// Choose names for the let-bound variables, in scope for the body only.
    ///
    /// `let` in SMTLib binds in parallel, so the right-hand sides — already recursed by now —
    /// correctly saw the *enclosing* scope rather than these new names.
    fn setup_let_scope(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Term>],
        _body: &Term,
        _vs_rec: &[Self::Binding],
    ) -> Result<(), Bottom> {
        self.push_scope(vs.iter().map(|v| (v.1, v.0.clone())));
        Ok(())
    }

    fn on_let(
        &mut self,
        _current: &Term,
        _vs: &[VarBinding<Str, Term>],
        _body: &Term,
        vs_rec: Vec<Self::Binding>,
        body_rec: Term,
    ) -> Result<Term, Bottom> {
        let frame = self
            .name_map
            .pop()
            .expect("let scope must have been pushed");
        // re-label each binder with the name its body was renamed against
        let vs_rec = vs_rec
            .into_iter()
            .map(|VarBinding(name, id, rhs)| {
                VarBinding(frame.get(&id).cloned().unwrap_or(name), id, rhs)
            })
            .collect();
        Ok(self.env.let_term(vs_rec, body_rec))
    }

    // --- Quantifiers ---

    fn setup_quantifier_scope(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Sort>],
        _t: &Term,
        _is_forall: bool,
    ) -> Result<(), Bottom> {
        self.push_scope(vs.iter().map(|v| (v.1, v.0.clone())));
        Ok(())
    }

    fn on_exists(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Sort>],
        _t: &Term,
        t_rec: Term,
    ) -> Result<Term, Bottom> {
        let vs = self.pop_quantifier_bindings(vs);
        Ok(self.env.exists(vs, t_rec))
    }

    fn on_forall(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Sort>],
        _t: &Term,
        t_rec: Term,
    ) -> Result<Term, Bottom> {
        let vs = self.pop_quantifier_bindings(vs);
        Ok(self.env.forall(vs, t_rec))
    }

    // --- Match ---

    /// Choose names for the variables this arm's pattern binds, then re-label the pattern.
    fn setup_match_case_scope(
        &mut self,
        _current: &Term,
        _scrutinee: &Term,
        cases: &[PatternArm],
        _scrutinee_rec: &Self::Out,
        case_idx: usize,
    ) -> Result<Pattern, Bottom> {
        let pattern = &cases[case_idx].pattern;
        self.push_scope(
            pattern
                .variables_and_ids()
                .into_iter()
                .map(|(name, id)| (id, name)),
        );
        Ok(self.rename_pattern(pattern))
    }

    /// Leave the arm's scope; the pattern was already renamed on the way in.
    fn on_match_arm(
        &mut self,
        _current: &Term,
        _scrutinee: &Term,
        _cases: &[PatternArm],
        _scrutinee_rec: &Self::Out,
        _case_idx: usize,
        current_pattern: Pattern,
        arm: Term,
    ) -> Result<PatternArm, Bottom> {
        self.name_map
            .pop()
            .expect("arm scope must have been pushed");
        Ok(PatternArm {
            pattern: current_pattern,
            body: arm,
        })
    }
}

/// Expose the cache to [`MemoizedRecursion`], which consults it before descending into a term and
/// records each result on the way out.
impl<E> Memoizing<Term, Term> for RenameEnv<'_, E> {
    type Cache<'c>
        = &'c mut HashMap<Term, Term>
    where
        Self: 'c;

    fn cache_mut(&mut self) -> Self::Cache<'_> {
        &mut self.cache
    }
}

impl<E> TypedTermRecursor for RenameEnv<'_, E> where E: HasArena {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::allocator::{LocalVarAllocator, ObjectAllocatorExt, StrAllocator};
    use crate::ast::fv::is_closed;
    use crate::ast::{ATerm, AlphaEquiv, CheckedApi, Context, Typecheck};
    use crate::traits::Repr;
    use crate::untyped::UntypedAst;

    fn setup() -> Context {
        let mut ctx = Context::new();
        UntypedAst
            .parse_script_str(
                r#"
            (set-logic ALL)
            (declare-const n Int)
            (declare-fun p (Int) Bool)
            (declare-fun q (Int Int) Bool)
            (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
            (declare-datatype Color ((red) (green)))
            (declare-const c Color)
            (declare-const pr Pair)
        "#,
            )
            .unwrap()
            .type_check(&mut ctx)
            .unwrap();
        ctx
    }

    fn parse(ctx: &mut Context, s: &str) -> Term {
        UntypedAst
            .parse_term_str(s)
            .unwrap()
            .type_check(ctx)
            .unwrap()
    }

    /// Rename `s` and assert it prints as `expected`, and that renaming preserved its meaning.
    fn assert_renames_to(s: &str, expected: &str) {
        let mut ctx = setup();
        let t = parse(&mut ctx, s);
        let renamed = t.alpha_rename(&mut ctx);
        assert_eq!(renamed.to_string(), expected);
        assert!(renamed.aeq(&t), "renaming must be alpha preserving");
    }

    /// Assert `s` binds nothing, so there is nothing to rename and the very same term comes back.
    fn assert_unchanged(s: &str) {
        let mut ctx = setup();
        let t = parse(&mut ctx, s);
        let renamed = t.alpha_rename(&mut ctx);
        assert_eq!(renamed.to_string(), t.to_string());
        // nothing was rebuilt, so hashconsing is preserved
        assert_eq!(renamed, t, "a term with no binder should come back as-is");
    }

    /// Every binder gets a freshly minted name, whether or not its own name clashed.
    #[test]
    fn test_every_binder_is_renamed() {
        assert_renames_to("(forall ((x Int)) (p x))", "(forall ((x-0 Int)) (p x-0))");
        assert_renames_to("(exists ((x Int)) (p x))", "(exists ((x-0 Int)) (p x-0))");
        assert_renames_to(
            "(forall ((x Int) (y Int)) (q x y))",
            "(forall ((x-0 Int) (y-0 Int)) (q x-0 y-0))",
        );
        assert_renames_to("(let ((x n)) (p x))", "(let ((x-0 n)) (p x-0))");
        assert_renames_to(
            "(forall ((x Int)) (exists ((y Int)) (q x y)))",
            "(forall ((x-0 Int)) (exists ((y-0 Int)) (q x-0 y-0)))",
        );
        assert_renames_to(
            "(match pr (((mk-pair a b) (q a b))))",
            "(match pr (((mk-pair a-0 b-0) (q a-0 b-0))))",
        );
        assert_renames_to(
            "(forall ((x Int)) (! (p x) :pattern ((p x))))",
            "(forall ((x-0 Int)) (! (p x-0) :pattern ((p x-0))))",
        );
    }

    /// A term that binds nothing has nothing to rename, and is returned as it is.
    #[test]
    fn test_no_binder_no_rename() {
        assert_unchanged("(p n)");
        // constructor-only patterns bind no variable
        assert_unchanged("(match c ((red true) (green false)))");
    }

    /// Shadowing binders end up with distinct names, and each variable follows its own binder.
    #[test]
    fn test_rename_shadowing() {
        assert_renames_to(
            "(forall ((x Int)) (exists ((x Int)) (p x)))",
            "(forall ((x-0 Int)) (exists ((x-1 Int)) (p x-1)))",
        );
        assert_renames_to(
            "(forall ((x Int)) (and (forall ((x Int)) (p x)) (p x)))",
            "(forall ((x-0 Int)) (and (forall ((x-1 Int)) (p x-1)) (p x-0)))",
        );
    }

    /// Three levels deep, each binder gets its own name.
    #[test]
    fn test_rename_nested_shadowing() {
        assert_renames_to(
            "(forall ((x Int)) (exists ((x Int)) (forall ((x Int)) (p x))))",
            "(forall ((x-0 Int)) (exists ((x-1 Int)) (forall ((x-2 Int)) (p x-2))))",
        );
    }

    /// Sibling scopes are disjoint, but reusing a name across them would still print ambiguously,
    /// so they are separated too.
    #[test]
    fn test_rename_sibling_scopes() {
        assert_renames_to(
            "(and (forall ((x Int)) (p x)) (forall ((x Int)) (p x)))",
            "(and (forall ((x-0 Int)) (p x-0)) (forall ((x-1 Int)) (p x-1)))",
        );
    }

    /// Two binders in a single binder list are separated as well.
    #[test]
    fn test_rename_clash_in_one_binder_list() {
        let mut ctx = setup();
        let int = ctx.int_sort();
        // build `(forall ((x Int) (x Int)) (q x x))` directly: the parser would reject the
        // duplicate name, but the unchecked API allows it and the ids keep it well-formed
        let id1 = ctx.new_local();
        let id2 = ctx.new_local();
        let x = ctx.allocate_symbol("x");
        let v1 = VarBinding(x.clone(), id1, int.clone());
        let v2 = VarBinding(x, id2, int);
        let l1 = ctx.local(Local::from(v1.clone()));
        let l2 = ctx.local(Local::from(v2.clone()));
        let body = ctx.typed_simp_app("q", [l1, l2]).unwrap();
        let t = ctx.forall(vec![v1, v2], body);
        assert_eq!(t.to_string(), "(forall ((x Int) (x Int)) (q x x))");

        let renamed = t.alpha_rename(&mut ctx);
        assert_eq!(
            renamed.to_string(),
            "(forall ((x-0 Int) (x-1 Int)) (q x-0 x-1))"
        );
    }

    /// Free variables and globals are untouched; only binders and their own variables move.
    #[test]
    fn test_rename_leaves_free_and_global_alone() {
        assert_unchanged("(p n)");
        assert_renames_to(
            "(forall ((x Int)) (q x n))",
            "(forall ((x-0 Int)) (q x-0 n))",
        );
    }

    /// A bound name is renamed even when it collides with a *global*, and the fresh name never
    /// captures a name the arena already knows.
    #[test]
    fn test_rename_ignores_global_names() {
        assert_renames_to("(forall ((n Int)) (p n))", "(forall ((n-0 Int)) (p n-0))");
    }

    /// `let` binds in parallel: a right-hand side sees the enclosing scope, not the new bindings.
    /// Here the inner `y`'s right-hand side is the *outer* `x`, so it follows the outer binder.
    #[test]
    fn test_rename_let_is_parallel() {
        assert_renames_to(
            "(let ((x n)) (let ((x 1) (y x)) (q x y)))",
            "(let ((x-0 n)) (let ((x-1 1) (y-1 x-0)) (q x-1 y-1)))",
        );
    }

    #[test]
    fn test_rename_match() {
        // the pattern variable and the enclosing binder end up with distinct names
        assert_renames_to(
            "(forall ((a Int)) (and (p a) (match pr (((mk-pair a b) (q a b))))))",
            "(forall ((a-0 Int)) (and (p a-0) (match pr (((mk-pair a-1 b-1) (q a-1 b-1))))))",
        );
        // a named wildcard binds one variable, and is renamed like any other binder
        assert_renames_to(
            "(forall ((w Int)) (and (p w) (match c ((red true) (w (p 1))))))",
            "(forall ((w-0 Int)) (and (p w-0) (match c ((red true) (w-1 (p 1))))))",
        );
    }

    /// `:pattern` carries terms, whose variables must be re-labelled along with the body.
    #[test]
    fn test_rename_annotated() {
        assert_renames_to(
            "(forall ((x Int)) (exists ((x Int)) (! (p x) :pattern ((p x)))))",
            "(forall ((x-0 Int)) (exists ((x-1 Int)) (! (p x-1) :pattern ((p x-1)))))",
        );
    }

    /// Renaming is *not* idempotent: every pass mints new names, so a second pass relabels again.
    /// The result stays alpha equivalent and clash free, it is just not the same term.
    #[test]
    fn test_rename_twice_mints_new_names() {
        let mut ctx = setup();
        let t = parse(&mut ctx, "(forall ((x Int)) (exists ((x Int)) (p x)))");
        let once = t.alpha_rename(&mut ctx);
        assert_eq!(
            once.to_string(),
            "(forall ((x-0 Int)) (exists ((x-1 Int)) (p x-1)))"
        );
        let twice = once.alpha_rename(&mut ctx);
        assert_eq!(
            twice.to_string(),
            "(forall ((x-2 Int)) (exists ((x-3 Int)) (p x-3)))"
        );
        assert_ne!(twice, once, "a second pass picks new names");
        assert!(twice.aeq(&once), "but only the labels change");
    }

    /// A fresh name strips any `-N` trailer, so suffixes do not accumulate.
    #[test]
    fn test_rename_strips_numeric_trailer() {
        assert_renames_to(
            "(forall ((|x-0| Int)) (exists ((|x-0| Int)) (p |x-0|)))",
            "(forall ((x-1 Int)) (exists ((x-2 Int)) (p x-2)))",
        );
    }

    /// A name containing `-` but no numeric trailer keeps its whole name as prefix.
    #[test]
    fn test_rename_prefix_with_dash() {
        assert_renames_to(
            "(forall ((|my-var| Int)) (exists ((|my-var| Int)) (p |my-var|)))",
            "(forall ((my-var-0 Int)) (exists ((my-var-1 Int)) (p my-var-1)))",
        );
    }

    /// Ids are preserved: only the printed labels change.
    #[test]
    fn test_rename_preserves_ids() {
        let mut ctx = setup();
        let t = parse(&mut ctx, "(forall ((x Int)) (exists ((x Int)) (p x)))");
        let renamed = t.alpha_rename(&mut ctx);
        let (ATerm::Forall(vs1, b1), ATerm::Forall(vs2, b2)) = (t.repr(), renamed.repr()) else {
            panic!("expected foralls")
        };
        assert_eq!(vs1[0].1, vs2[0].1, "the outer binder keeps its id");
        assert_ne!(vs1[0].0, vs2[0].0, "but gets a new name");

        let (ATerm::Exists(is1, _), ATerm::Exists(is2, _)) = (b1.repr(), b2.repr()) else {
            panic!("expected exists")
        };
        assert_eq!(is1[0].1, is2[0].1, "the inner binder keeps its id");
        assert_ne!(is1[0].0, is2[0].0, "and a new name too");
    }

    /// A shared sub-term is renamed once and the result reused, so the sharing survives.
    ///
    /// The two occurrences are the same hashconsed term, hence the same binder, and each sits in
    /// its own scope — so one name is unambiguous and the cached result serves both.
    #[test]
    fn test_rename_shared_subterm_stays_shared() {
        let mut ctx = setup();
        let inner = parse(&mut ctx, "(forall ((x Int)) (p x))");
        let t = ctx.and(vec![inner.clone(), inner.clone()]);
        let renamed = t.alpha_rename(&mut ctx);
        assert_eq!(
            renamed.to_string(),
            "(and (forall ((x-0 Int)) (p x-0)) (forall ((x-0 Int)) (p x-0)))"
        );
        // the cache returns the identical term for both conjuncts, so the sharing is intact
        let ATerm::And(ts) = renamed.repr() else {
            panic!("expected an and")
        };
        assert_eq!(ts[0], ts[1], "both conjuncts are the same renamed term");

        // distinct binders that merely share a name are still separated. the suffixes start at 1
        // because the rename above already took `x-0` out of this context's name supply
        let other = parse(&mut ctx, "(forall ((x Int)) (p x))");
        assert_ne!(other, inner, "separately parsed binders have distinct ids");
        let t = ctx.and(vec![inner, other]);
        assert_eq!(
            t.alpha_rename(&mut ctx).to_string(),
            "(and (forall ((x-1 Int)) (p x-1)) (forall ((x-2 Int)) (p x-2)))"
        );
    }

    /// A sub-term shared across sibling scopes is renamed once, and every occurrence agrees.
    #[test]
    fn test_rename_shared_subterm_under_clashing_binders() {
        let mut ctx = setup();
        let shared = parse(&mut ctx, "(forall ((y Int)) (p y))");
        // `(and shared shared)` under two binders that clash on `x`
        let outer = parse(&mut ctx, "(forall ((x Int)) (exists ((x Int)) true))");
        let body = ctx.and(vec![shared.clone(), shared]);
        let t = ctx.and(vec![outer, body]);
        let renamed = t.alpha_rename(&mut ctx);
        // the clashing binders are separated; the shared sub-term keeps one name throughout
        assert_eq!(
            renamed.to_string(),
            "(and (forall ((x-0 Int)) (exists ((x-1 Int)) true)) \
             (and (forall ((y-1 Int)) (p y-1)) (forall ((y-1 Int)) (p y-1))))"
        );
    }

    /// The point of renaming: a term with shadowing does not round-trip through printing, but
    /// its renamed form does, because every binder now has a distinct name.
    #[test]
    fn test_rename_enables_print_roundtrip() {
        let mut ctx = setup();
        let t = parse(&mut ctx, "(forall ((x Int)) (exists ((x Int)) (q x x)))");
        let renamed = t.alpha_rename(&mut ctx);
        let reparsed = parse(&mut ctx, &renamed.to_string());
        assert_eq!(reparsed.to_string(), renamed.to_string());
    }

    // --- Closed terms and alpha equivalence ---
    //
    // Strict `aeq` requires free local variables to be literally the same variable on both sides,
    // so it is only a meaningful check against a *reparsed* term when the term is closed: parsing
    // mints new ids, and a free variable would come back as a different variable. Every fixture
    // below is asserted closed for that reason.

    /// Closed terms covering each kind of binder, plus the shapes renaming has to get right.
    fn closed_terms() -> Vec<&'static str> {
        #[allow(unused_mut)]
        let mut terms = vec![
            // one binder of each kind, nothing to resolve
            "(forall ((x Int)) (p x))",
            "(exists ((x Int)) (p x))",
            "(forall ((x Int) (y Int)) (q x y))",
            "(let ((x n)) (p x))",
            "(match pr (((mk-pair a b) (q a b))))",
            "(match c ((red true) (green false)))",
            // globals and constants are not local variables, so these are still closed
            "(forall ((x Int)) (q x n))",
            "(forall ((n Int)) (p n))",
            // shadowing, the case renaming exists for
            "(forall ((x Int)) (exists ((x Int)) (p x)))",
            "(forall ((x Int)) (exists ((x Int)) (forall ((x Int)) (p x))))",
            "(forall ((x Int)) (and (forall ((x Int)) (p x)) (p x)))",
            // sibling scopes reusing a name
            "(and (forall ((x Int)) (p x)) (forall ((x Int)) (p x)))",
            // parallel `let`: the inner `y` is bound to the outer `x`
            "(let ((x n)) (let ((x 1) (y x)) (q x y)))",
            // a pattern variable clashing with an enclosing binder
            "(forall ((a Int)) (and (p a) (match pr (((mk-pair a b) (q a b))))))",
            // a named wildcard clashing with an enclosing binder
            "(forall ((w Int)) (and (p w) (match c ((red true) (w (p 1))))))",
            // `:pattern` terms carry variables too
            "(forall ((x Int)) (! (p x) :pattern ((p x))))",
            "(forall ((x Int)) (exists ((x Int)) (! (p x) :pattern ((p x)))))",
            // already-suffixed names, which the prefix logic has to handle
            "(forall ((|x-0| Int)) (exists ((|x-0| Int)) (p |x-0|)))",
            "(forall ((|my-var| Int)) (exists ((|my-var| Int)) (p |my-var|)))",
        ];
        // `:no-pattern` carries a single term, whose variables must be re-labelled like `:pattern`
        #[cfg(feature = "no-pattern")]
        terms.extend([
            "(forall ((x Int)) (! (p x) :no-pattern (p x)))",
            "(forall ((x Int)) (exists ((x Int)) (! (p x) :no-pattern (p x))))",
            "(forall ((x Int)) (! (p x) :pattern ((p x)) :no-pattern (p x)))",
        ]);
        terms
    }

    /// Renaming a closed term produces an alpha equivalent term: only the labels move.
    #[test]
    fn test_rename_closed_term_is_alpha_eq() {
        for s in closed_terms() {
            let mut ctx = setup();
            let t = parse(&mut ctx, s);
            assert!(is_closed(&t), "fixture must be closed: {s}");
            let renamed = t.alpha_rename(&mut ctx);
            assert!(
                is_closed(&renamed),
                "renaming must not free a variable: {s}"
            );
            assert!(renamed.aeq(&t), "renaming must be alpha preserving: {s}");
        }
    }

    /// A renamed closed term survives a print/parse round-trip up to alpha equivalence.
    ///
    /// This is what renaming buys: reparsing mints new ids and re-resolves every name by lexical
    /// scoping, so the result can only match the original when no binder is shadowed.
    #[test]
    fn test_rename_closed_term_roundtrips_alpha_eq() {
        for s in closed_terms() {
            let mut ctx = setup();
            let t = parse(&mut ctx, s);
            assert!(is_closed(&t), "fixture must be closed: {s}");
            let renamed = t.alpha_rename(&mut ctx);
            let reparsed = parse(&mut ctx, &renamed.to_string());
            assert!(
                reparsed.aeq(&t),
                "renamed term must reparse to an alpha equivalent term: {s}\n  \
                 renamed:  {renamed}\n  reparsed: {reparsed}"
            );
        }
    }

    /// Renaming a closed term twice still gives an alpha equivalent term, even though each pass
    /// picks new labels.
    #[test]
    fn test_repeated_rename_of_closed_term_stays_alpha_eq() {
        for s in closed_terms() {
            let mut ctx = setup();
            let t = parse(&mut ctx, s);
            let once = t.alpha_rename(&mut ctx);
            let twice = once.alpha_rename(&mut ctx);
            assert!(
                twice.aeq(&once),
                "second pass must stay alpha equivalent: {s}"
            );
            assert!(twice.aeq(&t), "and equivalent to the original: {s}");
        }
    }

    /// A closed term whose printed form is *ambiguous* does not round-trip, but its renamed form
    /// does — the concrete reason the pass exists.
    ///
    /// The body of the `exists` refers to the *outer* `x`, so printing loses that: reparsing binds
    /// the printed `x` to the inner binder instead. Renaming separates the two names first.
    #[test]
    fn test_rename_repairs_ambiguous_closed_term() {
        let mut ctx = setup();
        let int = ctx.int_sort();
        // build `(forall ((x Int)) (exists ((x Int)) (p x)))` where `(p x)` is the *outer* `x`.
        // the parser cannot produce this, but the unchecked API can, and the ids keep it
        // well-formed
        let outer_id = ctx.new_local();
        let inner_id = ctx.new_local();
        let x = ctx.allocate_symbol("x");
        let outer = VarBinding(x.clone(), outer_id, int.clone());
        let inner = VarBinding(x, inner_id, int);
        let outer_occurrence = ctx.local(Local::from(outer.clone()));
        let body = ctx.typed_simp_app("p", [outer_occurrence]).unwrap();
        let inner_term = ctx.exists(vec![inner], body);
        let t = ctx.forall(vec![outer], inner_term);
        assert!(
            is_closed(&t),
            "both binders are in scope, so the term is closed"
        );
        assert_eq!(t.to_string(), "(forall ((x Int)) (exists ((x Int)) (p x)))");

        // printed as it is, the inner binder captures the occurrence: not alpha equivalent
        let reparsed = parse(&mut ctx, &t.to_string());
        assert!(
            !reparsed.aeq(&t),
            "the shadowed binder should capture the occurrence on reparse"
        );

        // after renaming, the two binders differ and the occurrence survives the round-trip
        let renamed = t.alpha_rename(&mut ctx);
        assert_eq!(
            renamed.to_string(),
            "(forall ((x-0 Int)) (exists ((x-1 Int)) (p x-0)))"
        );
        assert!(renamed.aeq(&t), "renaming must be alpha preserving");
        let reparsed = parse(&mut ctx, &renamed.to_string());
        assert!(
            reparsed.aeq(&t),
            "the renamed term must reparse to an alpha equivalent term"
        );
    }
}
