// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Let-elimination: inlining let-bound variables.
//!
//! Let-elimination expands all local variables introduced by `let`-bindings with their bound
//! terms. After let-elimination, the resulting term contains no `let`-bindings, which simplifies
//! subsequent analysis (e.g. substitution, free variable computation, CNF conversion).
//!
//! Two implementations are provided:
//!
//! - [`LetElim`] — a trait-based recursive implementation. Simple to use via
//!   `.let_elim(&mut context)`, but may overflow the call stack on deeply nested terms.
//! - [`LetEliminator`] — a stack-safe implementation built on [`TermRecursor`]. It uses
//!   [`Memoize`] for automatic caching of shared sub-terms. Create one via
//!   [`LetEliminator::create(&mut arena)`](LetEliminator::create).
//!
//! # Untouched sub-terms are shared, not rebuilt
//!
//! Most terms contain no `let` at all, and even in those that do, only the sub-terms mentioning
//! a let-bound variable actually change. So the recursion produces an `Option<Term>`, where
//! [`None`] means "this sub-term is unchanged" and `Some(t)` means "this sub-term became `t`".
//! A node whose children all report [`None`] reports [`None`] in turn, so it is never
//! re-allocated through the arena — the original is reused. Only the spine leading to an
//! inlined variable is rebuilt.
//!
//! Note: let-elimination may increase term size due to duplication of shared sub-terms. For the
//! inverse operation (re-introducing let-bindings to share common sub-terms), see
//! [`crate::ast::letintro`].

use crate::allocator::TermAllocator;
use crate::ast::Sort;
use crate::ast::{
    Attribute, Constant, HasArena, Local, Memoize, PatternArm, QualifiedIdentifier, Str, Term,
    TermRecursor, TypedTermRecursor,
};
use crate::containers::Mapping;
use crate::raw::alg::rec::Bottom;
use crate::raw::alg::{LocalId, VarBinding};
use std::collections::HashMap;
use yaspar::ast::Keyword;

/// Eliminates all let-bindings by applying substitutions properly
///
/// This trait assumes that the given object has been type-checked.
pub trait LetElim<Env> {
    fn let_elim(&self, env: &mut Env) -> Self;
}

/// Rebuild the children of a node, or [`None`] when every one of them is unchanged.
///
/// `recs` holds the recursion result for each of `originals`, so the two agree in length, and
/// `rebuild` turns a changed result back into a child. A [`None`] return is what lets a node
/// report *itself* as unchanged instead of rebuilding.
///
/// The children are walked exactly once, and nothing is allocated at all unless one of them
/// really changed: the output vector is created on the first change, seeded with the unchanged
/// children already passed over.
fn rebuild_if_changed<T, R>(
    originals: &[T],
    recs: Vec<Option<R>>,
    rebuild: impl Fn(&T, R) -> T,
) -> Option<Vec<T>>
where
    T: Clone,
{
    let mut out: Option<Vec<T>> = None;
    for (idx, (rec, original)) in recs.into_iter().zip(originals).enumerate() {
        match rec {
            Some(rec) => out
                .get_or_insert_with(|| {
                    let mut built = Vec::with_capacity(originals.len());
                    built.extend_from_slice(&originals[..idx]);
                    built
                })
                .push(rebuild(original, rec)),
            // an unchanged child is only worth recording once we are already rebuilding
            None => {
                if let Some(built) = &mut out {
                    built.push(original.clone())
                }
            }
        }
    }
    out
}

/// [`rebuild_if_changed`] for children that the recursion already hands back fully rebuilt.
fn materialize_if_changed<T: Clone>(originals: &[T], recs: Vec<Option<T>>) -> Option<Vec<T>> {
    rebuild_if_changed(originals, recs, |_, rec| rec)
}

/// Stack-safe let-elimination using [`TermRecursor`].
///
/// It can be wrapped with [`Memoize`] for caching.
pub struct LetEliminatorInner<'a, E> {
    arena: &'a mut E,
    /// Environment stack: each frame maps a local variable id to the substituted term.
    /// Quantifier/match-bound variables are represented by frames with no entry
    /// (their locals simply won't be found, so they pass through unchanged).
    env: Vec<HashMap<LocalId, Option<Term>>>,
}

/// Memoized, stack-safe let-eliminator. Use [`LetEliminator::create`] to construct.
pub type LetEliminator<'a, E> = Memoize<LetEliminatorInner<'a, E>, HashMap<Term, Option<Term>>>;

impl<'a, E> LetEliminatorInner<'a, E>
where
    E: HasArena,
{
    pub fn new(arena: &'a mut E) -> Self {
        Self {
            arena,
            env: Vec::new(),
        }
    }

    /// Search the environment stack for a variable by id.
    ///
    /// Returns `Some(Some(term))` for let-bound variables (substitute with `term`),
    /// `Some(None)` for quantifier/match-bound variables (do not substitute),
    /// or `None` if the variable is not in any scope.
    fn lookup(&self, id: LocalId) -> Option<Option<Term>> {
        self.env.lookup(&id)
    }
}

impl<'a, E> LetEliminator<'a, E>
where
    E: HasArena,
{
    /// Create a new memoized let-eliminator backed by the given arena.
    pub fn create(arena: &'a mut E) -> Self {
        Memoize::new(LetEliminatorInner::new(arena))
    }
}

/// Every callback returns [`None`] to mean "unchanged", so an untouched sub-term costs nothing:
/// no arena allocation, and the caller keeps sharing the original. `Self::Attr`, `Self::Binding`
/// and `Self::Arm` carry the same convention for attributes, let-bindings and match arms.
impl<E: HasArena> TermRecursor<Str, Sort, Term> for LetEliminatorInner<'_, E> {
    type Out = Option<Term>;
    type Attr = Option<Attribute>;
    type Binding = Option<VarBinding<Str, Term>>;
    type Pattern = (); // match-bound vars use empty frames, no substitution
    type Arm = Option<Term>; // the arm's new body; the pattern never changes
    type Err = Bottom;

    // --- Leaves ---

    fn on_constant(
        &mut self,
        _: &Term,
        _: &Constant,
        _: &Option<Sort>,
    ) -> Result<Self::Out, Bottom> {
        Ok(None)
    }

    fn on_global(
        &mut self,
        _: &Term,
        _: &QualifiedIdentifier,
        _: &Option<Sort>,
    ) -> Result<Self::Out, Bottom> {
        Ok(None)
    }

    /// Look up the local variable in the environment. A let-bound variable
    /// (`Some(Some(t))`) is replaced by `t`; a quantifier/match-bound or free one is unchanged.
    fn on_local(&mut self, _: &Term, id: &Local) -> Result<Self::Out, Bottom> {
        Ok(self.lookup(id.id).flatten())
    }

    fn on_app(
        &mut self,
        _: &Term,
        id: &QualifiedIdentifier,
        ts: &[Term],
        s: &Option<Sort>,
        recs: Vec<Self::Out>,
    ) -> Result<Self::Out, Bottom> {
        Ok(materialize_if_changed(ts, recs)
            .map(|ts| self.arena.arena().app(id.clone(), ts, s.clone())))
    }

    // --- Let ---

    /// A binding whose right-hand side is unchanged reports [`None`], like every other callback,
    /// so nothing is rebuilt for it. [`Self::setup_let_scope`] reads the original instead.
    fn on_let_binding(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Term>],
        _: &Term,
        binding_idx: usize,
        rec: Self::Out,
    ) -> Result<Self::Binding, Bottom> {
        let v = &vs[binding_idx];
        Ok(rec.map(|rhs| VarBinding(v.0.clone(), v.1, rhs)))
    }

    /// Push a new scope frame mapping each let-bound variable to the term it stands for: its
    /// rebuilt right-hand side, or the original one when the recursion left it unchanged.
    ///
    /// This is the same "rebuilt else original" fallback as `rebuild_if_changed`, but there is
    /// no vector to build here — the right-hand sides go straight into the scope frame.
    fn setup_let_scope(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Term>],
        _: &Term,
        vs_rec: &[Self::Binding],
    ) -> Result<(), Bottom> {
        let frame = vs
            .iter()
            .zip(vs_rec)
            .map(|(v, rec)| (v.1, Some(rec.as_ref().unwrap_or(v).2.clone())))
            .collect();
        self.env.push(frame);
        Ok(())
    }

    /// Pop the let scope and return the body directly — the let-binding is eliminated.
    ///
    /// This is always a change: the `let` node itself is gone, whatever happened to the body.
    fn on_let(
        &mut self,
        _: &Term,
        _: &[VarBinding<Str, Term>],
        body: &Term,
        _: Vec<Self::Binding>,
        body_rec: Self::Out,
    ) -> Result<Self::Out, Bottom> {
        self.env.pop();
        Ok(Some(body_rec.unwrap_or_else(|| body.clone())))
    }

    // --- Quantifiers ---

    /// Push a scope frame with `None` values so quantifier-bound variables shadow
    /// any outer let-bindings and are not substituted.
    fn setup_quantifier_scope(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Sort>],
        _: &Term,
        _: bool,
    ) -> Result<(), Bottom> {
        self.env.push(vs.iter().map(|v| (v.1, None)).collect());
        Ok(())
    }

    fn on_exists(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Sort>],
        _: &Term,
        body: Self::Out,
    ) -> Result<Self::Out, Bottom> {
        self.env.pop();
        Ok(body.map(|body| self.arena.arena().exists(vs.to_vec(), body)))
    }

    fn on_forall(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Sort>],
        _: &Term,
        body: Self::Out,
    ) -> Result<Self::Out, Bottom> {
        self.env.pop();
        Ok(body.map(|body| self.arena.arena().forall(vs.to_vec(), body)))
    }

    // --- Match ---

    /// Push a scope frame with `None` values for pattern-bound variables, similar to quantifiers.
    fn setup_match_case_scope(
        &mut self,
        _: &Term,
        _: &Term,
        cases: &[PatternArm],
        _: &Self::Out,
        idx: usize,
    ) -> Result<Self::Pattern, Bottom> {
        self.env.push(
            cases[idx]
                .pattern
                .variables_and_ids()
                .into_iter()
                .map(|(_, id)| (id, None))
                .collect(),
        );
        Ok(())
    }

    /// Pop the arm's scope and pass its body up. The pattern is left to [`Self::on_match`],
    /// which only clones it if the match has to be rebuilt at all.
    fn on_match_arm(
        &mut self,
        _: &Term,
        _: &Term,
        _: &[PatternArm],
        _: &Self::Out,
        _: usize,
        _: Self::Pattern,
        body: Self::Out,
    ) -> Result<Self::Arm, Bottom> {
        self.env.pop();
        Ok(body)
    }

    fn on_match(
        &mut self,
        _: &Term,
        scrutinee: &Term,
        cases: &[PatternArm],
        scrutinee_rec: Self::Out,
        cases_rec: Vec<Self::Arm>,
    ) -> Result<Self::Out, Bottom> {
        let arms = rebuild_if_changed(cases, cases_rec, |case, body| PatternArm {
            pattern: case.pattern.clone(),
            body,
        });
        if scrutinee_rec.is_none() && arms.is_none() {
            return Ok(None);
        }
        let scrutinee = scrutinee_rec.unwrap_or_else(|| scrutinee.clone());
        let arms = arms.unwrap_or_else(|| cases.to_vec());
        Ok(Some(self.arena.arena().matching(scrutinee, arms)))
    }

    // --- Annotations ---

    fn on_annotated(
        &mut self,
        _: &Term,
        t: &Term,
        anns: &[Attribute],
        t_rec: Self::Out,
        anns_rec: Vec<Self::Attr>,
    ) -> Result<Self::Out, Bottom> {
        let anns_rec = materialize_if_changed(anns, anns_rec);
        if t_rec.is_none() && anns_rec.is_none() {
            return Ok(None);
        }
        let body = t_rec.unwrap_or_else(|| t.clone());
        let anns = anns_rec.unwrap_or_else(|| anns.to_vec());
        Ok(Some(self.arena.arena().annotated(body, anns)))
    }

    fn on_attribute_keyword(&mut self, _: &Keyword) -> Result<Self::Attr, Bottom> {
        Ok(None)
    }

    fn on_attribute_constant(&mut self, _: &Keyword, _: &Constant) -> Result<Self::Attr, Bottom> {
        Ok(None)
    }

    fn on_attribute_symbol(&mut self, _: &Keyword, _: &Str) -> Result<Self::Attr, Bottom> {
        Ok(None)
    }

    fn on_attribute_named(&mut self, _: &Str) -> Result<Self::Attr, Bottom> {
        Ok(None)
    }

    fn on_attribute_pattern(
        &mut self,
        patterns: &[Term],
        recs: Vec<Self::Out>,
    ) -> Result<Self::Attr, Bottom> {
        Ok(materialize_if_changed(patterns, recs).map(Attribute::Pattern))
    }

    #[cfg(feature = "no-pattern")]
    fn on_attribute_no_pattern(&mut self, _: &Term, rec: Self::Out) -> Result<Self::Attr, Bottom> {
        Ok(rec.map(Attribute::NoPattern))
    }

    // --- Connectives ---

    fn on_eq(
        &mut self,
        _: &Term,
        a: &Term,
        b: &Term,
        a_rec: Self::Out,
        b_rec: Self::Out,
    ) -> Result<Self::Out, Bottom> {
        if a_rec.is_none() && b_rec.is_none() {
            return Ok(None);
        }
        let a = a_rec.unwrap_or_else(|| a.clone());
        let b = b_rec.unwrap_or_else(|| b.clone());
        Ok(Some(self.arena.arena().eq(a, b)))
    }

    fn on_distinct(
        &mut self,
        _: &Term,
        ts: &[Term],
        recs: Vec<Self::Out>,
    ) -> Result<Self::Out, Bottom> {
        Ok(materialize_if_changed(ts, recs).map(|ts| self.arena.arena().distinct(ts)))
    }

    fn on_and(&mut self, _: &Term, ts: &[Term], recs: Vec<Self::Out>) -> Result<Self::Out, Bottom> {
        Ok(materialize_if_changed(ts, recs).map(|ts| self.arena.arena().and(ts)))
    }

    fn on_or(&mut self, _: &Term, ts: &[Term], recs: Vec<Self::Out>) -> Result<Self::Out, Bottom> {
        Ok(materialize_if_changed(ts, recs).map(|ts| self.arena.arena().or(ts)))
    }

    fn on_xor(&mut self, _: &Term, ts: &[Term], recs: Vec<Self::Out>) -> Result<Self::Out, Bottom> {
        Ok(materialize_if_changed(ts, recs).map(|ts| self.arena.arena().xor(ts)))
    }

    fn on_not(&mut self, _: &Term, _: &Term, rec: Self::Out) -> Result<Self::Out, Bottom> {
        Ok(rec.map(|t| self.arena.arena().not(t)))
    }

    fn on_implies(
        &mut self,
        _: &Term,
        ts: &[Term],
        t: &Term,
        ts_rec: Vec<Self::Out>,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Bottom> {
        let ts_rec = materialize_if_changed(ts, ts_rec);
        if t_rec.is_none() && ts_rec.is_none() {
            return Ok(None);
        }
        let premises = ts_rec.unwrap_or_else(|| ts.to_vec());
        let conclusion = t_rec.unwrap_or_else(|| t.clone());
        Ok(Some(self.arena.arena().implies(premises, conclusion)))
    }

    fn on_ite(
        &mut self,
        _: &Term,
        b: &Term,
        t: &Term,
        e: &Term,
        b_rec: Self::Out,
        t_rec: Self::Out,
        e_rec: Self::Out,
    ) -> Result<Self::Out, Bottom> {
        if b_rec.is_none() && t_rec.is_none() && e_rec.is_none() {
            return Ok(None);
        }
        let b = b_rec.unwrap_or_else(|| b.clone());
        let t = t_rec.unwrap_or_else(|| t.clone());
        let e = e_rec.unwrap_or_else(|| e.clone());
        Ok(Some(self.arena.arena().ite(b, t, e)))
    }
}

impl<E: HasArena> TypedTermRecursor for LetEliminatorInner<'_, E> {}

impl<E> LetElim<E> for Term
where
    E: HasArena,
{
    fn let_elim(&self, env: &mut E) -> Self {
        LetEliminator::create(env)
            .recurse_on_term_no_err(self)
            .unwrap_or_else(|| self.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::fv::FreeLocalVars;
    use crate::ast::{AlphaEquiv, Context, Typecheck};
    use crate::untyped::UntypedAst;

    #[test]
    fn test_let_elim1() {
        let mut context = Context::default();
        context.ensure_logic();
        let t = UntypedAst
            .parse_term_str("(let ((x (+ 1 2))) (* x x))")
            .unwrap()
            .type_check(&mut context)
            .unwrap()
            .let_elim(&mut context);
        let equiv = UntypedAst
            .parse_term_str("(* (+ 1 2) (+ 1 2))")
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        assert_eq!(t, equiv);
    }

    #[test]
    fn test_let_elim2() {
        let mut context = Context::default();
        context.ensure_logic();
        let t = UntypedAst
            .parse_term_str("(let ((x (+ 1 2))) (! (* x x) :pattern (x)))")
            .unwrap()
            .type_check(&mut context)
            .unwrap()
            .let_elim(&mut context);
        let equiv = UntypedAst
            .parse_term_str("(! (* (+ 1 2) (+ 1 2)) :pattern ((+ 1 2)))")
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        assert_eq!(t, equiv);
    }

    #[test]
    fn test_let_elim_xor() {
        let mut context = Context::default();
        context.ensure_logic();
        let t = UntypedAst
            .parse_term_str("(let ((p true) (q false)) (xor p q))")
            .unwrap()
            .type_check(&mut context)
            .unwrap()
            .let_elim(&mut context);
        let equiv = UntypedAst
            .parse_term_str("(xor true false)")
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        assert_eq!(t, equiv);
    }

    /// A term with no `let` must come back as the very same term, not a rebuilt copy.
    ///
    /// `recurse_on_term` reporting [`None`] is what guarantees nothing was re-allocated.
    #[test]
    fn test_let_elim_unchanged_is_none() {
        let mut context = Context::default();
        context.ensure_logic();
        let t = UntypedAst
            .parse_term_str(
                "(forall ((y Int)) (! (=> (> y 0) (distinct (ite true y 1) 2)) :named a))",
            )
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        assert_eq!(
            LetEliminator::create(&mut context).recurse_on_term_no_err(&t),
            None
        );
        assert_eq!(t.let_elim(&mut context), t);
    }

    /// Only the spine down to the inlined variable is rebuilt; the untouched sibling of a
    /// changed node is reported unchanged and so stays shared.
    #[test]
    fn test_let_elim_partial_change() {
        let mut context = Context::default();
        context.ensure_logic();
        let t = UntypedAst
            .parse_term_str("(and (let ((x 1)) (> x 0)) (< 2 3))")
            .unwrap()
            .type_check(&mut context)
            .unwrap()
            .let_elim(&mut context);
        let equiv = UntypedAst
            .parse_term_str("(and (> 1 0) (< 2 3))")
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        assert_eq!(t, equiv);
    }

    /// Elimination must not leave a let-bound variable behind.
    ///
    /// Every local in a well-formed term is bound, and elimination deletes the `let` binders,
    /// so a variable that was not replaced by its bound term would show up here as a free local
    /// variable. The quantifier-bound `y` stays bound, so it is not free.
    #[test]
    fn test_let_elim_leaves_no_free_locals() {
        let mut context = Context::default();
        context.ensure_logic();
        let t = UntypedAst
            .parse_term_str(
                "(let ((a 1)) (forall ((y Int)) (let ((b (+ a y))) (! (= b b) :pattern (b)))))",
            )
            .unwrap()
            .type_check(&mut context)
            .unwrap()
            .let_elim(&mut context);
        assert!(
            t.free_loc_vars().is_empty(),
            "{t} still has free local variables"
        );
    }

    /// A `let` inside one match arm is eliminated while the untouched arms stay shared.
    ///
    /// This pins down that rebuilt arms keep their own patterns: mispairing arms with patterns
    /// would still produce a well-sorted term, just the wrong one.
    #[test]
    fn test_let_elim_under_match() {
        let mut context = Context::default();
        UntypedAst
            .parse_script_str(
                "(set-logic ALL)
                 (declare-datatypes ((Color 0)) (((red) (green) (blue))))
                 (declare-const c Color)",
            )
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        let t = UntypedAst
            .parse_term_str("(match c ((red (let ((x 1)) (+ x 0))) (green 2) (blue 3)))")
            .unwrap()
            .type_check(&mut context)
            .unwrap()
            .let_elim(&mut context);
        let equiv = UntypedAst
            .parse_term_str("(match c ((red (+ 1 0)) (green 2) (blue 3)))")
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        assert_eq!(t, equiv);
    }

    /// A `let` inside a quantifier body must still be eliminated, and the quantifier rebuilt.
    ///
    /// Compared up to alpha equivalence, since each `type_check` mints a fresh id for `y`.
    #[test]
    fn test_let_elim_under_quantifier() {
        let mut context = Context::default();
        context.ensure_logic();
        let t = UntypedAst
            .parse_term_str("(forall ((y Int)) (let ((x (+ y 1))) (= x x)))")
            .unwrap()
            .type_check(&mut context)
            .unwrap()
            .let_elim(&mut context);
        let equiv = UntypedAst
            .parse_term_str("(forall ((y Int)) (= (+ y 1) (+ y 1)))")
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        assert!(t.aeq(&equiv), "{t} is not alpha-equivalent to {equiv}");
    }
}
