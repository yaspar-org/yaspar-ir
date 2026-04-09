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
//! Note: let-elimination may increase term size due to duplication of shared sub-terms. For the
//! inverse operation (re-introducing let-bindings to share common sub-terms), see
//! [`crate::ast::letintro`].

use crate::allocator::TermAllocator;
use crate::containers::Mapping;
use crate::raw::alg::VarBinding;
use crate::raw::instance::{Attribute, PatternArm, Str, Term};
use std::collections::HashMap;

use crate::ast::Sort;
use crate::ast::{HasArena, Memoize, TermRecursor, TypedTermRecursor};
use crate::raw::alg::rec::Bottom;
use crate::raw::alg::{Constant, Local, QualifiedIdentifier};
use yaspar::ast::Keyword;

/// Eliminates all let-bindings by applying substitutions properly
///
/// This trait assumes that the given object has been type-checked.
pub trait LetElim<Env> {
    fn let_elim(&self, env: &mut Env) -> Self;
}

/// Stack-safe let-elimination using [`TermRecursor`].
///
/// It can be wrapped with [`Memoize`] for caching.
pub struct LetEliminatorInner<'a, E> {
    arena: &'a mut E,
    /// Environment stack: each frame maps `(name, id)` to the substituted term.
    /// Quantifier/match-bound variables are represented by frames with no entry
    /// (their locals simply won't be found, so they pass through unchanged).
    env: Vec<HashMap<(Str, usize), Option<Term>>>,
}

/// Memoized, stack-safe let-eliminator. Use [`LetEliminator::create`] to construct.
pub type LetEliminator<'a, E> = Memoize<LetEliminatorInner<'a, E>, HashMap<Term, Term>>;

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

    /// Search the environment stack for a variable by `(name, id)`.
    ///
    /// Returns `Some(Some(term))` for let-bound variables (substitute with `term`),
    /// `Some(None)` for quantifier/match-bound variables (do not substitute),
    /// or `None` if the variable is not in any scope.
    fn lookup(&self, name: &Str, id: usize) -> Option<Option<Term>> {
        let key = (name.clone(), id);
        self.env.lookup(&key)
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

impl<E: HasArena> TermRecursor<Str, Sort, Term> for LetEliminatorInner<'_, E> {
    type Out = Term;
    type Attr = Attribute;
    type Binding = Term;
    type Pattern = (); // match-bound vars use empty frames, no substitution
    type Arm = PatternArm;
    type Err = Bottom;

    // --- Leaves ---

    fn on_constant(
        &mut self,
        current: &Term,
        _: &Constant<Str>,
        _: &Option<Sort>,
    ) -> Result<Term, Bottom> {
        Ok(current.clone())
    }

    fn on_global(
        &mut self,
        current: &Term,
        _: &QualifiedIdentifier<Str, Sort>,
        _: &Option<Sort>,
    ) -> Result<Term, Bottom> {
        Ok(current.clone())
    }

    /// Look up the local variable in the environment. If it is let-bound (`Some(Some(t))`),
    /// return the substituted term. Otherwise (quantifier/match-bound or not found), keep as-is.
    fn on_local(&mut self, current: &Term, id: &Local<Str, Sort>) -> Result<Term, Bottom> {
        Ok(match self.lookup(id.id_str(), id.id) {
            Some(Some(t)) => t,
            _ => current.clone(),
        })
    }

    // --- Compound ---

    fn on_app(
        &mut self,
        _: &Term,
        id: &QualifiedIdentifier<Str, Sort>,
        _: &[Term],
        s: &Option<Sort>,
        recs: Vec<Term>,
    ) -> Result<Term, Bottom> {
        Ok(self.arena.arena().app(id.clone(), recs, s.clone()))
    }

    fn on_eq(&mut self, _: &Term, _: &Term, _: &Term, a: Term, b: Term) -> Result<Term, Bottom> {
        Ok(self.arena.arena().eq(a, b))
    }

    fn on_distinct(&mut self, _: &Term, _: &[Term], recs: Vec<Term>) -> Result<Term, Bottom> {
        Ok(self.arena.arena().distinct(recs))
    }

    fn on_and(&mut self, _: &Term, _: &[Term], recs: Vec<Term>) -> Result<Term, Bottom> {
        Ok(self.arena.arena().and(recs))
    }

    fn on_or(&mut self, _: &Term, _: &[Term], recs: Vec<Term>) -> Result<Term, Bottom> {
        Ok(self.arena.arena().or(recs))
    }

    fn on_xor(&mut self, _: &Term, _: &[Term], recs: Vec<Term>) -> Result<Term, Bottom> {
        Ok(self.arena.arena().xor(recs))
    }

    fn on_not(&mut self, _: &Term, _: &Term, r: Term) -> Result<Term, Bottom> {
        Ok(self.arena.arena().not(r))
    }

    fn on_implies(
        &mut self,
        _: &Term,
        _: &[Term],
        _: &Term,
        ps: Vec<Term>,
        c: Term,
    ) -> Result<Term, Bottom> {
        Ok(self.arena.arena().implies(ps, c))
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
        Ok(self.arena.arena().ite(b, t, e))
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

    /// Push a new scope frame mapping each let-bound variable to its recursed RHS.
    fn setup_let_scope(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Term>],
        _: &Term,
        vs_rec: &[Term],
    ) -> Result<(), Bottom> {
        let frame = vs
            .iter()
            .zip(vs_rec.iter())
            .map(|(v, r)| ((v.0.clone(), v.1), Some(r.clone())))
            .collect();
        self.env.push(frame);
        Ok(())
    }

    /// Pop the let scope and return the body directly — the let-binding is eliminated.
    fn on_let(
        &mut self,
        _: &Term,
        _: &[VarBinding<Str, Term>],
        _: &Term,
        _: Vec<Term>,
        body: Term,
    ) -> Result<Term, Bottom> {
        self.env.pop();
        Ok(body)
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
        self.env
            .push(vs.iter().map(|v| ((v.0.clone(), v.1), None)).collect());
        Ok(())
    }

    fn on_forall(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Sort>],
        _: &Term,
        body: Term,
    ) -> Result<Term, Bottom> {
        self.env.pop();
        Ok(self.arena.arena().forall(vs.to_vec(), body))
    }

    fn on_exists(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Sort>],
        _: &Term,
        body: Term,
    ) -> Result<Term, Bottom> {
        self.env.pop();
        Ok(self.arena.arena().exists(vs.to_vec(), body))
    }

    // --- Match ---

    /// Push a scope frame with `None` values for pattern-bound variables, similar to quantifiers.
    fn setup_match_case_scope(
        &mut self,
        _: &Term,
        _: &Term,
        cases: &[PatternArm],
        _: &Term,
        idx: usize,
    ) -> Result<(), Bottom> {
        self.env.push(
            cases[idx]
                .pattern
                .variables_and_ids()
                .into_iter()
                .map(|tup| (tup, None))
                .collect(),
        );
        Ok(())
    }

    fn on_match_arm(
        &mut self,
        _: &Term,
        _: &Term,
        cases: &[PatternArm],
        idx: usize,
        _: (),
        body: Term,
    ) -> Result<PatternArm, Bottom> {
        self.env.pop();
        Ok(PatternArm {
            pattern: cases[idx].pattern.clone(),
            body,
        })
    }

    fn on_match(
        &mut self,
        _: &Term,
        _: &Term,
        _: &[PatternArm],
        scrutinee: Term,
        arms: Vec<PatternArm>,
    ) -> Result<Term, Bottom> {
        Ok(self.arena.arena().matching(scrutinee, arms))
    }

    // --- Annotated ---

    fn on_annotated(
        &mut self,
        _: &Term,
        _: &Term,
        _: &[Attribute],
        r: Term,
        anns: Vec<Attribute>,
    ) -> Result<Term, Bottom> {
        Ok(self.arena.arena().annotated(r, anns))
    }

    fn on_attribute_keyword(&mut self, kw: &Keyword) -> Result<Attribute, Bottom> {
        Ok(Attribute::Keyword(kw.clone()))
    }

    fn on_attribute_constant(
        &mut self,
        kw: &Keyword,
        c: &Constant<Str>,
    ) -> Result<Attribute, Bottom> {
        Ok(Attribute::Constant(kw.clone(), c.clone()))
    }

    fn on_attribute_symbol(&mut self, kw: &Keyword, s: &Str) -> Result<Attribute, Bottom> {
        Ok(Attribute::Symbol(kw.clone(), s.clone()))
    }

    fn on_attribute_named(&mut self, name: &Str) -> Result<Attribute, Bottom> {
        Ok(Attribute::Named(name.clone()))
    }

    fn on_attribute_pattern(&mut self, _: &[Term], recs: Vec<Term>) -> Result<Attribute, Bottom> {
        Ok(Attribute::Pattern(recs))
    }
}

impl<E: HasArena> TypedTermRecursor for LetEliminatorInner<'_, E> {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Context, Typecheck};
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
}
