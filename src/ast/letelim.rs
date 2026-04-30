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

use super::boilerplates::TypedBuilder;
use crate::allocator::TermAllocator;
use crate::ast::Sort;
use crate::ast::{
    Attribute, Constant, HasArena, Local, Memoize, PatternArm, QualifiedIdentifier, Str, Term,
    TermRecursor, TypedTermRecursor,
};
use crate::containers::Mapping;
use crate::raw::alg::VarBinding;
use crate::raw::alg::rec::Bottom;
use delegate::delegate;
use std::collections::HashMap;
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
    inner: TypedBuilder<'a, E>,
    /// Environment stack: each frame maps a local variable id to the substituted term.
    /// Quantifier/match-bound variables are represented by frames with no entry
    /// (their locals simply won't be found, so they pass through unchanged).
    env: Vec<HashMap<usize, Option<Term>>>,
}

/// Memoized, stack-safe let-eliminator. Use [`LetEliminator::create`] to construct.
pub type LetEliminator<'a, E> = Memoize<LetEliminatorInner<'a, E>, HashMap<Term, Term>>;

impl<'a, E> LetEliminatorInner<'a, E>
where
    E: HasArena,
{
    pub fn new(arena: &'a mut E) -> Self {
        Self {
            inner: TypedBuilder::new(arena),
            env: Vec::new(),
        }
    }

    /// Search the environment stack for a variable by id.
    ///
    /// Returns `Some(Some(term))` for let-bound variables (substitute with `term`),
    /// `Some(None)` for quantifier/match-bound variables (do not substitute),
    /// or `None` if the variable is not in any scope.
    fn lookup(&self, id: usize) -> Option<Option<Term>> {
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

impl<E: HasArena> TermRecursor<Str, Sort, Term> for LetEliminatorInner<'_, E> {
    type Out = Term;
    type Attr = Attribute;
    type Binding = Term;
    type Pattern = (); // match-bound vars use empty frames, no substitution
    type Arm = PatternArm;
    type Err = Bottom;

    delegate! {
        to self.inner {
            fn on_constant(&mut self, current: &Term, constant: &Constant, sort: &Option<Sort>) -> Result<Term, Bottom>;
            fn on_global(&mut self, current: &Term, id: &QualifiedIdentifier, sort: &Option<Sort>) -> Result<Term, Bottom>;
            fn on_app(&mut self, current: &Term, id: &QualifiedIdentifier, ts: &[Term], s: &Option<Sort>, recs: Vec<Self::Out>) -> Result<Term, Bottom>;
            fn on_match(&mut self, current: &Term, scrutinee: &Term, cases: &[PatternArm], scrutinee_rec: Self::Out, cases_rec: Vec<Self::Arm>) -> Result<Term, Bottom>;
            fn on_annotated(&mut self, current: &Term, t: &Term, anns: &[Attribute], t_rec: Term, anns_rec: Vec<Attribute>) -> Result<Term, Bottom>;
            fn on_attribute_keyword(&mut self, keyword: &Keyword) -> Result<Attribute, Bottom>;
            fn on_attribute_constant(&mut self, keyword: &Keyword, constant: &Constant) -> Result<Attribute, Bottom>;
            fn on_attribute_symbol(&mut self, keyword: &Keyword, symbol: &Str) -> Result<Attribute, Bottom>;
            fn on_attribute_named(&mut self, name: &Str) -> Result<Attribute, Bottom>;
            fn on_attribute_pattern(&mut self, patterns: &[Term], patterns_rec: Vec<Term>) -> Result<Attribute, Bottom>;
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

    /// Look up the local variable in the environment. If it is let-bound (`Some(Some(t))`),
    /// return the substituted term. Otherwise (quantifier/match-bound or not found), keep as-is.
    fn on_local(&mut self, current: &Term, id: &Local) -> Result<Term, Bottom> {
        Ok(match self.lookup(id.id) {
            Some(Some(t)) => t,
            _ => current.clone(),
        })
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
            .map(|(v, r)| (v.1, Some(r.clone())))
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
        self.env.push(vs.iter().map(|v| (v.1, None)).collect());
        Ok(())
    }

    fn on_exists(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Sort>],
        _: &Term,
        body: Term,
    ) -> Result<Term, Bottom> {
        self.env.pop();
        Ok(self.inner.arena().exists(vs.to_vec(), body))
    }

    fn on_forall(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Sort>],
        _: &Term,
        body: Term,
    ) -> Result<Term, Bottom> {
        self.env.pop();
        Ok(self.inner.arena().forall(vs.to_vec(), body))
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
                .map(|(_, id)| (id, None))
                .collect(),
        );
        Ok(())
    }

    fn on_match_arm(
        &mut self,
        _: &Term,
        _: &Term,
        cases: &[PatternArm],
        _scrutinee_rec: &Term,
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
