// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Free variable computation for terms.
//!
//! This module provides the [`FreeLocalVars`] trait, which computes the set of free (unbound)
//! local variables in a term. A variable is free if it is not bound by any enclosing `let`,
//! `forall`, `exists`, or `match` binder.
//!
//! Use [`is_closed`] as a convenience check for whether a term has
//! no free local variables.

use crate::ast::alg::VarBinding;
use crate::ast::{Attribute, Constant, PatternArm, QualifiedIdentifier};
use crate::ast::{Bottom, Local, Sort, Str, Term, TermRecursor, TypedTermRecursor};
use std::collections::HashSet;
use yaspar::ast::Keyword;

/// Compute the set of free local variables in a term.
///
/// A local variable is free if it is not bound by any enclosing binder (`let`, `forall`,
/// `exists`, or `match` pattern).
pub trait FreeLocalVars {
    fn free_loc_vars(&self) -> HashSet<(Str, usize)>;
}

impl FreeLocalVars for Term {
    fn free_loc_vars(&self) -> HashSet<(Str, usize)> {
        let mut finder = FreeLocalVariableFinder::default();
        match finder.recurse_on_term(self) {
            Ok(_) => finder.vars,
            Err(b) => match b {},
        }
    }
}

#[derive(Default)]
struct FreeLocalVariableFinder {
    vars: HashSet<(Str, usize)>,
}

impl FreeLocalVariableFinder {
    fn remove_bindings<T, F>(&mut self, bindings: impl Iterator<Item = T>, f: F)
    where
        F: Fn(T) -> (Str, usize),
    {
        for b in bindings {
            let loc = f(b);
            self.vars.remove(&loc);
        }
    }
}

impl TermRecursor<Str, Sort, Term> for FreeLocalVariableFinder {
    type Out = ();
    type Attr = ();
    type Binding = ();
    type Pattern = ();
    type Arm = ();
    type Err = Bottom;

    fn on_constant(
        &mut self,
        _current: &Term,
        _constant: &Constant,
        _sort: &Option<Sort>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(())
    }

    fn on_global(
        &mut self,
        _current: &Term,
        _id: &QualifiedIdentifier,
        _sort: &Option<Sort>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(())
    }

    fn on_local(&mut self, _current: &Term, id: &Local) -> Result<Self::Out, Self::Err> {
        self.vars.insert((id.symbol.clone(), id.id));
        Ok(())
    }

    fn on_app(
        &mut self,
        _current: &Term,
        _id: &QualifiedIdentifier,
        _ts: &[Term],
        _s: &Option<Sort>,
        _recs: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(())
    }

    fn on_let_binding(
        &mut self,
        _current: &Term,
        _vs: &[VarBinding<Str, Term>],
        _body: &Term,
        _binding_idx: usize,
        _binding_rec: Self::Out,
    ) -> Result<Self::Binding, Self::Err> {
        Ok(())
    }

    fn setup_let_scope(
        &mut self,
        _current: &Term,
        _vs: &[VarBinding<Str, Term>],
        _body: &Term,
        _vs_rec: &[Self::Binding],
    ) -> Result<(), Self::Err> {
        Ok(())
    }

    fn on_let(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Term>],
        _body: &Term,
        _vs_rec: Vec<Self::Binding>,
        _body_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        self.remove_bindings(vs.iter(), |v| (v.0.clone(), v.1));
        Ok(())
    }

    fn setup_quantifier_scope(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Sort>],
        _t: &Term,
        _is_forall: bool,
    ) -> Result<(), Self::Err> {
        self.remove_bindings(vs.iter(), |v| (v.0.clone(), v.1));
        Ok(())
    }

    fn on_exists(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Sort>],
        _t: &Term,
        _t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        self.remove_bindings(vs.iter(), |v| (v.0.clone(), v.1));
        Ok(())
    }

    fn on_forall(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Sort>],
        _t: &Term,
        _t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        self.remove_bindings(vs.iter(), |v| (v.0.clone(), v.1));
        Ok(())
    }

    fn setup_match_case_scope(
        &mut self,
        _current: &Term,
        _scrutinee: &Term,
        _cases: &[PatternArm],
        _scrutinee_rec: &Self::Out,
        _case_idx: usize,
    ) -> Result<Self::Pattern, Self::Err> {
        Ok(())
    }

    fn on_match_arm(
        &mut self,
        _current: &Term,
        _scrutinee: &Term,
        cases: &[PatternArm],
        _scrutinee_rec: &Self::Out,
        case_idx: usize,
        _current_pattern: Self::Pattern,
        _arm: Self::Out,
    ) -> Result<Self::Arm, Self::Err> {
        self.remove_bindings(
            cases[case_idx].pattern.variables_and_ids().into_iter(),
            |v| v.clone(),
        );

        Ok(())
    }

    fn on_match(
        &mut self,
        _current: &Term,
        _scrutinee: &Term,
        _cases: &[PatternArm],
        _scrutinee_rec: Self::Out,
        _cases_rec: Vec<Self::Arm>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(())
    }

    fn on_annotated(
        &mut self,
        _current: &Term,
        _t: &Term,
        _anns: &[Attribute],
        _t_rec: Self::Out,
        _anns_rec: Vec<Self::Attr>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(())
    }

    fn on_attribute_keyword(&mut self, _keyword: &Keyword) -> Result<Self::Attr, Self::Err> {
        Ok(())
    }

    fn on_attribute_constant(
        &mut self,
        _keyword: &Keyword,
        _constant: &Constant,
    ) -> Result<Self::Attr, Self::Err> {
        Ok(())
    }

    fn on_attribute_symbol(
        &mut self,
        _keyword: &Keyword,
        _symbol: &Str,
    ) -> Result<Self::Attr, Self::Err> {
        Ok(())
    }

    fn on_attribute_named(&mut self, _name: &Str) -> Result<Self::Attr, Self::Err> {
        Ok(())
    }

    fn on_attribute_pattern(
        &mut self,
        _patterns: &[Term],
        _patterns_rec: Vec<Self::Out>,
    ) -> Result<Self::Attr, Self::Err> {
        Ok(())
    }

    fn on_eq(
        &mut self,
        _current: &Term,
        _a: &Term,
        _b: &Term,
        _a_rec: Self::Out,
        _b_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        Ok(())
    }

    fn on_distinct(
        &mut self,
        _current: &Term,
        _ts: &[Term],
        _ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(())
    }

    fn on_and(
        &mut self,
        _current: &Term,
        _ts: &[Term],
        _ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(())
    }

    fn on_or(
        &mut self,
        _current: &Term,
        _ts: &[Term],
        _ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(())
    }

    fn on_xor(
        &mut self,
        _current: &Term,
        _ts: &[Term],
        _ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(())
    }

    fn on_not(
        &mut self,
        _current: &Term,
        _t: &Term,
        _t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        Ok(())
    }

    fn on_implies(
        &mut self,
        _current: &Term,
        _ts: &[Term],
        _t: &Term,
        _ts_rec: Vec<Self::Out>,
        _t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        Ok(())
    }

    fn on_ite(
        &mut self,
        _current: &Term,
        _b: &Term,
        _t: &Term,
        _e: &Term,
        _b_rec: Self::Out,
        _t_rec: Self::Out,
        _e_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        Ok(())
    }
}

impl TypedTermRecursor for FreeLocalVariableFinder {}

/// check whether a term is closed; i.e. no open local variables
pub fn is_closed(t: &Term) -> bool {
    t.free_loc_vars().is_empty()
}
