// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Monomorphization of parametric datatypes.
//!
//! This module provides functionality to instantiate parametric datatypes with concrete sorts,
//! eliminating sort variables by substituting them with ground types.

use crate::ast::alg::VarBinding;
use crate::ast::{ConstructorDec, DatatypeDec, HasArenaAlt, Sort, TC};
use crate::raw::tc::unif::{SortSubst, apply_subst};

/// Trait for monomorphizing parametric types by substituting sort variables with concrete sorts.
pub trait Monomorphization<E, I> {
    type Output;

    /// Monomorphize `self` using the provided input and environment.
    fn monomorphize(&self, input: &I, env: &mut E) -> Self::Output;
}

/// Apply a sort substitution to a sort, replacing sort variables with their concrete instantiations.
impl<E> Monomorphization<E, SortSubst> for Sort
where
    E: HasArenaAlt,
{
    type Output = Self;
    fn monomorphize(&self, input: &SortSubst, env: &mut E) -> Self {
        apply_subst(env, input, self)
    }
}

/// Monomorphize a variable binding by applying the substitution to its sort.
impl<E, S> Monomorphization<E, SortSubst> for VarBinding<S, Sort>
where
    E: HasArenaAlt,
    S: Clone,
{
    type Output = Self;
    fn monomorphize(&self, input: &SortSubst, env: &mut E) -> Self {
        Self(self.0.clone(), self.1, self.2.monomorphize(input, env))
    }
}

/// Monomorphize a constructor declaration by applying the substitution to all argument sorts.
impl<E> Monomorphization<E, SortSubst> for ConstructorDec
where
    E: HasArenaAlt,
{
    type Output = Self;
    fn monomorphize(&self, input: &SortSubst, env: &mut E) -> Self {
        Self {
            ctor: self.ctor.clone(),
            args: self
                .args
                .iter()
                .map(|b| b.monomorphize(input, env))
                .collect(),
        }
    }
}

/// Monomorphize a datatype declaration by instantiating its sort parameters with concrete sorts.
///
/// Given a parametric datatype and a concrete sort instantiation, this creates a new datatype
/// with no parameters where all occurrences of sort variables are replaced with the provided sorts.
impl<E> Monomorphization<E, Sort> for DatatypeDec
where
    E: HasArenaAlt,
{
    type Output = TC<DatatypeDec>;

    fn monomorphize(&self, input: &Sort, env: &mut E) -> Self::Output {
        if self.params.len() != input.1.len() {
            return Err(format!(
                "Sort {input} has {} sub-sorts, but {} are required!",
                input.1.len(),
                self.params.len()
            ));
        }

        let subst: SortSubst = self
            .params
            .iter()
            .zip(input.1.iter())
            .map(|(a, b)| (a.clone(), Some(b.clone())))
            .collect();

        Ok(DatatypeDec {
            params: vec![],
            constructors: self
                .constructors
                .iter()
                .map(|ctor| ctor.monomorphize(&subst, env))
                .collect(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::allocator::{ObjectAllocatorExt, SortAllocator, StrAllocator};
    use crate::ast::{ASortDef, Context, Typecheck};
    use crate::untyped::UntypedAst;

    #[test]
    fn test_sort_monomorphize() {
        let mut ctx = Context::new();
        ctx.ensure_logic();

        UntypedAst
            .parse_command_str(
                "(declare-datatype List (par (X) ((nil) (cons (car X) (cdr (List X))))))",
            )
            .unwrap()
            .type_check(&mut ctx)
            .unwrap();

        let int = ctx.int_sort();
        let list_sym = ctx.allocate_symbol("List");
        let list_int = ctx.sort_n(list_sym.clone(), vec![int]);
        let dt = match ctx.get_sort_def(&list_sym).unwrap() {
            ASortDef::Datatype(d) => d.clone(),
            _ => panic!("Expected datatype"),
        };
        let mono_dt = dt.monomorphize(&list_int, &mut ctx).unwrap();

        for ctor in &mono_dt.constructors {
            for arg in &ctor.args {
                // TC makes sure no open sort variable.
                arg.2.type_check(&mut ctx).unwrap();
            }
        }
    }

    #[test]
    fn test_constructor_monomorphize() {
        let mut ctx = Context::new();
        ctx.ensure_logic();

        UntypedAst
            .parse_command_str("(declare-datatype Pair (par (A B) ((mk-pair (fst A) (snd B)))))")
            .unwrap()
            .type_check(&mut ctx)
            .unwrap();

        let int = ctx.int_sort();
        let bool = ctx.bool_sort();
        let pair_sym = ctx.allocate_symbol("Pair");
        let pair = ctx.sort_n(pair_sym.clone(), vec![int, bool]);
        let dt = match ctx.get_sort_def(&pair_sym).unwrap() {
            ASortDef::Datatype(d) => d.clone(),
            _ => panic!("Expected datatype"),
        };
        let mono_dt = dt.monomorphize(&pair, &mut ctx).unwrap();

        for ctor in &mono_dt.constructors {
            for arg in &ctor.args {
                // TC makes sure no open sort variable.
                arg.2.type_check(&mut ctx).unwrap();
            }
        }
    }
}
