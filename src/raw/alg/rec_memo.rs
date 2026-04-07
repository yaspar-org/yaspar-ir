// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use super::rec::*;
use crate::ast::alg::{
    Attribute, Constant, Local, PatternArm, QualifiedIdentifier, Term, VarBinding,
};
use crate::containers::{InsertableMapping, Mapping};
use crate::traits::{Contains, Repr};
use either::Either;
use yaspar::ast::Keyword;

pub struct Memoize<R, M> {
    inner: R,
    cache: M,
}

impl<Str, So, T, R, M> TermRecursor<Str, So, T> for Memoize<R, M>
where
    T: Clone,
    R: TermRecursor<Str, So, T, Out: Clone>,
    M: InsertableMapping<Key = T, Value = R::Out>,
{
    type Out = R::Out;
    type Attr = R::Attr;
    type Binding = R::Binding;
    type Pattern = R::Pattern;
    type Arm = R::Arm;
    type Err = R::Err;

    fn recurse_on_term(&mut self, t: &T) -> Result<Self::Out, Self::Err>
    where
        Self: Sized,
        T: Contains<T: Repr<T = Term<Str, So, T>>>,
    {
        memo_term_recursion(self, t)
    }

    fn on_constant(
        &mut self,
        current: &T,
        constant: &Constant<Str>,
        sort: &Option<So>,
    ) -> Result<Self::Out, Self::Err> {
        let r = self.inner.on_constant(current, constant, sort)?;
        self.cache.insert(current.clone(), r.clone());
        Ok(r)
    }

    fn on_global(
        &mut self,
        current: &T,
        id: &QualifiedIdentifier<Str, So>,
        sort: &Option<So>,
    ) -> Result<Self::Out, Self::Err> {
        todo!()
    }

    fn on_local(&mut self, current: &T, id: &Local<Str, So>) -> Result<Self::Out, Self::Err> {
        todo!()
    }

    fn on_app(
        &mut self,
        current: &T,
        id: &QualifiedIdentifier<Str, So>,
        ts: &[T],
        s: &Option<So>,
        recs: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        todo!()
    }

    fn on_let_binding(
        &mut self,
        current: &T,
        vs: &[VarBinding<Str, T>],
        body: &T,
        binding_idx: usize,
        binding_rec: Self::Out,
    ) -> Result<Self::Binding, Self::Err> {
        todo!()
    }

    fn setup_let_scope(
        &mut self,
        current: &T,
        vs: &[VarBinding<Str, T>],
        body: &T,
        vs_rec: &[Self::Binding],
    ) -> Result<(), Self::Err> {
        todo!()
    }

    fn on_let(
        &mut self,
        current: &T,
        vs: &[VarBinding<Str, T>],
        body: &T,
        vs_rec: Vec<Self::Binding>,
        body_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        todo!()
    }

    fn setup_quantifier_scope(
        &mut self,
        current: &T,
        vs: &[VarBinding<Str, So>],
        t: &T,
        is_forall: bool,
    ) -> Result<(), Self::Err> {
        todo!()
    }

    fn on_exists(
        &mut self,
        current: &T,
        vs: &[VarBinding<Str, So>],
        t: &T,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        todo!()
    }

    fn on_forall(
        &mut self,
        current: &T,
        vs: &[VarBinding<Str, So>],
        t: &T,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        todo!()
    }

    fn setup_match_case_scope(
        &mut self,
        current: &T,
        scrutinee: &T,
        cases: &[PatternArm<Str, T>],
        scrutinee_rec: &Self::Out,
        case_idx: usize,
    ) -> Result<Self::Pattern, Self::Err> {
        todo!()
    }

    fn on_match_arm(
        &mut self,
        current: &T,
        scrutinee: &T,
        cases: &[PatternArm<Str, T>],
        case_idx: usize,
        current_pattern: Self::Pattern,
        arm: Self::Out,
    ) -> Result<Self::Arm, Self::Err> {
        todo!()
    }

    fn on_match(
        &mut self,
        current: &T,
        scrutinee: &T,
        cases: &[PatternArm<Str, T>],
        scrutinee_rec: Self::Out,
        cases_rec: Vec<Self::Arm>,
    ) -> Result<Self::Out, Self::Err> {
        todo!()
    }

    fn on_annotated(
        &mut self,
        current: &T,
        t: &T,
        anns: &[Attribute<Str, T>],
        t_rec: Self::Out,
        anns_rec: Vec<Self::Attr>,
    ) -> Result<Self::Out, Self::Err> {
        todo!()
    }

    fn on_attribute_keyword(
        &mut self,
        current: &T,
        keyword: &Keyword,
    ) -> Result<Self::Attr, Self::Err> {
        todo!()
    }

    fn on_attribute_constant(
        &mut self,
        current: &T,
        keyword: &Keyword,
        constant: &Constant<Str>,
    ) -> Result<Self::Attr, Self::Err> {
        todo!()
    }

    fn on_attribute_symbol(
        &mut self,
        current: &T,
        keyword: &Keyword,
        symbol: &Str,
    ) -> Result<Self::Attr, Self::Err> {
        todo!()
    }

    fn on_attribute_named(&mut self, current: &T, name: &Str) -> Result<Self::Attr, Self::Err> {
        todo!()
    }

    fn on_attribute_pattern(
        &mut self,
        current: &T,
        patterns: &[T],
        patterns_rec: Vec<Self::Out>,
    ) -> Result<Self::Attr, Self::Err> {
        todo!()
    }

    fn on_eq(
        &mut self,
        current: &T,
        a: &T,
        b: &T,
        a_rec: Self::Out,
        b_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        todo!()
    }

    fn on_distinct(
        &mut self,
        current: &T,
        ts: &[T],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        todo!()
    }

    fn on_and(
        &mut self,
        current: &T,
        ts: &[T],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        todo!()
    }

    fn on_or(
        &mut self,
        current: &T,
        ts: &[T],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        todo!()
    }

    fn on_xor(
        &mut self,
        current: &T,
        ts: &[T],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        todo!()
    }

    fn on_not(&mut self, current: &T, t: &T, t_rec: Self::Out) -> Result<Self::Out, Self::Err> {
        todo!()
    }

    fn on_implies(
        &mut self,
        current: &T,
        ts: &[T],
        t: &T,
        ts_rec: Vec<Self::Out>,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        todo!()
    }

    fn on_ite(
        &mut self,
        current: &T,
        b: &T,
        t: &T,
        e: &T,
        b_rec: Self::Out,
        t_rec: Self::Out,
        e_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        todo!()
    }
}

fn memo_expand_and_resolve<'a, R, M, Str: 'a, So: 'a, T>(
    recursor: &mut Memoize<R, M>,
    stack: &mut RStack<'a, Memoize<R, M>, Str, So, T>,
    mut current: &'a T,
) -> Result<R::Out, R::Err>
where
    R: TermRecursor<Str, So, T, Out: Clone>,
    M: InsertableMapping<Key = T, Value = R::Out>,
    T: Contains<T: Repr<T = Term<Str, So, T>>> + Clone,
{
    loop {
        if let Some(r) = recursor.cache.lookup(current) {
            return Ok(r);
        }

        match expand_and_resolve_once(recursor, stack, current)? {
            Either::Left(l) => {
                current = l;
            }
            Either::Right(r) => {
                return Ok(r);
            }
        }
    }
}

fn memo_term_recursion<R, M, Str, So, T>(
    recursor: &mut Memoize<R, M>,
    term: &T,
) -> Result<R::Out, R::Err>
where
    R: TermRecursor<Str, So, T, Out: Clone>,
    M: InsertableMapping<Key = T, Value = R::Out>,
    T: Contains<T: Repr<T = Term<Str, So, T>>> + Clone,
{
    let mut stack = vec![];
    let mut result = memo_expand_and_resolve(recursor, &mut stack, term)?;
    loop {
        match push_result(recursor, &mut stack, result)? {
            Either::Left(final_result) => return Ok(final_result),
            Either::Right(mut frame) => {
                let child = next_child(recursor, &mut frame)?;
                stack.push(frame);
                result = memo_expand_and_resolve(recursor, &mut stack, child)?;
            }
        }
    }
}
