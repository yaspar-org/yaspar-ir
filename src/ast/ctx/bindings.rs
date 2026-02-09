// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::allocator::TermAllocator;
use crate::ast::alg::VarBinding;
use crate::ast::ctx::local::LocalContext;
use crate::ast::ctx::{Arena, Context, FetchSort, Result, TCEnv, TypedApi};
use crate::ast::ctx::{Sort, Str, Term};
use crate::ast::{MatchContext, QuantifierContext, TC};
use crate::locenv::LocEnv;
use crate::raw::instance::HasArena;
use crate::traits::AllocatableString;

/// It's a builder context for building let-bindings
///
/// c.f. [TypedApi::build_let] and [LetContext::typed_let]
pub struct LetContext<'a, 'b> {
    // reuse LocalContext to reuse apis
    inner: LocalContext<'a, 'b>,
    bindings: Vec<VarBinding<Str, Term>>,
}

impl<'a, 'b> LetContext<'a, 'b> {
    pub(crate) fn new(context: &'a mut Context, tail: LocEnv<'b, Str, Sort>) -> Self {
        Self {
            inner: LocalContext::new(context, tail),
            bindings: vec![],
        }
    }

    pub(crate) fn new_with_bindings<T, S>(
        context: &'a mut Context,
        tail: LocEnv<'b, Str, Sort>,
        tups: T,
    ) -> Result<Self>
    where
        T: IntoIterator<Item = (S, Term)>,
        S: AllocatableString<Arena>,
    {
        let mut ctx = Self::new(context, tail);
        ctx.extend_many(tups)?;
        Ok(ctx)
    }

    /// This function is intended to be private to ensure well-scopedness
    fn extend_many<T, S>(&mut self, tups: T) -> Result<&mut Self>
    where
        T: IntoIterator<Item = (S, Term)>,
        S: AllocatableString<Arena>,
    {
        let mut names = vec![];
        let mut terms = vec![];
        let mut sorts = vec![];
        for (name, term) in tups {
            let name = name.allocate(self.arena());
            names.push(name);
            let s = term.get_sort(self);
            sorts.push(s);
            terms.push(term);
        }
        let ids = self
            .inner
            .extend_many(names.clone().into_iter().zip(sorts))?;
        for (name, (id, term)) in names.into_iter().zip(ids.into_iter().zip(terms)) {
            self.bindings.push(VarBinding(name, id, term));
        }
        Ok(self)
    }

    /// Consume the given context and produce a term of a let binding
    pub fn typed_let(mut self, body: Term) -> Term {
        self.inner.let_term(self.bindings, body)
    }
}

impl HasArena for LetContext<'_, '_> {
    #[inline]
    fn arena(&mut self) -> &mut Arena {
        self.inner.arena()
    }
}

impl TypedApi for LetContext<'_, '_> {
    #[inline]
    fn get_tcenv(&mut self) -> TCEnv<'_, '_, Sort> {
        self.inner.get_tcenv()
    }

    #[inline]
    fn build_quantifier(&mut self) -> TC<QuantifierContext<'_, '_>> {
        self.inner.build_quantifier()
    }

    fn build_let<T, S>(&mut self, bindings: T) -> TC<LetContext<'_, '_>>
    where
        T: IntoIterator<Item = (S, Term)>,
        S: AllocatableString<Arena>,
    {
        self.inner.build_let(bindings)
    }

    fn build_matching(&mut self, scrutinee: Term) -> TC<MatchContext<'_, '_>> {
        self.inner.build_matching(scrutinee)
    }
}
