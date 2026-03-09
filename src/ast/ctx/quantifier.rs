// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::allocator::TermAllocator;
use crate::ast::ctx::bindings::LetContext;
use crate::ast::ctx::local::LocalContext;
use crate::ast::ctx::{Arena, CheckedApi, Context, Result, Sort, Str, TCEnv, Term};
use crate::ast::utils::is_term_bool;
use crate::ast::{MatchContext, Theory};
use crate::locenv::LocEnv;
use crate::raw::instance::HasArena;
use crate::raw::tc::TC;
use crate::traits::AllocatableString;

/// A builder context for constructing quantified terms (`forall` and `exists`).
///
/// Created via [`CheckedApi::build_quantifier`] or [`CheckedApi::build_quantifier_with_domain`].
/// Variables are introduced into scope either at creation time (with `build_quantifier_with_domain`)
/// or incrementally via [`extend`](Self::extend) / [`extend_many`](Self::extend_many).
///
/// Once the body is built, finalize with [`typed_forall`](Self::typed_forall) or
/// [`typed_exists`](Self::typed_exists), both of which consume the context and return the
/// quantified term. The body must be `Bool`-sorted.
///
/// This context implements [`CheckedApi`], so all term-building methods are available inside it,
/// and nested builder contexts (let-bindings, inner quantifiers, match expressions) can be created.
///
/// # Example
///
/// ```rust
/// use yaspar_ir::ast::{CheckedApi, Context, ScopedSortApi};
///
/// let mut context = Context::new();
/// context.ensure_logic();
/// let int = context.wf_sort("Int").unwrap();
/// let mut q = context.build_quantifier_with_domain([("x", int)]).unwrap();
/// let x = q.typed_symbol("x").unwrap();
/// let zero = q.numeral(0u8.into()).unwrap();
/// let body = q.typed_simp_app(">", [x, zero]).unwrap();
/// let term = q.typed_forall(body).unwrap();
/// assert_eq!(term.to_string(), "(forall ((x Int)) (> x 0))");
/// ```
pub struct QuantifierContext<'a, 'b>(pub(crate) LocalContext<'a, 'b>);

impl<'a, 'b> QuantifierContext<'a, 'b> {
    pub(crate) fn new(context: &'a mut Context, tail: LocEnv<'b, Str, Sort>) -> TC<Self> {
        context.check_support_theory(Theory::Quantifiers)?;
        Ok(Self(LocalContext::new(context, tail)))
    }

    /// Extends a name-sort binding to the local environment
    pub fn extend<S>(&mut self, name: S, sort: Sort) -> Result<&mut Self>
    where
        S: AllocatableString<Arena>,
    {
        self.0.extend(name, sort)?;
        Ok(self)
    }

    /// Extends a vector of name-osrt bindings
    pub fn extend_many<T, S>(&mut self, tups: T) -> Result<&mut Self>
    where
        T: IntoIterator<Item = (S, Sort)>,
        S: AllocatableString<Arena>,
    {
        self.0.extend_many(tups)?;
        Ok(self)
    }

    /// Build a forall
    ///
    /// Body is a term built in `self` context
    pub fn typed_forall(mut self, body: Term) -> TC<Term> {
        is_term_bool(&mut self, &body)?;
        Ok(self.0.context.forall(self.0.env, body))
    }

    /// Build an exists
    ///
    /// Body is a term built in `self` context
    pub fn typed_exists(mut self, body: Term) -> TC<Term> {
        is_term_bool(&mut self, &body)?;
        Ok(self.0.context.exists(self.0.env, body))
    }
}

impl HasArena for QuantifierContext<'_, '_> {
    #[inline]
    fn arena(&mut self) -> &mut Arena {
        self.0.arena()
    }
}

impl CheckedApi for QuantifierContext<'_, '_> {
    fn get_tcenv(&mut self) -> TCEnv<'_, '_, Sort> {
        self.0.get_tcenv()
    }

    fn build_quantifier(&mut self) -> TC<QuantifierContext<'_, '_>> {
        self.0.build_quantifier()
    }

    fn build_let<T, S>(&mut self, bindings: T) -> TC<LetContext<'_, '_>>
    where
        T: IntoIterator<Item = (S, Term)>,
        S: AllocatableString<Arena>,
    {
        self.0.build_let(bindings)
    }

    fn build_matching(&mut self, scrutinee: Term) -> TC<MatchContext<'_, '_>> {
        self.0.build_matching(scrutinee)
    }
}
