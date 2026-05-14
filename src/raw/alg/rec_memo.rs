// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Memoized term recursion via [`Memoize`], a caching wrapper around [`TermRecursor`].
//!
//! When terms implement [Eq] and [Hash], structurally identical sub-terms share the same identity.
//! A plain [`TermRecursor`] traversal will re-visit such shared sub-terms every time they
//! appear. [`Memoize`] wraps any [`TermRecursor`] and caches the `Out` result for each
//! term node, so repeated encounters return the cached value immediately.
//!
//! # How it works
//!
//! [`Memoize`] holds an `inner` recursor and a `cache` mapping terms to results.
//!
//! - **On each `on_*` callback that produces `Out`**: the wrapper delegates to the inner
//!   recursor, inserts the result into the cache, and returns it.
//! - **On auxiliary callbacks** (`setup_*`, `on_let_binding`, `on_match_arm`,
//!   `on_attribute_*`): the wrapper delegates directly without caching.
//! - **During expansion** ([`memo_expand_and_resolve`]): before descending into a term,
//!   the cache is checked. On a hit the cached result is returned without expanding the
//!   node at all, short-circuiting the entire sub-tree.
//!
//! The cache type is generic (`M: `[`InsertableMapping`]), so callers can supply a
//! [`HashMap`], a pre-populated cache from a previous run, or any custom mapping.

use super::rec::*;
use crate::ast::alg::{
    Attribute, Constant, Local, PatternArm, QualifiedIdentifier, Term, VarBinding,
};
use crate::containers::{InsertableMapping, Mapping};
use crate::traits::{Contains, Repr};
use delegate::delegate;
use either::Either;
use std::collections::HashMap;
use std::ops::{Deref, DerefMut};
use yaspar::ast::Keyword;

/// A caching wrapper that memoizes the `Out` results of a [`TermRecursor`].
///
/// Wrap any recursor with [`Memoize::new`] to get automatic caching backed by a
/// [`HashMap`]. Use [`Memoize::with_cache`] to supply a pre-populated or
/// custom cache.
///
/// The `inner` recursor and `cache` are public fields, so callers can inspect or reuse
/// the cache after traversal.
///
/// Be aware of recursors with side effects! A cache hit will not perform the side effect of that term!
pub struct Memoize<R, M> {
    /// The wrapped recursor whose callbacks are delegated to.
    pub inner: R,
    /// The term-to-result cache. Publicly accessible so callers can inspect, reuse,
    /// or pre-populate it across traversals.
    pub cache: M,
}

impl<R, M> Deref for Memoize<R, M> {
    type Target = R;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<R, M> DerefMut for Memoize<R, M> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<R, T, Out> Memoize<R, HashMap<T, Out>> {
    /// Create a new memoized recursor backed by an empty `HashMap`.
    pub fn new<Str, So>(inner: R) -> Self
    where
        R: TermRecursor<Str, So, T, Out = Out>,
    {
        Self {
            inner,
            cache: HashMap::new(),
        }
    }
}

impl<R, M> Memoize<R, M> {
    /// Create a memoized recursor with a caller-supplied cache.
    ///
    /// This is useful for reusing a cache across multiple traversals, e.g. passing in
    /// `previous.cache` or `&mut previous.cache` to avoid recomputing results for terms that were already
    /// visited.
    pub fn with_cache<Str, So, T>(inner: R, cache: M) -> Self
    where
        R: TermRecursor<Str, So, T>,
        M: InsertableMapping<Key = T, Value = R::Out>,
    {
        Self { inner, cache }
    }
}

impl<K, V, R, M> Memoizing<K, V> for Memoize<R, M>
where
    M: InsertableMapping<Key = K, Value = V>,
{
    type Cache<'a>
        = &'a mut M
    where
        M: 'a,
        R: 'a;

    fn cache_mut(&mut self) -> Self::Cache<'_> {
        &mut self.cache
    }
}

/// Internal trait abstracting cache access for memoized recursion.
///
/// Implemented by [`Memoize`] to expose its cache to [`MemoizedRecursion`], which
/// inserts results after each `on_*` callback.
pub(crate) trait Memoizing<K, V> {
    type Cache<'a>: DerefMut<Target: InsertableMapping<Key = K, Value = V>>
    where
        Self: 'a;

    fn cache_mut(&mut self) -> Self::Cache<'_>;
}

/// Internal wrapper that interposes caching logic between the traversal engine and
/// the user's recursor.
///
/// All `on_*` callbacks that produce `Out` delegate to the inner recursor and then
/// insert the result into the cache. Auxiliary callbacks (`setup_*`, `on_let_binding`,
/// `on_match_arm`, `on_attribute_*`) delegate directly without caching.
///
/// This type is not public — users interact with [`Memoize`] directly.
pub(crate) struct MemoizedRecursion<'a, R>(&'a mut R);

impl<Str, So, T, R> TermRecursor<Str, So, T> for MemoizedRecursion<'_, R>
where
    T: Clone,
    R: TermRecursor<Str, So, T, Out: Clone>,
    R: Memoizing<T, R::Out>,
{
    type Out = R::Out;
    type Attr = R::Attr;
    type Binding = R::Binding;
    type Pattern = R::Pattern;
    type Arm = R::Arm;
    type Err = R::Err;

    fn recurse_on_term(&mut self, t: &T) -> Result<Self::Out, Self::Err>
    where
        T: Contains<T: Repr<T = Term<Str, So, T>>>,
    {
        MemoizedScheme::term_recursion(self, t)
    }

    delegate! {
        to self.0 {
            fn on_attribute_keyword(&mut self, keyword: &Keyword) -> Result<Self::Attr, Self::Err>;
            fn on_attribute_constant(&mut self, keyword: &Keyword, constant: &Constant<Str>) -> Result<Self::Attr, Self::Err>;
            fn on_attribute_symbol(&mut self, keyword: &Keyword, symbol: &Str) -> Result<Self::Attr, Self::Err>;
            fn on_attribute_named(&mut self, name: &Str) -> Result<Self::Attr, Self::Err>;
            fn on_attribute_pattern(&mut self, patterns: &[T], patterns_rec: Vec<Self::Out>) -> Result<Self::Attr, Self::Err>;
            fn on_let_binding(&mut self, current: &T, vs: &[VarBinding<Str, T>], body: &T, binding_idx: usize, binding_rec: Self::Out) -> Result<Self::Binding, Self::Err>;
            fn setup_let_scope(&mut self, current: &T, vs: &[VarBinding<Str, T>], body: &T, vs_rec: &[Self::Binding]) -> Result<(), Self::Err>;
            fn cleanup_let_scope_on_error(&mut self, current: &T, vs: &[VarBinding<Str, T>], body: &T, vs_rec: Vec<Self::Binding>);
            fn setup_quantifier_scope(&mut self, current: &T, vs: &[VarBinding<Str, So>], t: &T, is_forall: bool) -> Result<(), Self::Err>;
            fn cleanup_quantifier_scope_on_error(&mut self, current: &T, vs: &[VarBinding<Str, So>], t: &T, is_forall: bool);
            fn setup_match_case_scope(&mut self, current: &T, scrutinee: &T, cases: &[PatternArm<Str, T>], scrutinee_rec: &Self::Out, case_idx: usize) -> Result<Self::Pattern, Self::Err>;
            fn cleanup_match_case_scope_on_error(&mut self, current: &T, scrutinee: &T, cases: &[PatternArm<Str, T>], scrutinee_rec: Self::Out, case_idx: usize);
            fn on_match_arm(&mut self, current: &T, scrutinee: &T, cases: &[PatternArm<Str, T>], scrutinee_rec: &Self::Out, case_idx: usize, current_pattern: Self::Pattern, arm: Self::Out) -> Result<Self::Arm, Self::Err>;
        }
    }

    fn on_constant(
        &mut self,
        current: &T,
        constant: &Constant<Str>,
        sort: &Option<So>,
    ) -> Result<Self::Out, Self::Err> {
        let r = self.0.on_constant(current, constant, sort)?;
        self.0.cache_mut().insert(current.clone(), r.clone());
        Ok(r)
    }

    fn on_global(
        &mut self,
        current: &T,
        id: &QualifiedIdentifier<Str, So>,
        sort: &Option<So>,
    ) -> Result<Self::Out, Self::Err> {
        let r = self.0.on_global(current, id, sort)?;
        self.0.cache_mut().insert(current.clone(), r.clone());
        Ok(r)
    }

    fn on_local(&mut self, current: &T, id: &Local<Str, So>) -> Result<Self::Out, Self::Err> {
        let r = self.0.on_local(current, id)?;
        self.0.cache_mut().insert(current.clone(), r.clone());
        Ok(r)
    }

    fn on_app(
        &mut self,
        current: &T,
        id: &QualifiedIdentifier<Str, So>,
        ts: &[T],
        s: &Option<So>,
        recs: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        let r = self.0.on_app(current, id, ts, s, recs)?;
        self.0.cache_mut().insert(current.clone(), r.clone());
        Ok(r)
    }

    fn on_let(
        &mut self,
        current: &T,
        vs: &[VarBinding<Str, T>],
        body: &T,
        vs_rec: Vec<Self::Binding>,
        body_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        let r = self.0.on_let(current, vs, body, vs_rec, body_rec)?;
        self.0.cache_mut().insert(current.clone(), r.clone());
        Ok(r)
    }

    fn on_exists(
        &mut self,
        current: &T,
        vs: &[VarBinding<Str, So>],
        t: &T,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        let r = self.0.on_exists(current, vs, t, t_rec)?;
        self.0.cache_mut().insert(current.clone(), r.clone());
        Ok(r)
    }

    fn on_forall(
        &mut self,
        current: &T,
        vs: &[VarBinding<Str, So>],
        t: &T,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        let r = self.0.on_forall(current, vs, t, t_rec)?;
        self.0.cache_mut().insert(current.clone(), r.clone());
        Ok(r)
    }

    fn on_match(
        &mut self,
        current: &T,
        scrutinee: &T,
        cases: &[PatternArm<Str, T>],
        scrutinee_rec: Self::Out,
        cases_rec: Vec<Self::Arm>,
    ) -> Result<Self::Out, Self::Err> {
        let r = self
            .0
            .on_match(current, scrutinee, cases, scrutinee_rec, cases_rec)?;
        self.0.cache_mut().insert(current.clone(), r.clone());
        Ok(r)
    }

    fn on_annotated(
        &mut self,
        current: &T,
        t: &T,
        anns: &[Attribute<Str, T>],
        t_rec: Self::Out,
        anns_rec: Vec<Self::Attr>,
    ) -> Result<Self::Out, Self::Err> {
        let r = self.0.on_annotated(current, t, anns, t_rec, anns_rec)?;
        self.0.cache_mut().insert(current.clone(), r.clone());
        Ok(r)
    }

    fn on_eq(
        &mut self,
        current: &T,
        a: &T,
        b: &T,
        a_rec: Self::Out,
        b_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        let r = self.0.on_eq(current, a, b, a_rec, b_rec)?;
        self.0.cache_mut().insert(current.clone(), r.clone());
        Ok(r)
    }

    fn on_distinct(
        &mut self,
        current: &T,
        ts: &[T],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        let r = self.0.on_distinct(current, ts, ts_rec)?;
        self.0.cache_mut().insert(current.clone(), r.clone());
        Ok(r)
    }

    fn on_and(
        &mut self,
        current: &T,
        ts: &[T],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        let r = self.0.on_and(current, ts, ts_rec)?;
        self.0.cache_mut().insert(current.clone(), r.clone());
        Ok(r)
    }

    fn on_or(
        &mut self,
        current: &T,
        ts: &[T],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        let r = self.0.on_or(current, ts, ts_rec)?;
        self.0.cache_mut().insert(current.clone(), r.clone());
        Ok(r)
    }

    fn on_xor(
        &mut self,
        current: &T,
        ts: &[T],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        let r = self.0.on_xor(current, ts, ts_rec)?;
        self.0.cache_mut().insert(current.clone(), r.clone());
        Ok(r)
    }

    fn on_not(&mut self, current: &T, t: &T, t_rec: Self::Out) -> Result<Self::Out, Self::Err> {
        let r = self.0.on_not(current, t, t_rec)?;
        self.0.cache_mut().insert(current.clone(), r.clone());
        Ok(r)
    }

    fn on_implies(
        &mut self,
        current: &T,
        ts: &[T],
        t: &T,
        ts_rec: Vec<Self::Out>,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        let r = self.0.on_implies(current, ts, t, ts_rec, t_rec)?;
        self.0.cache_mut().insert(current.clone(), r.clone());
        Ok(r)
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
        let r = self.0.on_ite(current, b, t, e, b_rec, t_rec, e_rec)?;
        self.0.cache_mut().insert(current.clone(), r.clone());
        Ok(r)
    }
}

/// [`TermRecursor`] implementation for [`Memoize`].
///
/// All callbacks delegate directly to the inner recursor. The actual caching is performed
/// by `MemoizedRecursion`, which wraps `self` during [`Self::recurse_on_term`] and inserts
/// results into the cache after each `on_*` callback that produces `Out`.
///
/// This two-layer design means:
/// - Calling [`Self::recurse_on_term`] on a `Memoize` gives you full memoized traversal.
/// - Calling individual `on_*` methods directly bypasses caching (they are plain delegations).
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
        T: Contains<T: Repr<T = Term<Str, So, T>>>,
    {
        MemoizedRecursion(self).recurse_on_term(t)
    }

    delegate! {
        #[inline]
        to self.inner {
            fn on_attribute_keyword(&mut self, keyword: &Keyword) -> Result<Self::Attr, Self::Err>;
            fn on_attribute_constant(&mut self, keyword: &Keyword, constant: &Constant<Str>) -> Result<Self::Attr, Self::Err>;
            fn on_attribute_symbol(&mut self, keyword: &Keyword, symbol: &Str) -> Result<Self::Attr, Self::Err>;
            fn on_attribute_named(&mut self, name: &Str) -> Result<Self::Attr, Self::Err>;
            fn on_attribute_pattern(&mut self, patterns: &[T], patterns_rec: Vec<Self::Out>) -> Result<Self::Attr, Self::Err>;
            fn on_let_binding(&mut self, current: &T, vs: &[VarBinding<Str, T>], body: &T, binding_idx: usize, binding_rec: Self::Out) -> Result<Self::Binding, Self::Err>;
            fn setup_let_scope(&mut self, current: &T, vs: &[VarBinding<Str, T>], body: &T, vs_rec: &[Self::Binding]) -> Result<(), Self::Err>;
            fn cleanup_let_scope_on_error(&mut self, current: &T, vs: &[VarBinding<Str, T>], body: &T, vs_rec: Vec<Self::Binding>);
            fn setup_quantifier_scope(&mut self, current: &T, vs: &[VarBinding<Str, So>], t: &T, is_forall: bool) -> Result<(), Self::Err>;
            fn cleanup_quantifier_scope_on_error(&mut self, current: &T, vs: &[VarBinding<Str, So>], t: &T, is_forall: bool);
            fn setup_match_case_scope(&mut self, current: &T, scrutinee: &T, cases: &[PatternArm<Str, T>], scrutinee_rec: &Self::Out, case_idx: usize) -> Result<Self::Pattern, Self::Err>;
            fn cleanup_match_case_scope_on_error(&mut self, current: &T, scrutinee: &T, cases: &[PatternArm<Str, T>], scrutinee_rec: Self::Out, case_idx: usize);
            fn on_match_arm(&mut self, current: &T, scrutinee: &T, cases: &[PatternArm<Str, T>], scrutinee_rec: &Self::Out, case_idx: usize, current_pattern: Self::Pattern, arm: Self::Out) -> Result<Self::Arm, Self::Err>;
            fn on_constant(&mut self, current: &T, constant: &Constant<Str>, sort: &Option<So>) -> Result<Self::Out, Self::Err>;
            fn on_global(&mut self, current: &T, id: &QualifiedIdentifier<Str, So>, sort: &Option<So>) -> Result<Self::Out, Self::Err>;
            fn on_local(&mut self, current: &T, id: &Local<Str, So>) -> Result<Self::Out, Self::Err>;
            fn on_app(&mut self, current: &T, id: &QualifiedIdentifier<Str, So>, ts: &[T], s: &Option<So>, recs: Vec<Self::Out>) -> Result<Self::Out, Self::Err>;
            fn on_let(&mut self, current: &T, vs: &[VarBinding<Str, T>], body: &T, vs_rec: Vec<Self::Binding>, body_rec: Self::Out) -> Result<Self::Out, Self::Err>;
            fn on_exists(&mut self, current: &T, vs: &[VarBinding<Str, So>], t: &T, t_rec: Self::Out) -> Result<Self::Out, Self::Err>;
            fn on_forall(&mut self, current: &T, vs: &[VarBinding<Str, So>], t: &T, t_rec: Self::Out) -> Result<Self::Out, Self::Err>;
            fn on_match(&mut self, current: &T, scrutinee: &T, cases: &[PatternArm<Str, T>], scrutinee_rec: Self::Out, cases_rec: Vec<Self::Arm>) -> Result<Self::Out, Self::Err>;
            fn on_annotated(&mut self, current: &T, t: &T, anns: &[Attribute<Str, T>], t_rec: Self::Out, anns_rec: Vec<Self::Attr>) -> Result<Self::Out, Self::Err>;
            fn on_eq(&mut self, current: &T, a: &T, b: &T, a_rec: Self::Out, b_rec: Self::Out) -> Result<Self::Out, Self::Err>;
            fn on_distinct(&mut self, current: &T, ts: &[T], ts_rec: Vec<Self::Out>) -> Result<Self::Out, Self::Err>;
            fn on_and(&mut self, current: &T, ts: &[T], ts_rec: Vec<Self::Out>) -> Result<Self::Out, Self::Err>;
            fn on_or(&mut self, current: &T, ts: &[T], ts_rec: Vec<Self::Out>) -> Result<Self::Out, Self::Err>;
            fn on_xor(&mut self, current: &T, ts: &[T], ts_rec: Vec<Self::Out>) -> Result<Self::Out, Self::Err>;
            fn on_not(&mut self, current: &T, t: &T, t_rec: Self::Out) -> Result<Self::Out, Self::Err>;
            fn on_implies(&mut self, current: &T, ts: &[T], t: &T, ts_rec: Vec<Self::Out>, t_rec: Self::Out) -> Result<Self::Out, Self::Err>;
            fn on_ite(&mut self, current: &T, b: &T, t: &T, e: &T, b_rec: Self::Out, t_rec: Self::Out, e_rec: Self::Out) -> Result<Self::Out, Self::Err>;
        }
    }
}

/// A caching traversal scheme for [`Memoize`]-wrapped recursors.
///
/// Overrides [`expand_and_resolve`](TermRecursionScheme::expand_and_resolve) to check
/// the cache before descending into a term. On a cache hit, the entire sub-tree is
/// skipped and the cached result is returned immediately.
pub(crate) struct MemoizedScheme;

impl<'b, R, Str, So, T> TermRecursionScheme<MemoizedRecursion<'b, R>, Str, So, T> for MemoizedScheme
where
    T: Clone,
    R: TermRecursor<Str, So, T, Out: Clone>,
    R: Memoizing<T, R::Out>,
{
    /// Like [`expand_and_resolve`], but checks the cache before descending.
    ///
    /// If `current` is already in the cache, the cached result is returned immediately
    /// without pushing any frames or invoking any callbacks.
    fn expand_and_resolve<'a>(
        recursor: &mut MemoizedRecursion<'b, R>,
        stack: &mut RStack<'a, MemoizedRecursion<'b, R>, Str, So, T>,
        mut current: &'a T,
    ) -> Result<R::Out, R::Err>
    where
        Str: 'a,
        So: 'a,
        T: Contains<T: Repr<T = Term<Str, So, T>>>,
    {
        loop {
            if let Some(r) = recursor.0.cache_mut().lookup(current) {
                return Ok(r);
            }

            match Self::expand_and_resolve_once(recursor, stack, current)? {
                Either::Left(l) => {
                    current = l;
                }
                Either::Right(r) => {
                    return Ok(r);
                }
            }
        }
    }
}
