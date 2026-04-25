// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! This module handles expansions of global definitions.
//!
//! A global substitution operation expands global definitions, invoking local substitution
//! whenever necessary. The [`GlobalSubst`] trait provides the main entry point via
//! `.gsubst(names, context)`, which expands the specified global definitions on the fly.

use crate::allocator::{SortAllocator, TermAllocator};
use crate::ast::alg::VarBinding;
use crate::ast::subst::SubstituteV2;
use crate::ast::{
    Arena, Attribute, Constant, Context, FetchSort, FunctionDef, HasArena, Local, Memoize,
    Monomorphization, Pattern, PatternArm, QualifiedIdentifier, Sort, Str, SubstitutionV2, Term,
    TypedBuilder,
};
use crate::ast::{TermRecursor, TypedTermRecursor};
use crate::raw::alg::rec::Bottom;
use crate::raw::tc::unif::{empty_subst, instantiate_subst};
use crate::traits::AllocatableString;
use delegate::delegate;
use std::collections::{HashMap, HashSet};
use yaspar::ast::Keyword;

/// Expand global names with their definitions in `Self`.
///
/// This trait implements substitutions by expanding the bodies of names during substitutions.
pub trait GlobalSubst<E> {
    /// The type produced by the substitution.
    type Out;

    /// Apply global substitutions with an iterable of specific names of global definitions to expand.
    fn gsubst<S>(&self, global_names: impl IntoIterator<Item = S>, env: &mut E) -> Self::Out
    where
        S: AllocatableString<Arena>;

    /// Like [`gsubst`](Self::gsubst), but accepts a pre-allocated set of names.
    fn gsubst_with_names(&self, global_names: &HashSet<Str>, env: &mut E) -> Self::Out;

    /// Apply global substitutions to all global definitions
    fn gsubst_all(&self, env: &mut E) -> Self::Out;
}

impl GlobalSubst<Context> for [Term] {
    type Out = Vec<Term>;

    fn gsubst<S>(&self, global_names: impl IntoIterator<Item = S>, env: &mut Context) -> Self::Out
    where
        S: AllocatableString<Arena>,
    {
        let global_names = global_names
            .into_iter()
            .map(|s| s.allocate(env.arena()))
            .collect::<HashSet<_>>();
        self.gsubst_with_names(&global_names, env)
    }

    fn gsubst_with_names(&self, global_names: &HashSet<Str>, env: &mut Context) -> Self::Out {
        let mut cache = HashMap::new();
        let block = HashSet::new();
        let mut gsubster = GlobalSubstituter::create(env, global_names, &block, &mut cache);
        self.iter()
            .map(|t| gsubster.recurse_on_term_no_err(t))
            .collect()
    }

    fn gsubst_all(&self, env: &mut Context) -> Self::Out {
        let block = HashSet::new();
        let global_names = env.defined_symbols();
        #[cfg(feature = "cache")]
        {
            let mut cache = std::mem::take(&mut env.caches.global_def_cache);
            let mut gsubster = GlobalSubstituter::create(env, &global_names, &block, &mut cache);
            let r = self
                .iter()
                .map(|t| gsubster.recurse_on_term_no_err(t))
                .collect();
            env.caches.global_def_cache = cache;
            r
        }
        #[cfg(not(feature = "cache"))]
        {
            let mut cache = HashMap::new();
            let mut gsubster = GlobalSubstituter::create(env, &global_names, &block, &mut cache);
            self.iter()
                .map(|t| gsubster.recurse_on_term_no_err(t))
                .collect()
        }
    }
}

impl GlobalSubst<Context> for Term {
    type Out = Term;

    fn gsubst<S>(&self, global_names: impl IntoIterator<Item = S>, env: &mut Context) -> Self::Out
    where
        S: AllocatableString<Arena>,
    {
        std::slice::from_ref(self)
            .gsubst(global_names, env)
            .pop()
            .unwrap()
    }

    fn gsubst_with_names(&self, global_names: &HashSet<Str>, env: &mut Context) -> Self::Out {
        std::slice::from_ref(self)
            .gsubst_with_names(global_names, env)
            .pop()
            .unwrap()
    }

    fn gsubst_all(&self, env: &mut Context) -> Self::Out {
        std::slice::from_ref(self).gsubst_all(env).pop().unwrap()
    }
}

/// Memoized, stack-safe global definition expander. Use [`GlobalSubstituter::create`] to construct.
pub type GlobalSubstituter<'a> = Memoize<GlobalSubstituterInner<'a>, HashMap<Term, Term>>;

impl<'a> GlobalSubstituter<'a> {
    /// Create a new memoized global substituter.
    ///
    /// - `ctx`: the context holding global definitions.
    /// - `global_names`: the set of names to expand.
    /// - `block`: names to block from expansion (e.g. to prevent infinite recursion).
    /// - `global_def_cache`: shared cache for resolved function definitions.
    pub fn create(
        ctx: &'a mut Context,
        global_names: &'a HashSet<Str>,
        block: &'a HashSet<Str>,
        global_def_cache: &'a mut HashMap<Str, FunctionDef>,
    ) -> Self {
        Memoize::new(GlobalSubstituterInner {
            inner: TypedBuilder::new(ctx),
            global_names,
            block,
            global_def_cache,
        })
    }
}

/// Stack-safe global definition expansion using [`TermRecursor`].
///
/// Expands global definitions (from `define-fun`, `define-const`, etc.) by inlining their
/// bodies. For parametric definitions, applies monomorphization. Uses a cache to avoid
/// re-expanding the same definition multiple times.
pub struct GlobalSubstituterInner<'a> {
    inner: TypedBuilder<'a, Context>,
    global_names: &'a HashSet<Str>,
    block: &'a HashSet<Str>,
    global_def_cache: &'a mut HashMap<Str, FunctionDef>,
}

impl<'a> GlobalSubstituterInner<'a> {
    /// Create a child substituter that additionally blocks the given names from expansion.
    pub fn with_block<'b>(&'b mut self, block: &'b HashSet<Str>) -> GlobalSubstituterInner<'b>
    where
        'a: 'b,
    {
        GlobalSubstituterInner {
            inner: TypedBuilder::new(self.inner.arena),
            global_names: self.global_names,
            block,
            global_def_cache: self.global_def_cache,
        }
    }

    /// Populate the cache for a symbol if not already present. Returns true if the definition
    /// exists and was cached (or was already cached).
    fn populate_cache(&mut self, sym: &Str) -> bool {
        if !self.global_def_cache.contains_key(sym) {
            if let Some(def) = self.inner.arena.get_definition(sym).cloned() {
                let mut gsubster = self.with_block(&def.rec_deps);
                let ret = gsubster.recurse_on_term_no_err(&def.def.body);

                // the only possible case is a parametric function
                self.global_def_cache.insert(
                    def.def.name.clone(),
                    FunctionDef {
                        body: ret.clone(),
                        ..def.def
                    },
                );
                true
            } else {
                false
            }
        } else {
            true
        }
    }
}

impl HasArena for GlobalSubstituterInner<'_> {
    #[inline]
    fn arena(&mut self) -> &mut Arena {
        self.inner.arena()
    }
}

impl TermRecursor<Str, Sort, Term> for GlobalSubstituterInner<'_> {
    type Out = Term;
    type Attr = Attribute;
    type Binding = VarBinding<Str, Term>;
    type Pattern = Pattern;
    type Arm = PatternArm;
    type Err = Bottom;

    delegate! {
        to self.inner {
            fn on_constant(&mut self, current: &Term, constant: &Constant, sort: &Option<Sort>) -> Result<Term, Bottom>;
            fn on_local(&mut self, current: &Term, local: &Local) -> Result<Term, Bottom>;
            fn on_let_binding(&mut self, current: &Term, vs: &[VarBinding<Str, Term>], body: &Term, binding_idx: usize, binding_rec: Term) -> Result<Self::Binding, Bottom>;
            fn setup_let_scope(&mut self, current: &Term, vs: &[VarBinding<Str, Term>], body: &Term, vs_rec: &[Self::Binding]) -> Result<(), Bottom>;
            fn on_let(&mut self, current: &Term, vs: &[VarBinding<Str, Term>], body: &Term, vs_rec: Vec<Self::Binding>, body_rec: Term) -> Result<Term, Bottom>;
            fn setup_quantifier_scope(&mut self, current: &Term, vs: &[VarBinding<Str, Sort>], t: &Term, is_forall: bool) -> Result<(), Bottom>;
            fn on_exists(&mut self, current: &Term, vs: &[VarBinding<Str, Sort>], t: &Term, t_rec: Term) -> Result<Term, Bottom>;
            fn on_forall(&mut self, current: &Term, vs: &[VarBinding<Str, Sort>], t: &Term, t_rec: Term) -> Result<Term, Bottom>;
            fn setup_match_case_scope(&mut self, current: &Term, scrutinee: &Term, cases: &[PatternArm], scrutinee_rec: &Self::Out, case_idx: usize) -> Result<Pattern, Bottom>;
            fn on_match_arm(&mut self, current: &Term, scrutinee: &Term, cases: &[PatternArm], scrutinee_rec: &Self::Out, case_idx: usize, current_pattern: Pattern, arm: Term) -> Result<PatternArm, Bottom>;
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

    /// Expand a global symbol if it's in the expansion set and has a nullary definition.
    fn on_global(
        &mut self,
        current: &Term,
        qid: &QualifiedIdentifier,
        sort: &Option<Sort>,
    ) -> Result<Term, Bottom> {
        let sort = sort.as_ref().expect("type invariant violation!").clone();
        let sym = qid.id_str();
        if self.global_names.contains(sym) && !self.block.contains(sym) {
            if !self.populate_cache(sym) {
                return Ok(current.clone());
            }
            // The cache was just populated
            let def = self.global_def_cache.get(sym).unwrap();
            if def.sort_params.is_empty() {
                Ok(def.body.clone())
            } else {
                // We instantiate a substitution with the sort in the signature
                // with the overall sort, and use that to propagate the sort information to
                // obtain the final overall term
                let mut subst = empty_subst(&def.sort_params);
                instantiate_subst(&mut subst, [(&def.out_sort, &sort)]).unwrap();
                Ok(def.body.monomorphize(&subst, &mut self.inner))
            }
        } else {
            Ok(current.clone())
        }
    }

    /// Expand a function application if the head symbol is in the expansion set.
    fn on_app(
        &mut self,
        _current: &Term,
        f: &QualifiedIdentifier,
        _: &[Term],
        sort: &Option<Sort>,
        recs: Vec<Term>,
    ) -> Result<Term, Bottom> {
        let sort = sort.as_ref().expect("type invariant violation!").clone();
        let sym = f.id_str();
        if self.global_names.contains(sym) && !self.block.contains(sym) {
            if !self.populate_cache(sym) {
                return Ok(self.arena().app(f.clone(), recs, Some(sort)));
            }
            // The cache was just populated
            let def = self.global_def_cache.get(sym).unwrap();
            let sorts: Vec<Sort> = recs.iter().map(|t| t.get_sort(&mut self.inner)).collect();
            let subst = SubstitutionV2::new(def.vars.iter().map(|v| v.clone().into()).zip(recs));
            if def.sort_params.is_empty() {
                Ok(def.body.subst(&subst, &mut self.inner))
            } else {
                // We instantiate a substitution with the sort in the signature
                // with the overall sort, and use that to propagate the sort information to
                // obtain the final overall term
                let mut sort_subst = empty_subst(&def.sort_params);
                let sort_params: Vec<_> = def
                    .sort_params
                    .iter()
                    .map(|s| self.inner.sort0(s.clone()))
                    .collect();
                instantiate_subst(
                    &mut sort_subst,
                    sort_params
                        .iter()
                        .zip(sorts.iter())
                        .chain([(&def.out_sort, &sort)]),
                )
                .unwrap();
                Ok(def
                    .body
                    .monomorphize(&sort_subst, &mut self.inner)
                    .subst(&subst, &mut self.inner))
            }
        } else {
            Ok(self.arena().app(f.clone(), recs, Some(sort)))
        }
    }
}

impl TypedTermRecursor for GlobalSubstituterInner<'_> {}
