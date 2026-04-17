// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! This module handles expansions of global definitions.
//!
//! A global substitution operation expands global definitions, invoking [`Substitute::subst`]
//! whenever necessary. The [`GlobalSubst`] trait provides the main entry point via
//! `.gsubst(names, context)`, which expands the specified global definitions on the fly.

use crate::allocator::{SortAllocator, TermAllocator};
use crate::ast::alg::VarBinding;
use crate::ast::subst::{Substitute, Substitution};
use crate::ast::{
    ATerm, Arena, Attribute, Constant, Context, FetchSort, FunctionDef, HasArena, Local,
    Monomorphization, PatternArm, QualifiedIdentifier, Sort, Str, Term, TypedBuilder,
};
use crate::ast::{TermRecursor, TypedTermRecursor};
use crate::raw::alg::rec::Bottom;
use crate::raw::instance;
use crate::raw::tc::unif::{empty_subst, instantiate_subst};
use crate::traits::{AllocatableString, Repr};
use delegate::delegate;
use std::collections::{HashMap, HashSet};
use yaspar::ast::Keyword;

/// Expand global names with their definitions in `Self`.
///
/// This trait implements substitutions by expanding the bodies of names during substitutions.
pub trait GlobalSubst<E> {
    fn gsubst<S>(&self, global_names: impl IntoIterator<Item = S>, env: &mut E) -> Self
    where
        S: AllocatableString<Arena>;

    fn gsubst_with_names(&self, global_names: &HashSet<Str>, env: &mut E) -> Self;
}

impl<T, E> GlobalSubst<E> for T
where
    T: GlobalSubstImpl<E>,
    E: HasArena,
{
    fn gsubst<S>(&self, global_names: impl IntoIterator<Item = S>, env: &mut E) -> Self
    where
        S: AllocatableString<Arena>,
    {
        {
            let global_names = global_names
                .into_iter()
                .map(|s| s.allocate(env.arena()))
                .collect::<HashSet<_>>();
            self.gsubst_with_names(&global_names, env)
        }
    }

    fn gsubst_with_names(&self, global_names: &HashSet<Str>, env: &mut E) -> Self {
        let mut cache = HashMap::new();
        self.gsubst_impl(global_names, &HashSet::new(), env, &mut cache)
    }
}

trait GlobalSubstImpl<E> {
    fn gsubst_impl(
        &self,
        global_names: &HashSet<Str>,
        block: &HashSet<Str>,
        env: &mut E,
        cache: &mut HashMap<Str, FunctionDef>,
    ) -> Self;
}

impl<T, E> GlobalSubstImpl<E> for Vec<T>
where
    T: GlobalSubstImpl<E>,
{
    fn gsubst_impl(
        &self,
        global_names: &HashSet<Str>,
        block: &HashSet<Str>,
        env: &mut E,
        cache: &mut HashMap<Str, FunctionDef>,
    ) -> Self {
        self.iter()
            .map(|v| v.gsubst_impl(global_names, block, env, cache))
            .collect()
    }
}

impl GlobalSubstImpl<Context> for Attribute {
    fn gsubst_impl(
        &self,
        global_names: &HashSet<Str>,
        block: &HashSet<Str>,
        env: &mut Context,
        cache: &mut HashMap<Str, FunctionDef>,
    ) -> Self {
        if let Attribute::Pattern(ts) = self {
            Attribute::Pattern(ts.gsubst_impl(global_names, block, env, cache))
        } else {
            self.clone()
        }
    }
}

fn populate_cache(
    sym: &Str,
    global_names: &HashSet<Str>,
    env: &mut Context,
    cache: &mut HashMap<Str, FunctionDef>,
) -> bool {
    if !cache.contains_key(sym) {
        if let Some(def) = env.get_definition(sym).cloned() {
            let ret = def
                .def
                .body
                .gsubst_impl(global_names, &def.rec_deps, env, cache);
            // the only possible case is a parametric function

            cache.insert(
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

impl GlobalSubstImpl<Context> for Term {
    fn gsubst_impl(
        &self,
        global_names: &HashSet<Str>,
        block: &HashSet<Str>,
        env: &mut Context,
        cache: &mut HashMap<Str, FunctionDef>,
    ) -> Self {
        match self.repr() {
            ATerm::Constant(_, _) | ATerm::Local(_) => self.clone(),
            ATerm::Global(qid, sort) => {
                let sort = sort.as_ref().expect("type invariant violation!").clone();
                let sym = qid.id_str();
                if global_names.contains(sym) && !block.contains(sym) {
                    if !populate_cache(sym, global_names, env, cache) {
                        return self.clone();
                    }
                    // The cache was just populated
                    let def = cache.get(sym).unwrap();
                    if def.sort_params.is_empty() {
                        def.body.clone()
                    } else {
                        // We instantiate a substitution with the sort in the signature
                        // with the overall sort, and use that to propagate the sort information to
                        // obtain the final overall term
                        let mut subst = empty_subst(&def.sort_params);
                        instantiate_subst(&mut subst, [(&def.out_sort, &sort)]).unwrap();
                        def.body.monomorphize(&subst, env)
                    }
                } else {
                    self.clone()
                }
            }
            ATerm::App(f, args, sort) => {
                let sort = sort.as_ref().expect("type invariant violation!").clone();
                let nargs: Vec<Term> = args
                    .iter()
                    .map(|a| a.gsubst_impl(global_names, block, env, cache))
                    .collect();
                let sym = f.id_str();
                if global_names.contains(sym) && !block.contains(sym) {
                    if !populate_cache(sym, global_names, env, cache) {
                        return self.clone();
                    }
                    // The cache was just populated
                    let def = cache.get(sym).unwrap();
                    let sorts: Vec<Sort> = nargs.iter().map(|t| t.get_sort(env)).collect();
                    let subst =
                        Substitution::new_str(def.vars.iter().map(|v| v.0.clone()).zip(nargs));
                    if def.sort_params.is_empty() {
                        def.body.subst(&subst, env)
                    } else {
                        // We instantiate a substitution with the sort in the signature
                        // with the overall sort, and use that to propagate the sort information to
                        // obtain the final overall term
                        let mut sort_subst = empty_subst(&def.sort_params);
                        let sort_params: Vec<_> = def
                            .sort_params
                            .iter()
                            .map(|s| env.sort0(s.clone()))
                            .collect();
                        instantiate_subst(
                            &mut sort_subst,
                            sort_params
                                .iter()
                                .zip(sorts.iter())
                                .chain([(&def.out_sort, &sort)]),
                        )
                        .unwrap();
                        def.body.monomorphize(&sort_subst, env).subst(&subst, env)
                    }
                } else {
                    env.arena.app(f.clone(), nargs, Some(sort.clone()))
                }
            }
            ATerm::Let(bindings, body) => {
                let nbindings = bindings
                    .iter()
                    .map(|b| {
                        VarBinding(
                            b.0.clone(),
                            b.1,
                            b.2.gsubst_impl(global_names, block, env, cache),
                        )
                    })
                    .collect();
                let nbody = body.gsubst_impl(global_names, block, env, cache);
                env.let_term(nbindings, nbody)
            }
            ATerm::Exists(vs, body) => {
                let nbody = body.gsubst_impl(global_names, block, env, cache);
                env.exists(vs.clone(), nbody)
            }
            ATerm::Forall(vs, body) => {
                let nbody = body.gsubst_impl(global_names, block, env, cache);
                env.forall(vs.clone(), nbody)
            }
            ATerm::Matching(t, cases) => {
                let nt = t.gsubst_impl(global_names, block, env, cache);
                let ncases = cases
                    .iter()
                    .map(|c| PatternArm {
                        pattern: c.pattern.clone(),
                        body: c.body.gsubst_impl(global_names, block, env, cache),
                    })
                    .collect();
                env.matching(nt, ncases)
            }
            ATerm::Annotated(t, annos) => {
                let nt = t.gsubst_impl(global_names, block, env, cache);
                let nannos = annos.gsubst_impl(global_names, block, env, cache);
                env.annotated(nt, nannos)
            }
            ATerm::Eq(a, b) => {
                let na = a.gsubst_impl(global_names, block, env, cache);
                let nb = b.gsubst_impl(global_names, block, env, cache);
                env.eq(na, nb)
            }
            ATerm::Distinct(ts) => {
                let nts = ts.gsubst_impl(global_names, block, env, cache);
                env.distinct(nts)
            }
            ATerm::And(ts) => {
                let nts = ts.gsubst_impl(global_names, block, env, cache);
                env.and(nts)
            }
            ATerm::Or(ts) => {
                let nts = ts.gsubst_impl(global_names, block, env, cache);
                env.or(nts)
            }
            ATerm::Xor(ts) => {
                let nts = ts.gsubst_impl(global_names, block, env, cache);
                env.xor(nts)
            }
            ATerm::Implies(ts, concl) => {
                let nts = ts.gsubst_impl(global_names, block, env, cache);
                let nconcl = concl.gsubst_impl(global_names, block, env, cache);
                env.implies(nts, nconcl)
            }
            ATerm::Not(t) => {
                let nt = t.gsubst_impl(global_names, block, env, cache);
                env.not(nt)
            }
            ATerm::Ite(c, t, e) => {
                let nc = c.gsubst_impl(global_names, block, env, cache);
                let nt = t.gsubst_impl(global_names, block, env, cache);
                let ne = e.gsubst_impl(global_names, block, env, cache);
                env.ite(nc, nt, ne)
            }
        }
    }
}

/// Stack-safe global definition expansion using [`TermRecursor`].
///
/// Expands global definitions (from `define-fun`, `define-const`, etc.) by inlining their
/// bodies. For parametric definitions, applies monomorphization. Uses a cache to avoid
/// re-expanding the same definition multiple times.
pub struct GlobalSubstituter<'a> {
    inner: TypedBuilder<'a, Context>,
    global_names: &'a HashSet<Str>,
    cache: HashMap<Str, FunctionDef>,
}

impl<'a> GlobalSubstituter<'a> {
    pub fn new(ctx: &'a mut Context, global_names: &'a HashSet<Str>) -> Self {
        Self {
            inner: TypedBuilder::new(ctx),
            global_names,
            cache: HashMap::new(),
        }
    }

    /// Populate the cache for a symbol if not already present. Returns true if the definition
    /// exists and was cached (or was already cached).
    fn populate_cache(&mut self, sym: &Str) -> bool {
        if !self.cache.contains_key(sym) {
            if let Some(def) = self.inner.arena.get_definition(sym).cloned() {
                let ret = self.recurse_on_term_no_err()

                let ret = def
                    .def
                    .body
                    .gsubst_impl(global_names, &def.rec_deps, env, cache);
                // the only possible case is a parametric function

                cache.insert(
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
        }    }

    fn arena(&mut self) -> &mut Arena {
        &mut self.ctx.arena
    }
}

impl TermRecursor<Str, Sort, Term> for GlobalSubstituter<'_> {
    type Out = Term;
    type Attr = Attribute;
    type Binding = VarBinding<Str, Term>;
    type Pattern = ();
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
            fn setup_match_case_scope(&mut self, current: &Term, scrutinee: &Term, cases: &[PatternArm], scrutinee_rec: &Self::Out, case_idx: usize) -> Result<(), Bottom>;
            fn on_match_arm(&mut self, current: &Term, scrutinee: &Term, cases: &[PatternArm], case_idx: usize, current_pattern: (), arm: Term) -> Result<PatternArm, Bottom>;
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
        if self.global_names.contains(sym) {
            if !self.populate_cache(sym) {
                return Ok(current.clone());
            }
            let def = self.cache.get(sym).unwrap();
            if def.sort_params.is_empty() {
                Ok(def.body.clone())
            } else {
                let mut subst = empty_subst(&def.sort_params);
                instantiate_subst(&mut subst, [(&def.out_sort, &sort)]).unwrap();
                Ok(def.body.monomorphize(&subst, self.ctx))
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
        if self.global_names.contains(sym) {
            if !self.populate_cache(sym) {
                return Ok(self.arena().app(f.clone(), recs, Some(sort)));
            }
            let def = self.cache.get(sym).unwrap();
            let sorts: Vec<Sort> = recs.iter().map(|t| t.get_sort(self.ctx)).collect();
            let subst = Substitution::new_str(def.vars.iter().map(|v| v.0.clone()).zip(recs));
            if def.sort_params.is_empty() {
                Ok(def.body.subst(&subst, self.ctx))
            } else {
                let mut sort_subst = empty_subst(&def.sort_params);
                let sort_params: Vec<_> = def
                    .sort_params
                    .iter()
                    .map(|s| self.ctx.sort0(s.clone()))
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
                    .monomorphize(&sort_subst, self.ctx)
                    .subst(&subst, self.ctx))
            }
        } else {
            Ok(self.arena().app(f.clone(), recs, Some(sort)))
        }
    }
}

impl TypedTermRecursor for GlobalSubstituter<'_> {}
