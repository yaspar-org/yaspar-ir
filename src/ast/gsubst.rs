// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! This module handles expansions of global definitions
//!
//! In principle, a global substitution operation expands global definitions, invoking [Substitute::subst]
//! whenever necessary.

use crate::allocator::{SortAllocator, TermAllocator};
use crate::ast::alg::{PatternArm, VarBinding};
use crate::ast::subst::{Substitute, Substitution};
use crate::ast::{
    ATerm, Arena, Attribute, Context, FetchSort, FunctionDef, HasArena, Monomorphization, Sort,
    Str, Term,
};
use crate::raw::tc::unif::{empty_subst, instantiate_subst};
use crate::traits::{AllocatableString, Repr};
use std::collections::{HashMap, HashSet};

/// Expand global names with their definitions in `Self`.
///
/// This trait implements substitutions by expanding the bodies of names during substitutions.
pub trait GlobalSubst<E> {
    fn gsubst<S>(&self, global_names: impl IntoIterator<Item = S>, env: &mut E) -> Self
    where
        S: AllocatableString<Arena>;
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
        let mut cache = HashMap::new();
        let global_names = global_names
            .into_iter()
            .map(|s| s.allocate(env.arena()))
            .collect::<HashSet<_>>();
        self.gsubst_impl(&global_names, &HashSet::new(), env, &mut cache)
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
