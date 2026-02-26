// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! This module handles expansions of global definitions
//!
//! In principle, a global substitution operation expands global definitions, invoking [Substitute::subst]
//! whenever necessary.
//!
//! There are two variants of the implementations:
//! 1. [GlobalSubstPreproc]: it expands global definitions transitively in a preprocessing process;
//! 2. [GlobalSubstInplace]: it expands global definitions on the fly whenever needed.
//!
//! It is unclear which strategy is more performant. We might deprecate one variant in the future.

use crate::allocator::TermAllocator;
use crate::ast::alg::{PatternArm, VarBinding};
use crate::ast::subst::{Substitute, Substitution};
use crate::ast::{ATerm, Arena, Attribute, Context, HasArena, Str, Term};
use crate::traits::{AllocatableString, Repr};
use std::collections::{HashMap, HashSet};

/// Expand global names with their definitions in `Self`.
///
/// This trait implements substitutions by expanding the bodies of names in preprocessing.
pub trait GlobalSubstPreproc<E> {
    fn gsubst_preproc<S>(&self, global_names: impl IntoIterator<Item = S>, env: &mut E) -> Self
    where
        S: AllocatableString<Arena>;
}

/// Expand global names with their definitions in `Self`.
///
/// This trait implements substitutions by expanding the bodies of names during substitutions.
pub trait GlobalSubstInplace<E> {
    fn gsubst_inplace<S>(&self, global_names: impl IntoIterator<Item = S>, env: &mut E) -> Self
    where
        S: AllocatableString<Arena>;
}

struct FuncBody {
    vars: Vec<Str>,
    body: Term,
}

trait GlobalSubstPreprocImpl<E> {
    fn gsubst_preproc_impl(&self, body_map: &HashMap<Str, FuncBody>, env: &mut E) -> Self;
}

impl<T> GlobalSubstPreproc<Context> for T
where
    T: GlobalSubstPreprocImpl<Context>,
{
    fn gsubst_preproc<S>(
        &self,
        global_names: impl IntoIterator<Item = S>,
        env: &mut Context,
    ) -> Self
    where
        S: AllocatableString<Arena>,
    {
        let global_names = global_names
            .into_iter()
            .map(|s| s.allocate(env.arena()))
            .collect::<HashSet<_>>();
        let body_map = build_body_map(env, &global_names);
        self.gsubst_preproc_impl(&body_map, env)
    }
}

impl<T, E> GlobalSubstInplace<E> for T
where
    T: GlobalSubstInplaceImpl<E>,
    E: HasArena,
{
    fn gsubst_inplace<S>(&self, global_names: impl IntoIterator<Item = S>, env: &mut E) -> Self
    where
        S: AllocatableString<Arena>,
    {
        let mut cache = HashMap::new();
        let global_names = global_names
            .into_iter()
            .map(|s| s.allocate(env.arena()))
            .collect::<HashSet<_>>();
        self.gsubst_inplace_impl(&global_names, &HashSet::new(), env, &mut cache)
    }
}

impl<T, E> GlobalSubstPreprocImpl<E> for Vec<T>
where
    T: GlobalSubstPreprocImpl<E>,
{
    fn gsubst_preproc_impl(&self, body_map: &HashMap<Str, FuncBody>, env: &mut E) -> Self {
        self.iter()
            .map(|x| x.gsubst_preproc_impl(body_map, env))
            .collect()
    }
}

impl GlobalSubstPreprocImpl<Context> for Attribute {
    fn gsubst_preproc_impl(&self, body_map: &HashMap<Str, FuncBody>, env: &mut Context) -> Self {
        match self {
            Attribute::Pattern(t) => Attribute::Pattern(t.gsubst_preproc_impl(body_map, env)),
            _ => self.clone(),
        }
    }
}

impl GlobalSubstPreprocImpl<Context> for Term {
    fn gsubst_preproc_impl(&self, body_map: &HashMap<Str, FuncBody>, env: &mut Context) -> Self {
        match self.repr() {
            ATerm::Constant(_, _) | ATerm::Local(_) => self.clone(),
            ATerm::Global(qid, _) => {
                let sym = qid.id_str();
                if let Some(body) = body_map.get(sym) {
                    body.body.clone()
                } else {
                    self.clone()
                }
            }
            ATerm::App(f, args, sort) => {
                let nargs = args
                    .iter()
                    .map(|a| a.gsubst_preproc_impl(body_map, env))
                    .collect();
                let sym = f.id_str();
                if let Some(body) = body_map.get(sym) {
                    // here we expand the definition of f
                    // we know that the signature of f and def must be consistent, so we just directly
                    // work on def.
                    let subst = Substitution::new_str(body.vars.iter().cloned().zip(nargs));
                    body.body.subst(&subst, env)
                } else {
                    env.app(f.clone(), nargs, sort.clone())
                }
            }
            ATerm::Let(bindings, body) => {
                let nbindings = bindings
                    .iter()
                    .map(|b| VarBinding(b.0.clone(), b.1, b.2.gsubst_preproc_impl(body_map, env)))
                    .collect();
                let nbody = body.gsubst_preproc_impl(body_map, env);
                env.let_term(nbindings, nbody)
            }
            ATerm::Exists(vs, body) => {
                let nbody = body.gsubst_preproc_impl(body_map, env);
                env.exists(vs.clone(), nbody)
            }
            ATerm::Forall(vs, body) => {
                let nbody = body.gsubst_preproc_impl(body_map, env);
                env.forall(vs.clone(), nbody)
            }
            ATerm::Matching(t, cases) => {
                let nt = t.gsubst_preproc_impl(body_map, env);
                let ncases = cases
                    .iter()
                    .map(|c| {
                        let nbody = c.body.gsubst_preproc_impl(body_map, env);
                        PatternArm {
                            pattern: c.pattern.clone(),
                            body: nbody,
                        }
                    })
                    .collect();
                env.matching(nt, ncases)
            }
            ATerm::Annotated(t, annos) => {
                let nt = t.gsubst_preproc_impl(body_map, env);
                let nannos = annos.gsubst_preproc_impl(body_map, env);
                env.annotated(nt, nannos)
            }
            ATerm::Eq(a, b) => {
                let na = a.gsubst_preproc_impl(body_map, env);
                let nb = b.gsubst_preproc_impl(body_map, env);
                env.eq(na, nb)
            }
            ATerm::Distinct(ts) => {
                let nts = ts.gsubst_preproc_impl(body_map, env);
                env.distinct(nts)
            }
            ATerm::And(ts) => {
                let nts = ts.gsubst_preproc_impl(body_map, env);
                env.and(nts)
            }
            ATerm::Or(ts) => {
                let nts = ts.gsubst_preproc_impl(body_map, env);
                env.or(nts)
            }
            ATerm::Xor(ts) => {
                let nts = ts.gsubst_preproc_impl(body_map, env);
                env.xor(nts)
            }
            ATerm::Implies(ts, concl) => {
                let nts = ts.gsubst_preproc_impl(body_map, env);
                let nconcl = concl.gsubst_preproc_impl(body_map, env);
                env.implies(nts, nconcl)
            }
            ATerm::Not(t) => {
                let nt = t.gsubst_preproc_impl(body_map, env);
                env.not(nt)
            }
            ATerm::Ite(c, t, e) => {
                let nc = c.gsubst_preproc_impl(body_map, env);
                let nt = t.gsubst_preproc_impl(body_map, env);
                let ne = e.gsubst_preproc_impl(body_map, env);
                env.ite(nc, nt, ne)
            }
        }
    }
}

fn find_dependencies_attribute(
    context: &mut Context,
    global_names: &HashSet<Str>,
    dependencies: &mut HashMap<Str, Vec<Str>>,
    block: &HashSet<Str>,
    current: &Attribute,
    acc: &mut Vec<Str>,
) {
    if let Attribute::Pattern(ts) = current {
        ts.iter()
            .for_each(|t| find_dependencies(context, global_names, dependencies, block, t, acc));
    }
}

fn find_dependencies(
    context: &mut Context,
    global_names: &HashSet<Str>,
    dependencies: &mut HashMap<Str, Vec<Str>>,
    block: &HashSet<Str>, // a subset of global_names; known dependencies of recursive definitions
    current: &Term,
    acc: &mut Vec<Str>,
) {
    match current.repr() {
        ATerm::Constant(_, _) | ATerm::Local(_) => {}
        ATerm::Global(qid, _) => {
            let sym = qid.id_str();
            if global_names.contains(sym) && !block.contains(sym) {
                acc.push(sym.clone());
            }
        }
        ATerm::App(f, args, _) => {
            args.iter().for_each(|a| {
                find_dependencies(context, global_names, dependencies, block, a, acc);
            });
            let sym = f.id_str();
            if global_names.contains(sym) && !block.contains(sym) {
                acc.push(sym.clone());
            }
        }
        ATerm::Let(bindings, body) => {
            bindings.iter().for_each(|b| {
                find_dependencies(context, global_names, dependencies, block, &b.2, acc);
            });
            find_dependencies(context, global_names, dependencies, block, body, acc);
        }
        ATerm::Exists(_, body) | ATerm::Forall(_, body) => {
            find_dependencies(context, global_names, dependencies, block, body, acc);
        }
        ATerm::Matching(t, cases) => {
            find_dependencies(context, global_names, dependencies, block, t, acc);
            cases.iter().for_each(|c| {
                find_dependencies(context, global_names, dependencies, block, &c.body, acc);
            })
        }
        ATerm::Annotated(t, annos) => {
            find_dependencies(context, global_names, dependencies, block, t, acc);
            annos.iter().for_each(|a| {
                find_dependencies_attribute(context, global_names, dependencies, block, a, acc)
            });
        }
        ATerm::Eq(a, b) => {
            find_dependencies(context, global_names, dependencies, block, a, acc);
            find_dependencies(context, global_names, dependencies, block, b, acc);
        }
        ATerm::Distinct(ts) | ATerm::And(ts) | ATerm::Or(ts) | ATerm::Xor(ts) => {
            ts.iter().for_each(|t| {
                find_dependencies(context, global_names, dependencies, block, t, acc);
            });
        }
        ATerm::Implies(ts, concl) => {
            ts.iter().for_each(|t| {
                find_dependencies(context, global_names, dependencies, block, t, acc);
            });
            find_dependencies(context, global_names, dependencies, block, concl, acc);
        }
        ATerm::Not(t) => find_dependencies(context, global_names, dependencies, block, t, acc),
        ATerm::Ite(c, t, e) => {
            find_dependencies(context, global_names, dependencies, block, c, acc);
            find_dependencies(context, global_names, dependencies, block, t, acc);
            find_dependencies(context, global_names, dependencies, block, e, acc);
        }
    }
}

fn build_dependencies(
    context: &mut Context,
    global_names: &HashSet<Str>,
) -> HashMap<Str, Vec<Str>> {
    let mut dependencies = HashMap::new();
    for name in global_names {
        if let Some(m) = context.get_definition(name).cloned() {
            let mut acc = vec![];
            find_dependencies(
                context,
                global_names,
                &mut dependencies,
                &m.rec_deps,
                &m.def.body,
                &mut acc,
            );
            dependencies.insert(name.clone(), acc);
        }
    }
    dependencies
}

fn do_build_body_map(
    context: &mut Context,
    dependencies: &HashMap<Str, Vec<Str>>,
    body_map: &mut HashMap<Str, FuncBody>,
    scanned: &mut HashSet<Str>,
    name: &Str,
) {
    if scanned.contains(name) {
        return;
    }
    scanned.insert(name.clone());
    let meta_data = if let Some(m) = context.get_definition(name) {
        let vars = m.def.vars.iter().map(|v| v.0.clone()).collect();
        Some((vars, m.def.body.clone()))
    } else {
        None
    };
    // we neet to split this because of the borrow checker
    if let Some((vars, body)) = meta_data {
        // we must have the dependencies
        let deps = dependencies
            .get(name)
            .expect("fatal algorithmic mistake in build_body_map!");
        for dep in deps {
            do_build_body_map(context, dependencies, body_map, scanned, dep);
        }
        // at this point, body_map contains unfolding of all transitive dependencies
        let body = body.gsubst_preproc_impl(body_map, context);
        body_map.insert(name.clone(), FuncBody { vars, body });
    }
}

fn build_body_map(context: &mut Context, global_names: &HashSet<Str>) -> HashMap<Str, FuncBody> {
    let mut body_map = HashMap::new();
    let dependencies = build_dependencies(context, global_names);
    let mut scanned = HashSet::new();
    for name in global_names {
        do_build_body_map(context, &dependencies, &mut body_map, &mut scanned, name);
    }
    body_map
}

trait GlobalSubstInplaceImpl<E> {
    fn gsubst_inplace_impl(
        &self,
        global_names: &HashSet<Str>,
        block: &HashSet<Str>,
        env: &mut E,
        cache: &mut HashMap<Str, FuncBody>,
    ) -> Self;
}

impl<T, E> GlobalSubstInplaceImpl<E> for Vec<T>
where
    T: GlobalSubstInplaceImpl<E>,
{
    fn gsubst_inplace_impl(
        &self,
        global_names: &HashSet<Str>,
        block: &HashSet<Str>,
        env: &mut E,
        cache: &mut HashMap<Str, FuncBody>,
    ) -> Self {
        self.iter()
            .map(|v| v.gsubst_inplace_impl(global_names, block, env, cache))
            .collect()
    }
}

impl GlobalSubstInplaceImpl<Context> for Attribute {
    fn gsubst_inplace_impl(
        &self,
        global_names: &HashSet<Str>,
        block: &HashSet<Str>,
        env: &mut Context,
        cache: &mut HashMap<Str, FuncBody>,
    ) -> Self {
        if let Attribute::Pattern(ts) = self {
            Attribute::Pattern(ts.gsubst_inplace_impl(global_names, block, env, cache))
        } else {
            self.clone()
        }
    }
}

impl GlobalSubstInplaceImpl<Context> for Term {
    fn gsubst_inplace_impl(
        &self,
        global_names: &HashSet<Str>,
        block: &HashSet<Str>,
        env: &mut Context,
        cache: &mut HashMap<Str, FuncBody>,
    ) -> Self {
        match self.repr() {
            ATerm::Constant(_, _) | ATerm::Local(_) => self.clone(),
            ATerm::Global(qid, _) => {
                let sym = qid.id_str();
                if global_names.contains(sym)
                    && !block.contains(sym)
                    && let Some(def) = env.get_definition(sym).cloned()
                {
                    let ret =
                        def.def
                            .body
                            .gsubst_inplace_impl(global_names, &def.rec_deps, env, cache);
                    cache.insert(
                        sym.clone(),
                        FuncBody {
                            vars: vec![],
                            body: ret.clone(),
                        },
                    );
                    ret
                } else {
                    self.clone()
                }
            }
            ATerm::App(f, args, sort) => {
                let nargs = args
                    .iter()
                    .map(|a| a.gsubst_inplace_impl(global_names, block, env, cache))
                    .collect();
                let sym = f.id_str();
                if global_names.contains(sym)
                    && !block.contains(sym)
                    && let Some(def) = env.get_definition(sym).cloned()
                {
                    let subst =
                        Substitution::new_str(def.def.vars.iter().map(|v| v.0.clone()).zip(nargs));
                    let ret =
                        def.def
                            .body
                            .gsubst_inplace_impl(global_names, &def.rec_deps, env, cache);
                    cache.insert(
                        sym.clone(),
                        FuncBody {
                            vars: def.def.vars.into_iter().map(|v| v.0).collect(),
                            body: ret.clone(),
                        },
                    );
                    ret.subst(&subst, env)
                } else {
                    env.arena.app(f.clone(), nargs, sort.clone())
                }
            }
            ATerm::Let(bindings, body) => {
                let nbindings = bindings
                    .iter()
                    .map(|b| {
                        VarBinding(
                            b.0.clone(),
                            b.1,
                            b.2.gsubst_inplace_impl(global_names, block, env, cache),
                        )
                    })
                    .collect();
                let nbody = body.gsubst_inplace_impl(global_names, block, env, cache);
                env.let_term(nbindings, nbody)
            }
            ATerm::Exists(vs, body) => {
                let nbody = body.gsubst_inplace_impl(global_names, block, env, cache);
                env.exists(vs.clone(), nbody)
            }
            ATerm::Forall(vs, body) => {
                let nbody = body.gsubst_inplace_impl(global_names, block, env, cache);
                env.forall(vs.clone(), nbody)
            }
            ATerm::Matching(t, cases) => {
                let nt = t.gsubst_inplace_impl(global_names, block, env, cache);
                let ncases = cases
                    .iter()
                    .map(|c| PatternArm {
                        pattern: c.pattern.clone(),
                        body: c.body.gsubst_inplace_impl(global_names, block, env, cache),
                    })
                    .collect();
                env.matching(nt, ncases)
            }
            ATerm::Annotated(t, annos) => {
                let nt = t.gsubst_inplace_impl(global_names, block, env, cache);
                let nannos = annos.gsubst_inplace_impl(global_names, block, env, cache);
                env.annotated(nt, nannos)
            }
            ATerm::Eq(a, b) => {
                let na = a.gsubst_inplace_impl(global_names, block, env, cache);
                let nb = b.gsubst_inplace_impl(global_names, block, env, cache);
                env.eq(na, nb)
            }
            ATerm::Distinct(ts) => {
                let nts = ts.gsubst_inplace_impl(global_names, block, env, cache);
                env.distinct(nts)
            }
            ATerm::And(ts) => {
                let nts = ts.gsubst_inplace_impl(global_names, block, env, cache);
                env.and(nts)
            }
            ATerm::Or(ts) => {
                let nts = ts.gsubst_inplace_impl(global_names, block, env, cache);
                env.or(nts)
            }
            ATerm::Xor(ts) => {
                let nts = ts.gsubst_inplace_impl(global_names, block, env, cache);
                env.xor(nts)
            }
            ATerm::Implies(ts, concl) => {
                let nts = ts.gsubst_inplace_impl(global_names, block, env, cache);
                let nconcl = concl.gsubst_inplace_impl(global_names, block, env, cache);
                env.implies(nts, nconcl)
            }
            ATerm::Not(t) => {
                let nt = t.gsubst_inplace_impl(global_names, block, env, cache);
                env.not(nt)
            }
            ATerm::Ite(c, t, e) => {
                let nc = c.gsubst_inplace_impl(global_names, block, env, cache);
                let nt = t.gsubst_inplace_impl(global_names, block, env, cache);
                let ne = e.gsubst_inplace_impl(global_names, block, env, cache);
                env.ite(nc, nt, ne)
            }
        }
    }
}
