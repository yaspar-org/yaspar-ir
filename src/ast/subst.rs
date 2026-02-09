// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! This module handles the substitution operation

use crate::allocator::TermAllocator;
use crate::ast::alg::VarBinding;
use crate::ast::{ATerm, Arena, Attribute, HasArena, HasArenaAlt, PatternArm, Str, Term};
use crate::locenv::MemLinkedList;
use crate::traits::{AllocatableString, Repr};
use std::collections::HashMap;

/// a substitution object
pub struct Substitution(HashMap<Str, Option<Term>>);

impl Substitution {
    pub fn empty() -> Substitution {
        Substitution(HashMap::new())
    }

    pub fn new_str(bindings: impl IntoIterator<Item = (Str, Term)>) -> Substitution {
        let map = bindings.into_iter().map(|(s, t)| (s, Some(t))).collect();
        Substitution(map)
    }

    pub fn new<S, E>(bindings: impl IntoIterator<Item = (S, Term)>, env: &mut E) -> Substitution
    where
        S: AllocatableString<Arena>,
        E: HasArena,
    {
        Self::new_str(
            bindings
                .into_iter()
                .map(|(s, t)| (s.allocate(env.arena()), t)),
        )
    }

    /// Push one more binding to the substitution
    ///
    /// c.f. [Self::extend]
    pub fn push(&mut self, name: Str, term: Term) {
        self.0.insert(name, Some(term));
    }

    /// Push multiple bindings to the substitution
    ///
    /// c.f. [Self::push]
    pub fn extend(&mut self, bindings: impl IntoIterator<Item = (Str, Term)>) {
        for (name, term) in bindings {
            self.0.insert(name, Some(term));
        }
    }
}

impl Default for Substitution {
    fn default() -> Substitution {
        Substitution::empty()
    }
}

/// Apply a substitution to `Self`.
///
/// Note that it is the caller's responsibility to maintain well-sortedness invariance.
pub trait Substitute<E> {
    fn subst(&self, subst: &Substitution, env: &mut E) -> Self;
}

/// A stack of substitutions to handle shadowing
type SubstList<'a> = MemLinkedList<'a, Substitution>;

impl SubstList<'_> {
    fn lookup(&self, x: &Str) -> Option<Term> {
        match self {
            SubstList::Nil => None,
            SubstList::Cons { car, cdr } => {
                if let Some(t) = car.0.get(x) {
                    t.clone()
                } else {
                    cdr.lookup(x)
                }
            }
        }
    }
}

trait SubstituteImpl<E> {
    fn subst_impl(&self, substs: &SubstList, env: &mut E) -> Self;
}

impl<E, X> Substitute<E> for X
where
    E: HasArenaAlt,
    X: SubstituteImpl<E>,
{
    fn subst(&self, subst: &Substitution, env: &mut E) -> Self {
        self.subst_impl(
            &SubstList::Cons {
                car: subst,
                cdr: &SubstList::Nil,
            },
            env,
        )
    }
}

impl<E, T> SubstituteImpl<E> for Vec<T>
where
    E: HasArenaAlt,
    T: SubstituteImpl<E>,
{
    fn subst_impl(&self, substs: &SubstList, env: &mut E) -> Self {
        self.iter().map(|a| a.subst_impl(substs, env)).collect()
    }
}

impl<E> SubstituteImpl<E> for Attribute
where
    E: HasArenaAlt,
{
    fn subst_impl(&self, substs: &SubstList, env: &mut E) -> Self {
        match self {
            Attribute::Pattern(t) => Attribute::Pattern(t.subst_impl(substs, env)),
            _ => self.clone(),
        }
    }
}

fn subst_binder_shadow<V, E>(
    vars: &[V],
    body: &Term,
    substs: &SubstList,
    env: &mut E,
    f: impl Fn(&V) -> Str,
) -> Term
where
    E: HasArenaAlt,
{
    let shadow = vars.iter().map(|v| (f(v), None)).collect();
    let subst = Substitution(shadow);
    body.subst_impl(
        &SubstList::Cons {
            car: &subst,
            cdr: substs,
        },
        env,
    )
}

impl<E> SubstituteImpl<E> for Term
where
    E: HasArenaAlt,
{
    fn subst_impl(&self, substs: &SubstList, env: &mut E) -> Self {
        match self.repr() {
            ATerm::Constant(_, _) | ATerm::Global(_, _) => self.clone(),
            ATerm::Local(var) => {
                if let Some(t) = substs.lookup(&var.symbol) {
                    t
                } else {
                    self.clone()
                }
            }
            ATerm::App(f, args, s) => {
                let nargs = args.subst_impl(substs, env);
                env.arena_alt().app(f.clone(), nargs, s.clone())
            }
            ATerm::Let(bindings, body) => {
                let nbindings = bindings
                    .iter()
                    .map(|b| VarBinding(b.0.clone(), b.1, b.2.subst_impl(substs, env)))
                    .collect();
                let nbody = subst_binder_shadow(bindings, body, substs, env, |v| v.0.clone());
                env.arena_alt().let_term(nbindings, nbody)
            }
            ATerm::Exists(vars, body) => {
                let nbody = subst_binder_shadow(vars, body, substs, env, |v| v.0.clone());
                env.arena_alt().exists(vars.clone(), nbody)
            }
            ATerm::Forall(vars, body) => {
                let nbody = subst_binder_shadow(vars, body, substs, env, |v| v.0.clone());
                env.arena_alt().forall(vars.clone(), nbody)
            }
            ATerm::Matching(t, cases) => {
                let nt = t.subst_impl(substs, env);
                let ncases = cases
                    .iter()
                    .map(|c| {
                        let nbody = subst_binder_shadow(
                            &c.pattern.variables(),
                            &c.body,
                            substs,
                            env,
                            |v| Str::clone(v),
                        );
                        PatternArm {
                            pattern: c.pattern.clone(),
                            body: nbody,
                        }
                    })
                    .collect();
                env.arena_alt().matching(nt, ncases)
            }
            ATerm::Annotated(t, annos) => {
                let nt = t.subst_impl(substs, env);
                let nannos = annos.subst_impl(substs, env);
                env.arena_alt().annotated(nt, nannos)
            }
            ATerm::Eq(a, b) => {
                let na = a.subst_impl(substs, env);
                let nb = b.subst_impl(substs, env);
                env.arena_alt().eq(na, nb)
            }
            ATerm::Distinct(ts) => {
                let nts = ts.subst_impl(substs, env);
                env.arena_alt().distinct(nts)
            }
            ATerm::And(ts) => {
                let nts = ts.subst_impl(substs, env);
                env.arena_alt().and(nts)
            }
            ATerm::Or(ts) => {
                let nts = ts.subst_impl(substs, env);
                env.arena_alt().or(nts)
            }
            ATerm::Implies(ts, concl) => {
                let nts = ts.subst_impl(substs, env);
                let concl = concl.subst_impl(substs, env);
                env.arena_alt().implies(nts, concl)
            }
            ATerm::Not(t) => {
                let nt = t.subst_impl(substs, env);
                env.arena_alt().not(nt)
            }
            ATerm::Ite(c, t, e) => {
                let nc = c.subst_impl(substs, env);
                let nt = t.subst_impl(substs, env);
                let ne = e.subst_impl(substs, env);
                env.arena_alt().ite(nc, nt, ne)
            }
        }
    }
}
