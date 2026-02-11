// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! This module implements the implicant computation algorithm
//!
//! It computes an iteration of implicant based on the boolean skeleton of a term.
//!
//! This module depends on [crate::ast::cnf] and requires the feature `implicant-generation`.

use crate::ast::cnf::CNFCache;
use crate::ast::{ATerm, Arena, FlatConnectivesExt, Term};
use crate::traits::Repr;
use sat_interface::{Clause, SatSolver, SolverState};
use std::collections::HashSet;

/// A trait that characterizes what a model should do:
///
/// 1. It should be able to evaluate a term to a boolean;
/// 2. Remember which clause to block.
pub trait Model {
    /// Evaluates the truth of a given term.
    ///
    /// It returns a bool in case the evaluation is not successful.
    fn evaluate(&mut self, t: &Term) -> Option<bool>;
    /// Block a given term in the model
    fn block(&mut self, t: &Term);
}

/// Helpers for finding one implicant
///
/// An implicant for a formula phi is a formula that implies phi.
///
/// Assume let-eliminated and nnf.
trait FindImplicantImpl<Env, Model> {
    fn find_one_implicant_impl(&self, env: Env, model: &mut Model, block: bool) -> Self;
}

impl<M> FindImplicantImpl<&mut Arena, M> for Term
where
    M: Model,
{
    fn find_one_implicant_impl(&self, env: &mut Arena, model: &mut M, block: bool) -> Self {
        match self.repr() {
            ATerm::Annotated(t, _) => t.find_one_implicant_impl(&mut *env, model, block),
            ATerm::And(ts) => {
                let nts = ts
                    .iter()
                    .map(|t| t.find_one_implicant_impl(&mut *env, model, block))
                    .collect();
                env.flat_and(nts)
            }
            ATerm::Or(ts) => ts
                .iter()
                .find(|t| model.evaluate(t).unwrap()) // there must be a result due to the CNF conversion
                .unwrap()
                .find_one_implicant_impl(&mut *env, model, true),

            // the only possibility for reducing the size of the original formula is the `or` case.
            // In this case, we rely on the model to find out the first sub-formula that is true.

            // we make this case explicit, because we assume negative normal form, so there really
            // isn't much to do here other than cloning.
            ATerm::Not(t) => {
                if block {
                    model.block(t);
                }
                self.clone()
            }
            _ => {
                if block {
                    model.block(self);
                }
                self.clone()
            }
        }
    }
}

impl<M> FindImplicantImpl<&mut Arena, M> for Vec<Term>
where
    M: Model,
{
    fn find_one_implicant_impl(&self, env: &mut Arena, model: &mut M, block: bool) -> Self {
        // the implementation removes duplicated implicants, i.e. only one copy is kept.

        let mut result = vec![];
        let mut existing_id = HashSet::new();
        let mut insert = |t: Term| {
            if existing_id.insert(t.uid()) {
                result.push(t);
            }
        };
        for t in self {
            let ti = t.find_one_implicant_impl(&mut *env, model, block);
            match ti.repr() {
                ATerm::And(ts) => {
                    for t in ts {
                        insert(t.clone());
                    }
                }
                _ => insert(ti),
            }
        }
        result
    }
}
struct SatState<'a, 'b, Solver> {
    solver: &'a mut Solver,
    cache: &'b CNFCache,
    blocking_literals: HashSet<i32>,
}

impl<Solver> Model for SatState<'_, '_, Solver>
where
    Solver: SatSolver,
{
    fn evaluate(&mut self, t: &Term) -> Option<bool> {
        let i = self.cache.var_map.get(&t.uid())?;
        let r = self.solver.val(*i);
        Some(r)
    }

    fn block(&mut self, t: &Term) {
        let i = self.cache.var_map.get(&t.uid()).unwrap();
        let r = self.solver.val(*i);
        self.blocking_literals.insert(if r { -*i } else { *i });
    }
}

/// Find one implicant of `self`, assuming `self` is in NNF and let-eliminated.
pub trait FindImplicant<Env, Solver>
where
    Self: Sized,
    Solver: SatSolver,
{
    /// When result is None, it means there is no more implicant.
    /// When result is an error, it means the sat solver cannot produce an implicant.
    /// Otherwise, we obtain one implicant.
    fn find_one_implicant(&self, env: Env, solver: &mut Solver)
    -> Option<crate::ast::Result<Self>>;
}

pub(crate) struct ImplicantEnv<'a> {
    pub arena: &'a mut Arena,
    pub cnf_cache: &'a CNFCache,
}

impl<'a, Solver> FindImplicant<ImplicantEnv<'a>, Solver> for Vec<Term>
where
    Solver: SatSolver,
{
    fn find_one_implicant(
        &self,
        env: ImplicantEnv<'a>,
        solver: &mut Solver,
    ) -> Option<crate::ast::Result<Self>> {
        let status = solver.solve();
        if status.is_unsat() {
            None
        } else if status.is_unknown() {
            Some(Err("Implicant: SAT returns unknown!".into()))
        } else {
            let mut state = SatState {
                solver,
                cache: env.cnf_cache,
                blocking_literals: HashSet::new(),
            };
            let result = self.find_one_implicant_impl(env.arena, &mut state, false);
            let blocking_clause = Clause::new(state.blocking_literals.iter().cloned().collect());
            solver.insert(&blocking_clause);
            Some(Ok(result))
        }
    }
}

/// An iterator that iterates over the implements of `T`
pub trait ImplicantIterator<T>: Iterator<Item = crate::ast::Result<T>> {
    /// Block `item` in the implicants. Useful when `item` is an unsat core.
    fn block(&mut self, item: &T);
}

pub(crate) struct ImplicantEnumerator<'a, 'b, Solver, T> {
    pub arena: &'b mut Arena,
    pub solver: &'a mut Solver,
    pub cache: &'b CNFCache,
    pub nnf: T,
    pub finished: bool,
}

impl<Solver, T> Iterator for ImplicantEnumerator<'_, '_, Solver, T>
where
    Solver: SatSolver,
    T: for<'c> FindImplicant<ImplicantEnv<'c>, Solver>,
{
    type Item = crate::ast::Result<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }
        let implicant = self.nnf.find_one_implicant(
            ImplicantEnv {
                arena: self.arena,
                cnf_cache: self.cache,
            },
            self.solver,
        );
        match &implicant {
            None => {
                self.finished = true;
            }
            Some(Err(_)) => {
                self.finished = true;
            }
            &Some(Ok(_)) => {}
        }
        implicant
    }
}

impl<Solver> ImplicantIterator<Vec<Term>> for ImplicantEnumerator<'_, '_, Solver, Vec<Term>>
where
    Solver: SatSolver,
{
    fn block(&mut self, item: &Vec<Term>) {
        let vars = item
            .iter()
            .flat_map(|t| self.cache.var_map.get(&t.uid()).map(|i| -*i))
            .collect();
        self.solver.insert(&Clause::new(vars));
    }
}
