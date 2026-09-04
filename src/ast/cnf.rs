// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! NNF (Negation Normal Form) and CNF (Conjunctive Normal Form) conversion algorithms.
//!
//! This module provides the [`CNFConversion`] trait with three operations:
//!
//! - `nnf(env)` — convert a Boolean term to Negation Normal Form (negations pushed to literals).
//! - `cnf(env)` — convert to a SAT [`Formula`] in CNF.
//! - `cnf_tseitin(env)` — convert to CNF using the Tseitin transformation for a bidirectional
//!   (equisatisfiable) encoding, which avoids exponential blowup.
//!
//! Best used after let-elimination. Inputs must have sort `Bool`.
//!
//! Requires the `cnf` feature flag.

use crate::ast::{
    AConstant, ATerm, Arena, FetchSort, FlatConnectivesExt, ObjectAllocatorExt, Term, TermAllocator,
};
use crate::traits::Repr;
use sat_interface::{Clause, Formula};
use std::collections::HashMap;
use yaspar_macros::stack_safe;

/// This trait implements the conjunctive normal form (CNF) conversion from [Self] to a formula.
///
/// Better invoke after let-elimination; assume inputs have sort Bool.
pub trait CNFConversion<Env> {
    /// This function converts [Self] to a boolean SAT CNF formula
    fn cnf(&self, env: Env) -> Formula;
    /// This function converts [Self] to a boolean SAT CNF formula
    /// using the tseitin transformation, i.e. it provides a bidirectional
    /// encoding (by calling cnf_nnf_tseitin) unlike cnf
    fn cnf_tseitin(&self, env: Env) -> Formula;
    /// This function converts [Self] to its negative normal form (NNF)
    ///
    /// The NNF conversion should preserve the satisfiability of [Self]
    fn nnf(&self, env: Env) -> Self;
}

/// The data structure for the states required for both CNF and NNF transformations
pub struct CNFCache {
    pub var_map: HashMap<u64, i32>,
    pub var_map_reverse: HashMap<i32, u64>,
    pub next_var: i32,                              // always positive
    pub nnf_cache: HashMap<u64, [Option<Term>; 2]>, // it is an array of 2 because of polarity below.
}

impl CNFCache {
    pub(crate) fn new() -> Self {
        Self {
            var_map: HashMap::new(),
            var_map_reverse: HashMap::new(),
            next_var: 1, // in this way, we make sure that [next_var] is always positive
            nnf_cache: HashMap::new(),
        }
    }
}

pub(crate) struct CNFEnv<'a> {
    pub arena: &'a mut Arena,
    pub cache: &'a mut CNFCache,
}

impl CNFEnv<'_> {
    fn new_var(&mut self) -> i32 {
        let v = self.cache.next_var;
        if v == i32::MAX {
            panic!("Too many boolean variables; reached i32::MAX!");
        }
        self.cache.next_var += 1;
        v
    }
}

/// This is a private helper trait to implement CNF conversion.
///
/// The CNF conversion of a formula can be achieved in two steps implemented by this trait.
///
/// This trait assumes terms have been type-checked and let-eliminated.
trait CNFConversionHelper<Env> {
    /// This function computes the negative normal forms of the given formula
    ///
    /// If `polarity` is true, then the function returns an NNF that is equivalent to the input;
    /// if `!polarity`, then the return value is an NNF that negates the input.
    fn nnf_impl(&self, env: Env, polarity: bool) -> Self;

    /// This function computes the variable representing the given term and updates the `formula`
    /// if necessary.
    fn cnf_nnf(&self, env: Env, formula: &mut Formula) -> i32;

    /// This function computes the variable representing the given term and updates the `formula`
    /// if necessary using the Tseitin transformation
    fn cnf_nnf_tseitin(&self, env: Env, formula: &mut Formula) -> i32;
}

impl CNFConversionHelper<&mut CNFEnv<'_>> for Term {
    fn nnf_impl(&self, env: &mut CNFEnv<'_>, polarity: bool) -> Self {
        nnf_of(self, env, polarity)
    }

    fn cnf_nnf(&self, env: &mut CNFEnv<'_>, formula: &mut Formula) -> i32 {
        pg_of(self, env, formula)
    }

    fn cnf_nnf_tseitin(&self, env: &mut CNFEnv<'_>, formula: &mut Formula) -> i32 {
        tseitin_of(self, env, formula)
    }
}

/// The three conversions, as free functions rather than trait methods: each recurses over a term of
/// unbounded depth, and `#[stack_safe]` needs the rewritten body beside the member, which a trait
/// impl has no room for. Recursing here also stays out of trait dispatch, so a nested call re-enters
/// the driver instead of starting a new one.
#[stack_safe(data_in_frame)]
mod convert {
    use super::*;

    /// The body of [`CNFConversionHelper::nnf_impl`].
    pub(super) fn nnf_of(this: &Term, env: &mut CNFEnv<'_>, polarity: bool) -> Term {
        // this function implements two things:
        // 1. it performs some immediate simplifications to extract the basic boolean skeleton from the formula
        // 2. it then performs NNF transformation.

        // index in the cache array
        let idx = if polarity { 1 } else { 0 };
        // cache lookup; return early if cache is hit.
        if let Some(r) = &env
            .cache
            .nnf_cache
            .entry(this.uid())
            .or_insert_with(|| [None, None])[idx]
        {
            return r.clone();
        }

        let r = match this.repr() {
            ATerm::Annotated(t, _) => nnf_of(t, env, polarity), // omit attributes
            ATerm::Eq(a, b) => {
                // 1. check if it's comparing two booleans
                let bs = env.arena.bool_sort();
                let sa = a.get_sort(env.arena);
                if sa != bs {
                    // 2. if not, then we regard a = b as an atom
                    if polarity {
                        this.clone()
                    } else {
                        env.arena.not(this.clone())
                    }
                } else {
                    // 2. if so, then we convert a = b to a <=> b
                    let not_a = env.arena.not(a.clone());
                    let not_b = env.arena.not(b.clone());
                    let a_i_b = env.arena.flat_or(vec![not_a, b.clone()]);
                    let b_i_a = env.arena.flat_or(vec![not_b, a.clone()]);
                    let eqf: Term = env.arena.flat_and(vec![a_i_b, b_i_a]);
                    nnf_of(&eqf, env, polarity)
                }
            }
            ATerm::Distinct(ts) => {
                // we know from parsing that ts is non-empty.
                let bs = env.arena.bool_sort();
                let s = ts[0].get_sort(env.arena);
                match ts.len() {
                    1 => {
                        // a single term is always distinct
                        let t: Term = env.arena.get_true();
                        nnf_of(&t, env, polarity)
                    }
                    2 => {
                        // If there are two terms, then they must be unequal
                        let eq = env.arena.eq(ts[0].clone(), ts[1].clone());
                        let eqf: Term = env.arena.not(eq);
                        nnf_of(&eqf, env, polarity)
                    }
                    _ => {
                        // If the terms are booleans, then more than two terms cannot be distinct
                        if bs == s {
                            let f: Term = env.arena.get_false();
                            nnf_of(&f, env, polarity)
                        } else {
                            // Otherwise, we treat the whole Distinct term as atomic
                            if polarity {
                                this.clone()
                            } else {
                                env.arena.not(this.clone())
                            }
                        }
                    }
                }
            }
            ATerm::Constant(AConstant::Bool(b), _) => {
                if polarity {
                    this.clone()
                } else {
                    env.arena.bool(!*b)
                }
            }
            ATerm::And(ts) => {
                match ts.len() {
                    0 => {
                        let t: Term = env.arena.get_true();
                        nnf_of(&t, env, polarity)
                    }
                    1 => nnf_of(&ts[0], env, polarity),
                    _ => {
                        let mut nts: Vec<Term> = Vec::with_capacity(ts.len());
                        let mut i = 0usize;
                        while i < ts.len() {
                            nts.push(nnf_of(&ts[i], env, polarity));
                            i += 1;
                        }
                        if polarity {
                            env.arena.flat_and(nts)
                        } else {
                            // notice that `(not (and a b))` is `(or (not a) (not b))`
                            env.arena.flat_or(nts)
                        }
                    }
                }
            }
            ATerm::Or(ts) => {
                match ts.len() {
                    0 => {
                        let f: Term = env.arena.get_false();
                        nnf_of(&f, env, polarity)
                    }
                    1 => nnf_of(&ts[0], env, polarity),
                    _ => {
                        let mut nts: Vec<Term> = Vec::with_capacity(ts.len());
                        let mut i = 0usize;
                        while i < ts.len() {
                            nts.push(nnf_of(&ts[i], env, polarity));
                            i += 1;
                        }
                        if polarity {
                            env.arena.flat_or(nts)
                        } else {
                            // notice that `(not (or a b))` is `(and (not a) (not b))`
                            env.arena.flat_and(nts)
                        }
                    }
                }
            }
            ATerm::Implies(ts, b) => {
                // notice `(=> a1 a2 ... an b)` is `(or (not a1) ... (not an) b)`
                let mut nts: Vec<Term> = Vec::with_capacity(ts.len() + 1);
                let mut i = 0usize;
                while i < ts.len() {
                    nts.push(nnf_of(&ts[i], env, !polarity));
                    i += 1;
                }
                let nb = nnf_of(b, env, polarity);
                nts.push(nb);
                if polarity {
                    env.arena.flat_or(nts)
                } else {
                    env.arena.flat_and(nts)
                }
            }
            ATerm::Not(t) => nnf_of(t, env, !polarity),
            ATerm::Ite(b, t, e) => {
                // notice `(ite b t e)` is `(or (and b t) (and (not b) e))`
                let not_b = env.arena.not(b.clone());
                let bt = env.arena.flat_and(vec![b.clone(), t.clone()]);
                let not_b_e = env.arena.flat_and(vec![not_b, e.clone()]);
                let eqf: Term = env.arena.flat_or(vec![bt, not_b_e]);
                nnf_of(&eqf, env, polarity)
            }
            _ => {
                // all other cases are regarded as atoms.
                if polarity {
                    this.clone()
                } else {
                    env.arena.not(this.clone())
                }
            }
        };
        // unwrap is safe here because we know we've inserted the array at the beginning.
        env.cache.nnf_cache.get_mut(&this.uid()).unwrap()[idx] = Some(r.clone());
        if polarity {
            // if polarity is positive, then we know nnf is idempotent, i.e. nnf of nnf gives the same nnf.
            // therefore, we can just update the cache to reflect this fact to save some compute
            let arr = env.cache.nnf_cache.entry(r.uid()).or_insert([None, None]);
            arr[1] = Some(r.clone());
        }
        r
    }

    /// The body of [`CNFConversionHelper::cnf_nnf`].
    pub(super) fn pg_of(this: &Term, env: &mut CNFEnv<'_>, formula: &mut Formula) -> i32 {
        // cache lookup
        if let Some(i) = env.cache.var_map.get(&this.uid()) {
            return *i;
        }

        let v = match this.repr() {
            ATerm::Constant(AConstant::Bool(b), _) => {
                let v = env.new_var();
                if *b {
                    // the CNF of true is just a fresh variable; there is no need to change the formula.
                    v
                } else {
                    formula.add(Clause::single(-v));
                    v
                }
            }
            ATerm::And(ts) => match ts.len() {
                0 => {
                    // (and) is just true.
                    let t: Term = env.arena.get_true();
                    pg_of(&t, env, formula)
                }
                1 => pg_of(&ts[0], env, formula), // (and a) is just a.
                _ => {
                    let nv = env.new_var();
                    let mut vs: Vec<i32> = Vec::with_capacity(ts.len());
                    let mut i = 0usize;
                    while i < ts.len() {
                        vs.push(pg_of(&ts[i], env, formula));
                        i += 1;
                    }
                    let mut j = 0usize;
                    while j < vs.len() {
                        formula.add(Clause::new(vec![vs[j], -nv]));
                        j += 1;
                    }
                    nv
                }
            },
            ATerm::Or(ts) => match ts.len() {
                0 => {
                    // (or) is just false.
                    let f: Term = env.arena.get_false();
                    pg_of(&f, env, formula)
                }
                1 => pg_of(&ts[0], env, formula), // (or a) is just a.
                _ => {
                    let nv = env.new_var();
                    let mut vs: Vec<i32> = Vec::with_capacity(ts.len() + 1);
                    let mut i = 0usize;
                    while i < ts.len() {
                        vs.push(pg_of(&ts[i], env, formula));
                        i += 1;
                    }
                    vs.push(-nv);
                    formula.add(Clause::new(vs));
                    nv
                }
            },
            ATerm::Not(t) => -pg_of(t, env, formula),
            _ => env.new_var(),
        };
        env.cache.var_map.insert(this.uid(), v);
        env.cache.var_map_reverse.insert(v, this.uid());
        v
    }

    /// The body of [`CNFConversionHelper::cnf_nnf_tseitin`].
    pub(super) fn tseitin_of(this: &Term, env: &mut CNFEnv<'_>, formula: &mut Formula) -> i32 {
        // cache lookup
        if let Some(i) = env.cache.var_map.get(&this.uid()) {
            return *i;
        }

        let v = match this.repr() {
            ATerm::Constant(AConstant::Bool(b), _) => {
                let v = env.new_var();
                if *b {
                    // the CNF of true is just a fresh variable; there is no need to change the formula.
                    v
                } else {
                    formula.add(Clause::single(-v));
                    v
                }
            }
            ATerm::And(ts) => match ts.len() {
                0 => {
                    // (and) is just true.
                    let t: Term = env.arena.get_true();
                    tseitin_of(&t, env, formula)
                }
                1 => tseitin_of(&ts[0], env, formula), // (and a) is just a.
                _ => {
                    let nv = env.new_var();
                    let mut vs: Vec<i32> = Vec::with_capacity(ts.len());
                    let mut i = 0usize;
                    while i < ts.len() {
                        vs.push(tseitin_of(&ts[i], env, formula));
                        i += 1;
                    }
                    let mut j = 0usize;
                    while j < vs.len() {
                        formula.add(Clause::new(vec![vs[j], -nv]));
                        j += 1;
                    }
                    let mut nvs: Vec<i32> = Vec::with_capacity(vs.len() + 1);
                    let mut k = 0usize;
                    while k < vs.len() {
                        nvs.push(-vs[k]);
                        k += 1;
                    }
                    nvs.push(nv);
                    formula.add(Clause::new(nvs));
                    nv
                }
            },
            ATerm::Or(ts) => match ts.len() {
                0 => {
                    // (or) is just false.
                    let f: Term = env.arena.get_false();
                    tseitin_of(&f, env, formula)
                }
                1 => tseitin_of(&ts[0], env, formula), // (or a) is just a.
                _ => {
                    let nv = env.new_var();
                    let mut vs: Vec<i32> = Vec::with_capacity(ts.len() + 1);
                    let mut i = 0usize;
                    while i < ts.len() {
                        vs.push(tseitin_of(&ts[i], env, formula));
                        i += 1;
                    }
                    let mut j = 0usize;
                    while j < vs.len() {
                        formula.add(Clause::new(vec![-vs[j], nv]));
                        j += 1;
                    }
                    vs.push(-nv);
                    formula.add(Clause::new(vs));
                    nv
                }
            },
            ATerm::Not(t) => -tseitin_of(t, env, formula),
            _ => env.new_var(),
        };
        env.cache.var_map.insert(this.uid(), v);
        env.cache.var_map_reverse.insert(v, this.uid());
        v
    }
}

impl CNFConversion<&mut CNFEnv<'_>> for Term {
    fn cnf(&self, env: &mut CNFEnv<'_>) -> Formula {
        // CNF conversion is implemented by chaining first NNF and then PG transformation.
        let nnf = self.nnf(&mut *env);
        let mut formula = Formula::empty();
        let v = nnf.cnf_nnf(env, &mut formula);
        formula.add(Clause::single(v));
        formula
    }

    fn cnf_tseitin(&self, env: &mut CNFEnv<'_>) -> Formula {
        // CNF conversion is implemented by chaining first NNF and then Tseitin transformation.
        let nnf = self.nnf(&mut *env);
        let mut formula = Formula::empty();
        let v = nnf.cnf_nnf_tseitin(env, &mut formula);
        formula.add(Clause::single(v));
        formula
    }

    fn nnf(&self, env: &mut CNFEnv<'_>) -> Self {
        self.nnf_impl(env, true)
    }
}

impl CNFConversion<&mut CNFEnv<'_>> for Vec<Term> {
    fn cnf(&self, env: &mut CNFEnv<'_>) -> Formula {
        let mut formula = Formula::empty();
        let nnfs = self.nnf(&mut *env);
        let lits = nnfs
            .iter()
            .map(|t| t.cnf_nnf(env, &mut formula))
            .collect::<Vec<_>>();
        for l in lits {
            formula.add(Clause::single(l));
        }
        formula
    }

    fn cnf_tseitin(&self, env: &mut CNFEnv<'_>) -> Formula {
        let mut formula = Formula::empty();
        let nnfs = self.nnf(&mut *env);
        let lits = nnfs
            .iter()
            .map(|t| t.cnf_nnf_tseitin(env, &mut formula))
            .collect::<Vec<_>>();
        for l in lits {
            formula.add(Clause::single(l));
        }
        formula
    }

    fn nnf(&self, env: &mut CNFEnv<'_>) -> Self {
        self.iter()
            .flat_map(|t| {
                let t = t.nnf(&mut *env);
                match t.repr() {
                    ATerm::And(ts) => ts.clone(),
                    _ => vec![t],
                }
            })
            .collect()
    }
}

fn has_no_disjunction(t: &Term) -> bool {
    match t.repr() {
        ATerm::And(ts) => ts.iter().all(has_no_disjunction),
        ATerm::Or(_) => false,
        _ => true,
    }
}

/// Partition nnfs into (those that have no disjunction, those that have disjunctions)
pub fn partition_nnfs(ts: Vec<Term>) -> (Vec<Term>, Vec<Term>) {
    ts.into_iter().partition(has_no_disjunction)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;

    #[test]
    fn test_nnf_false() {
        let mut env = CNFEnv {
            arena: &mut Default::default(),
            cache: &mut CNFCache::new(),
        };
        let terms = vec![env.arena.get_false()];
        let nnf = terms.nnf(&mut env);
        assert_eq!(nnf, terms);
    }

    #[test]
    fn test_nnf_false2() {
        let mut env = CNFEnv {
            arena: &mut Default::default(),
            cache: &mut CNFCache::new(),
        };
        let fals = env.arena.get_false();
        let terms = vec![env.arena.and(vec![fals.clone(), fals.clone()])];
        let nnf = terms.nnf(&mut env);
        let expected = vec![fals.clone(), fals];
        assert_eq!(nnf, expected);
    }

    #[test]
    fn test_nnf_false3() {
        // this test makes sure annotations are omitted
        let mut env = CNFEnv {
            arena: &mut Default::default(),
            cache: &mut CNFCache::new(),
        };
        let fals = env.arena.get_false();
        let and = env.arena.and(vec![fals.clone(), fals.clone()]);
        let goal = env.arena.allocate_symbol("goal");
        let terms = vec![env.arena.annotated(and, vec![Attribute::Named(goal)])];
        let nnf = terms.nnf(&mut env);
        let expected = vec![fals.clone(), fals];
        assert_eq!(nnf, expected);
    }

    #[test]
    fn test_cnf_tseitin_conjunction() {
        let mut env = CNFEnv {
            arena: &mut Default::default(),
            cache: &mut CNFCache::new(),
        };
        // Test: Simple conjunction (a ∧ b)
        let a = env.arena.simple_symbol("a");
        let b = env.arena.simple_symbol("b");
        let and_term = env.arena.and(vec![a.clone(), b.clone()]);

        let formula = and_term.cnf_tseitin(&mut env);

        // Get the variable assignments
        let a_var = env.cache.var_map.get(&a.uid()).copied().unwrap();
        let b_var = env.cache.var_map.get(&b.uid()).copied().unwrap();
        let and_var = env.cache.var_map.get(&and_term.uid()).copied().unwrap();

        // Check that we have exactly 4 clauses for Tseitin transformation of (a ∧ b):
        // 1. (a ∨ ¬and_var) - if and_var is true, then a must be true
        // 2. (b ∨ ¬and_var) - if and_var is true, then b must be true
        // 3. (¬a ∨ ¬b ∨ and_var) - if a and b are true, then and_var must be true
        // 4. (and_var) - the top-level assertion
        assert_eq!(formula.0.len(), 4);
        assert_eq!(formula.0[0], Clause(vec![a_var, -and_var]));
        assert_eq!(formula.0[1], Clause(vec![b_var, -and_var]));
        assert_eq!(formula.0[2], Clause(vec![-a_var, -b_var, and_var]));
        assert_eq!(formula.0[3], Clause(vec![and_var]));
    }

    #[test]
    fn test_cnf_tseitin_disjunction() {
        let mut env = CNFEnv {
            arena: &mut Default::default(),
            cache: &mut CNFCache::new(),
        };
        // Test: Simple disjunction (a ∨ b)
        let a = env.arena.simple_symbol("a");
        let b = env.arena.simple_symbol("b");
        let or_term = env.arena.or(vec![a.clone(), b.clone()]);

        let formula = or_term.cnf_tseitin(&mut env);

        let a_var = env.cache.var_map.get(&a.uid()).copied().unwrap();
        let b_var = env.cache.var_map.get(&b.uid()).copied().unwrap();
        let or_var = env.cache.var_map.get(&or_term.uid()).copied().unwrap();

        // Check that we have exactly 4 clauses for Tseitin transformation of (a ∨ b):
        // 1. (¬a ∨ or_var) - if a is true, then or_var must be true
        // 2. (¬b ∨ or_var) - if b is true, then or_var must be true
        // 3. (a ∨ b ∨ ¬or_var) - if or_var is true, then at least one of a, b must be true
        // 4. (or_var) - the top-level assertion
        assert_eq!(formula.0.len(), 4);
        assert_eq!(formula.0[0], Clause(vec![-a_var, or_var]));
        assert_eq!(formula.0[1], Clause(vec![-b_var, or_var]));
        assert_eq!(formula.0[2], Clause(vec![a_var, b_var, -or_var]));
        assert_eq!(formula.0[3], Clause(vec![or_var]));
    }

    #[test]
    fn test_cnf_tseitin_nested_conjunction() {
        let mut env = CNFEnv {
            arena: &mut Default::default(),
            cache: &mut CNFCache::new(),
        };
        // Test: Simple conjunction ((a ∧ b) ∧ b)
        let a = env.arena.simple_symbol("a");
        let b = env.arena.simple_symbol("b");
        let inner_and_term = env.arena.and(vec![a.clone(), b.clone()]);
        let outer_or_term = env.arena.or(vec![inner_and_term.clone(), b.clone()]);

        let formula = outer_or_term.cnf_tseitin(&mut env);

        // Get the variable assignments
        let a_var = env.cache.var_map.get(&a.uid()).copied().unwrap();
        let b_var = env.cache.var_map.get(&b.uid()).copied().unwrap();
        let inner_and_var = env
            .cache
            .var_map
            .get(&inner_and_term.uid())
            .copied()
            .unwrap();
        let outer_or_var = env
            .cache
            .var_map
            .get(&outer_or_term.uid())
            .copied()
            .unwrap();

        // Check that we have exactly 4 clauses for Tseitin transformation of (a ∧ b):
        // 1. (a ∨ ¬inner_and_var) - if inner_and_var is true, then a must be true
        // 2. (b ∨ ¬inner_and_var) - if inner_and_var is true, then b must be true
        // 3. (¬a ∨ ¬b ∨ inner_and_var) - if a and b are true, then inner_and_var must be true
        // 4. (¬inner_and_var ∨ outer_or_var) - if a is true, then outer_or_var must be true
        // 5. (¬b ∨ outer_or_var) - if b is true, then outer_or_var must be true
        // 6. (inner_and_var ∨ b ∨ ¬outer_or_var) - if outer_or_var is true, then at least one of a, b must be true
        // 7. (outer_or_var) - the top-level assertion
        assert_eq!(formula.0.len(), 7);
        assert_eq!(formula.0[0], Clause(vec![a_var, -inner_and_var]));
        assert_eq!(formula.0[1], Clause(vec![b_var, -inner_and_var]));
        assert_eq!(formula.0[2], Clause(vec![-a_var, -b_var, inner_and_var]));
        assert_eq!(formula.0[3], Clause(vec![-inner_and_var, outer_or_var]));
        assert_eq!(formula.0[4], Clause(vec![-b_var, outer_or_var]));
        assert_eq!(
            formula.0[5],
            Clause(vec![inner_and_var, b_var, -outer_or_var])
        );
        assert_eq!(formula.0[6], Clause(vec![outer_or_var]));
    }
}

#[cfg(test)]
mod stack_safety {
    use super::*;
    use crate::ast::*;

    /// `(and x (or x (and x (or x …))))`, nested `depth` deep. The connectives alternate so that
    /// `flat_and`/`flat_or` cannot collapse the nesting into one wide term: depth is the point.
    fn deep_alternating(arena: &mut Arena, depth: usize) -> Term {
        let bs = arena.bool_sort();
        let x = arena.simple_sorted_symbol("x", bs);
        let mut t = x.clone();
        for i in 0..depth {
            t = if i % 2 == 0 {
                arena.flat_or(vec![x.clone(), t])
            } else {
                arena.flat_and(vec![x.clone(), t])
            };
        }
        t
    }

    const DEEP: usize = 100_000;

    fn on_small_stack(f: impl FnOnce() -> bool + Send + 'static) -> bool {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(f)
            .expect("spawn")
            .join()
            .expect("the conversion overflowed the stack")
    }

    #[test]
    fn nnf_is_flat() {
        assert!(on_small_stack(|| {
            let mut arena = Arena::default();
            let mut cache = CNFCache::new();
            let mut env = CNFEnv {
                arena: &mut arena,
                cache: &mut cache,
            };
            let t = deep_alternating(env.arena, DEEP);
            let nnf = t.nnf(&mut env);
            let ok = nnf == t;
            std::mem::forget((t, nnf));
            ok
        }));
    }

    #[test]
    fn cnf_is_flat() {
        assert!(on_small_stack(|| {
            let mut arena = Arena::default();
            let mut cache = CNFCache::new();
            let mut env = CNFEnv {
                arena: &mut arena,
                cache: &mut cache,
            };
            let t = deep_alternating(env.arena, DEEP);
            // Reaching here at all is the assertion; `on_small_stack` fails on an overflow.
            let f = t.cnf(&mut env);
            std::mem::forget((t, f));
            true
        }));
    }

    #[test]
    fn cnf_tseitin_is_flat() {
        assert!(on_small_stack(|| {
            let mut arena = Arena::default();
            let mut cache = CNFCache::new();
            let mut env = CNFEnv {
                arena: &mut arena,
                cache: &mut cache,
            };
            let t = deep_alternating(env.arena, DEEP);
            let f = t.cnf_tseitin(&mut env);
            std::mem::forget((t, f));
            true
        }));
    }
}
