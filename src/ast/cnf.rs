//! This module implements the NNF and CNF conversion algorithms
//!
//! It is enabled using `cnf`.

use crate::ast::{
    AConstant, ATerm, Arena, FetchSort, FlatConnectivesExt, ObjectAllocatorExt, Term, TermAllocator,
};
use crate::traits::Repr;
use sat_interface::{Clause, Formula};
use std::collections::HashMap;

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
    /// If [polarity] is true, then the function returns an NNF that is equivalent to the input [Self];
    /// if [!polarity], then the return value is an NNF that negates the input [Self].
    fn nnf_impl(&self, env: Env, polarity: bool) -> Self;

    /// This function computes the variable representing the given term and updates the [formula]
    /// if necessary.
    fn cnf_nnf(&self, env: Env, formula: &mut Formula) -> i32;

    /// This function computes the variable representing the given term and updates the [formula]
    /// if necessary using the Tseitin transformation
    fn cnf_nnf_tseitin(&self, env: Env, formula: &mut Formula) -> i32;
}

impl CNFConversionHelper<&mut CNFEnv<'_>> for Term {
    fn nnf_impl(&self, env: &mut CNFEnv<'_>, polarity: bool) -> Self {
        // this function implements two things:
        // 1. it performs some immediate simplifications to extract the basic boolean skeleton from the formula
        // 2. it then performs NNF transformation.

        // index in the cache array
        let idx = if polarity { 1 } else { 0 };
        // cache lookup; return early if cache is hit.
        if let Some(r) = &env
            .cache
            .nnf_cache
            .entry(self.uid())
            .or_insert_with(|| [None, None])[idx]
        {
            return r.clone();
        }

        let r = match self.repr() {
            ATerm::Annotated(t, _) => t.nnf_impl(env, polarity), // omit attributes
            ATerm::Eq(a, b) => {
                // 1. check if it's comparing two booleans
                let bs = env.arena.bool_sort();
                let sa = a.get_sort(env.arena);
                if sa != bs {
                    // 2. if not, then we regard a = b as an atom
                    if polarity {
                        self.clone()
                    } else {
                        env.arena.not(self.clone())
                    }
                } else {
                    // 2. if so, then we convert a = b to a <=> b
                    let not_a = env.arena.not(a.clone());
                    let not_b = env.arena.not(b.clone());
                    let a_i_b = env.arena.flat_or(vec![not_a, b.clone()]);
                    let b_i_a = env.arena.flat_or(vec![not_b, a.clone()]);
                    let eqf = env.arena.flat_and(vec![a_i_b, b_i_a]);
                    eqf.nnf_impl(env, polarity)
                }
            }
            ATerm::Distinct(ts) => {
                // we know from parsing that ts is non-empty.
                let bs = env.arena.bool_sort();
                let s = ts[0].get_sort(env.arena);
                // 1. we check if ts are booleans
                if bs != s {
                    // 2. if not, then this term is considered atomic.
                    if polarity {
                        self.clone()
                    } else {
                        env.arena.not(self.clone())
                    }
                } else {
                    // otherwise, we translate it into a boolean formula
                    match ts.len() {
                        1 => ts[0].nnf_impl(env, polarity), // if there is only one term, there is not need for comparison
                        2 => {
                            // if there are two terms, then these two must be unequal.
                            let eq = env.arena.eq(ts[0].clone(), ts[1].clone());
                            let eqf = env.arena.not(eq);
                            eqf.nnf_impl(env, polarity)
                        }
                        _ => env.arena.get_false().nnf_impl(env, polarity), // more than two distinct booleans are not possible.
                    }
                }
            }
            ATerm::Constant(AConstant::Bool(b), _) => {
                if polarity {
                    self.clone()
                } else {
                    env.arena.bool(!*b)
                }
            }
            ATerm::And(ts) => {
                match ts.len() {
                    0 => env.arena.get_true().nnf_impl(env, polarity),
                    1 => ts[0].nnf_impl(env, polarity),
                    _ => {
                        let nts = ts
                            .iter()
                            .map(|t| t.nnf_impl(&mut *env, polarity))
                            .collect::<Vec<_>>();
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
                    0 => env.arena.get_false().nnf_impl(env, polarity),
                    1 => ts[0].nnf_impl(env, polarity),
                    _ => {
                        let nts = ts
                            .iter()
                            .map(|t| t.nnf_impl(env, polarity))
                            .collect::<Vec<_>>();
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
                let mut nts: Vec<_> = ts.iter().map(|t| t.nnf_impl(env, !polarity)).collect();
                let nb = b.nnf_impl(env, polarity);
                nts.push(nb);
                if polarity {
                    env.arena.flat_or(nts)
                } else {
                    env.arena.flat_and(nts)
                }
            }
            ATerm::Not(t) => t.nnf_impl(env, !polarity),
            ATerm::Ite(b, t, e) => {
                // notice `(ite b t e)` is `(or (and b t) (and (not b) e))`
                let not_b = env.arena.not(b.clone());
                let bt = env.arena.flat_and(vec![b.clone(), t.clone()]);
                let not_b_e = env.arena.flat_and(vec![not_b, e.clone()]);
                let eqf = env.arena.flat_or(vec![bt, not_b_e]);
                eqf.nnf_impl(env, polarity)
            }
            _ => {
                // all other cases are regarded as atoms.
                if polarity {
                    self.clone()
                } else {
                    env.arena.not(self.clone())
                }
            }
        };
        // unwrap is safe here because we know we've inserted the array at the beginning.
        env.cache.nnf_cache.get_mut(&self.uid()).unwrap()[idx] = Some(r.clone());
        if polarity {
            // if polarity is positive, then we know nnf is idempotent, i.e. nnf of nnf gives the same nnf.
            // therefore, we can just update the cache to reflect this fact to save some compute
            let arr = env.cache.nnf_cache.entry(r.uid()).or_insert([None, None]);
            arr[1] = Some(r.clone());
        }
        r
    }

    /// This function implements Plaisted-Greenbaum (PG) transformation.
    ///
    /// Essentially, when given an NNF formula, the transformation assigns one fresh variable for
    /// each conjunction or disjunction.
    ///
    /// There are two interesting cases:
    ///
    /// 1. for `(and a1 a2 ... an)` and a fresh variable `x`, it is sufficient to add to the [formula]
    /// `(=> x (and a1 a2 ... an))`, which unfolds to a conjunction of `(or (not x) ai)` for all `i`.
    ///
    /// 2.  `(or a1 a2 ... an)` and a fresh variable `x`, it is sufficient to add to the [formula]
    /// `(=> x (or a1 a2 ... an))`, which unfolds to one clause: `(or (not x) a1 ... an)`.
    ///
    /// c.f. https://dl.acm.org/doi/10.1145/3551349.3556938
    fn cnf_nnf(&self, env: &mut CNFEnv<'_>, formula: &mut Formula) -> i32 {
        // cache lookup
        if let Some(i) = env.cache.var_map.get(&self.uid()) {
            return *i;
        }

        let v = match self.repr() {
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
                0 => env.arena.get_true().cnf_nnf(env, formula), // (and) is just true.
                1 => ts[0].cnf_nnf(env, formula),                // (and a) is just a.
                _ => {
                    //
                    let nv = env.new_var();
                    let vs: Vec<_> = ts.iter().map(|t| t.cnf_nnf(env, formula)).collect();
                    for v in vs {
                        formula.add(Clause::new(vec![v, -nv]))
                    }
                    nv
                }
            },
            ATerm::Or(ts) => match ts.len() {
                0 => env.arena.get_false().cnf_nnf(env, formula), // (or) is just false.
                1 => ts[0].cnf_nnf(env, formula),                 // (or a) is just a.
                _ => {
                    let nv = env.new_var();
                    let mut vs: Vec<_> = ts.iter().map(|t| t.cnf_nnf(env, formula)).collect();
                    vs.push(-nv);
                    formula.add(Clause::new(vs));
                    nv
                }
            },
            ATerm::Not(t) => -t.cnf_nnf(env, formula),
            _ => env.new_var(),
        };
        env.cache.var_map.insert(self.uid(), v);
        env.cache.var_map_reverse.insert(v, self.uid());
        v
    }

    /// This function implements Tseitin transformation.
    ///
    /// Essentially, when given an NNF formula, the transformation assigns one fresh variable for
    /// each conjunction or disjunction.
    ///
    /// There are two interesting cases:
    ///
    /// 1. for `(and a1 a2 ... an)` and a fresh variable `x`, we add to the [formula]
    /// `(=> x (and a1 a2 ... an))`, which unfolds to a conjunction of `(or (not x) ai)` for all `i`
    /// and `(=> (and a1 a2 ... an) x)`, which unfolds to `(or (not a1) ... (not an) x)``.
    ///
    /// 2.  `(or a1 a2 ... an)` and a fresh variable `x`, we add to the [formula]
    /// `(=> x (or a1 a2 ... an))`, which unfolds to one clause: `(or (not x) a1 ... an)`
    /// and `(=> (or a1 a2 ... an) x)`, which unfolds to a conjunction of of `(or x (not ai))` for all `i`
    ///
    /// c.f. https://en.wikipedia.org/wiki/Tseytin_transformation
    fn cnf_nnf_tseitin(&self, env: &mut CNFEnv<'_>, formula: &mut Formula) -> i32 {
        // cache lookup
        if let Some(i) = env.cache.var_map.get(&self.uid()) {
            return *i;
        }

        let v = match self.repr() {
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
                0 => env.arena.get_true().cnf_nnf_tseitin(env, formula), // (and) is just true.
                1 => ts[0].cnf_nnf_tseitin(env, formula),                // (and a) is just a.
                _ => {
                    let nv = env.new_var();
                    let vs: Vec<_> = ts.iter().map(|t| t.cnf_nnf_tseitin(env, formula)).collect();
                    for v in vs.clone() {
                        formula.add(Clause::new(vec![v, -nv]))
                    }
                    let mut nvs: Vec<_> = vs.iter().map(|l| -l).collect();
                    nvs.push(nv);
                    formula.add(Clause::new(nvs));
                    nv
                }
            },
            ATerm::Or(ts) => match ts.len() {
                0 => env.arena.get_false().cnf_nnf_tseitin(env, formula), // (or) is just false.
                1 => ts[0].cnf_nnf_tseitin(env, formula),                 // (or a) is just a.
                _ => {
                    let nv = env.new_var();
                    let mut vs: Vec<_> =
                        ts.iter().map(|t| t.cnf_nnf_tseitin(env, formula)).collect();
                    for v in vs.clone() {
                        formula.add(Clause::new(vec![-v, nv]))
                    }
                    vs.push(-nv);
                    formula.add(Clause::new(vs));
                    nv
                }
            },
            ATerm::Not(t) => -t.cnf_nnf_tseitin(env, formula),
            _ => env.new_var(),
        };
        env.cache.var_map.insert(self.uid(), v);
        env.cache.var_map_reverse.insert(v, self.uid());
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

/// partition nnfs into (those that have no disjunction, those that have disjunctions)
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
