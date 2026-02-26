// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! # Let-introduction in A Topological Order
//!
//! Often in different places in a term appears a common shared sub-term. The construction of this shared
//! sub-term has been deduplicated by hashconsing. Meanwhile, the default infrastructure that prints a term
//! is too naive to take a shared term into account. For example, when printing a term
//! ```smt2
//! (* (+ 1 2) (+ 1 2))
//! ```
//! it's optimal to group `(+ 1 2)`, such that the following is printed
//! ```smt2
//! (let ((x (+ 1 2)) (* x x))
//! ```
//! This expectation should cascade if `x` binds a term with more shared subterms.
//!
//! This module therefore solves this problem. This module effectively does a topological sorting on
//! a term, so that sub-terms are sorted by their order of dependencies, with the least dependency level
//! on top. Then, based on the order, we reintroduce let-bindings to the given term, so that bindings
//! appear later **necessarily** depend on earlier ones and the resulting term is equivalent to the
//! original one. In this way, a shared term is never referred twice.
//!
//! The algorithm proceeds as follows:
//!
//! 1. We first discover a topological order of sub-terms. The algorithm ensures that
//!     1. a shared subterm appears in its least possible dependency level. In other words, this sub-term
//!        necessarily depends on some other terms in lower levels, transitively.
//!     2. if a sub-term is not shared, then it is not in this order.
//!
//!     A dependency level could contain multiple sub-terms, which of course do not depend on each other.
//!
//! 2. We then use the order to create a let-introduced term.
//!
//! The more difficult part is the first step, where we compute a topological order. The challenge is
//! due to binders, where new variables are introduced. Therefore, we must keep track of a tree of
//! bindings, as well as compute the dependency levels of a term after some (not necessarily all)
//! variables are closed by the binders. This consideration is captured by the trait `FindSectionsImpl`
//! and the return type `FindResult` is a vector to handle this complication due to binders. The binding
//! structure is captured by a linked list and remembered by a hashmap.
//!
//! `FindResult` appears to constitute a semi-lattice structure, which is captured by the `glb` and
//! `glbs` functions.
//!
//! The top-level API is exposed by the trait [TopoLetIntro].

use crate::allocator::{LocalVarAllocator, TermAllocator};
use crate::ast::alg::VarBinding;
use crate::ast::{ATerm, FetchSort, FreshVar, HasArenaAlt, Local, PatternArm, Str, Term};
use crate::traits::Repr;
use std::cell::RefCell;
use std::cmp::max;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Debug, Clone)]
struct SecRecord {
    /// How many times a term has been referenced?
    referenced: usize,
    /// The level of let-bindings to appear for a given term;
    /// this level is the smallest possible level
    level: usize,
}

/// The algorithm is organized to return a tree, where a branch is created for each binder. A [Section] stores
/// data for each node in the tree.
///
/// The topological order of sub-terms is stored in `let_hierarchy`.
#[derive(Debug, Clone)]
struct Section {
    /// The bound variables introduced by the binder
    bound_variables: Vec<Str>,
    /// Remember how sub-terms are referenced
    ///
    /// This field does not consider sub-terms in deeper binders
    let_hierarchy: HashMap<Term, SecRecord>,
    /// The level in a tree
    level: usize,
    /// Parent node
    parent: Option<SectionCell>,
}

type SectionCell = Rc<RefCell<Section>>;

impl Section {
    fn new() -> Self {
        Self {
            bound_variables: vec![],
            let_hierarchy: Default::default(),
            level: 0,
            parent: None,
        }
    }

    fn new_with_bound_variables(bound_variables: &[Str], parent: SectionCell) -> Self {
        let l = parent.borrow().level;
        Self {
            bound_variables: bound_variables.to_vec(),
            let_hierarchy: Default::default(),
            level: l + 1,
            parent: Some(parent),
        }
    }

    fn get_let_bindings(&self) -> Vec<Vec<Term>> {
        let mut r = vec![];
        for (t, lvl) in self
            .let_hierarchy
            .iter()
            .filter(|(_, v)| v.referenced > 1)
            .map(|(k, v)| (k.clone(), v.level))
        {
            while r.len() <= lvl {
                r.push(vec![]);
            }
            r[lvl].push(t);
        }
        r
    }
}

/// The return type of [FindSectionsImpl]
///
/// It returns a vector of (the [Section] where the term could be included in, an option of
/// let-binding level if it should be bound). It is non-empty.
///
/// It is essentially a prefix of the path going from the current [Section] to root (found by [find_root])
///
/// It is a vector because it should maintain an induction invariant. In this case, other than
/// the last element, the given term contains free variables in all other [Section]s.
type FindResult = Vec<(SectionCell, Option<usize>)>;

/// locate the cell of the variable n
fn find_bound_section(cell: &SectionCell, n: &str) -> Option<SectionCell> {
    if cell
        .borrow()
        .bound_variables
        .iter()
        .any(|v| v.as_str() == n)
    {
        Some(cell.clone())
    } else {
        cell.borrow()
            .parent
            .as_ref()
            .and_then(|p| find_bound_section(p, n))
    }
}

/// Find the root of the binding stack
fn find_root(cell: &SectionCell) -> SectionCell {
    if let Some(parent) = cell.borrow().parent.as_ref() {
        find_root(parent)
    } else {
        cell.clone()
    }
}

/// Extend a cell with bound variables
fn extend_cell(parent: SectionCell, bound_variables: &[Str]) -> SectionCell {
    Rc::new(RefCell::new(Section::new_with_bound_variables(
        bound_variables,
        parent,
    )))
}

fn opt_max(a: Option<usize>, b: Option<usize>) -> Option<usize> {
    match a {
        None => b,
        Some(a) => match b {
            None => Some(a),
            Some(b) => Some(max(a, b)),
        },
    }
}

/// Find the greatest lower bound of two [FindResult]
///
/// The goal of this function is to find the glb of two binding results to place the term that contains
/// both `r1` and `r2`.
fn glb(r1: &FindResult, r2: &FindResult) -> FindResult {
    let mut l = r1;
    let mut r = r2;
    if r.len() > l.len() {
        (l, r) = (r, l);
    }
    // r now is shorter
    let mut result = vec![];
    for i in 0..l.len() {
        if i < r.len() {
            let (e, j) = &l[i];
            let (_, k) = &r[i];
            result.push((e.clone(), opt_max(*j, *k)));
        } else {
            result.push(l[i].clone())
        }
    }
    result
}

fn glbs(rs: &[FindResult]) -> Option<FindResult> {
    if rs.is_empty() {
        None
    } else {
        let fst = rs[0].clone();
        Some(rs[1..].iter().fold(fst, |x, y| glb(&x, y)))
    }
}

fn incr_opt(o: Option<usize>) -> Option<usize> {
    o.map(|n| n + 1).or(Some(0))
}

fn incr_result(f: FindResult) -> FindResult {
    f.into_iter().map(|(c, lvl)| (c, incr_opt(lvl))).collect()
}

/// The trait that implements the algorithm that builds up the tree of [Section]s
trait FindSectionsImpl {
    /// * `tail` is the leaf of the current tree where `self` is bound at
    /// * `binders` stores a mapping from all binders to their [Section]
    /// * `insert` indicate whether the current term should be inserted into the [Section], meaning
    ///   that it is a sub-term of a larger term.
    fn find_sections(
        &self,
        tail: &SectionCell,
        binders: &mut HashMap<Term, SectionCell>,
        insert: bool,
    ) -> FindResult;
}

impl FindSectionsImpl for Term {
    fn find_sections(
        &self,
        tail: &SectionCell,
        binders: &mut HashMap<Term, SectionCell>,
        mut insert: bool,
    ) -> FindResult {
        fn find_sections_slice(
            ts: &[Term],
            tail: &SectionCell,
            binders: &mut HashMap<Term, SectionCell>,
        ) -> FindResult {
            let res = ts
                .iter()
                .map(|t| t.find_sections(tail, binders, true))
                .collect::<Vec<_>>();
            match glbs(&res) {
                Some(r) if !r.is_empty() => incr_result(r),
                _ => {
                    // in this case, it means app has no argument, then we can just bubble it to the top level.
                    let root = find_root(tail);
                    vec![(root, Some(0))]
                }
            }
        }

        fn find_sections_binder<T>(
            vs: &[VarBinding<Str, T>],
            t: &Term,
            tail: &SectionCell,
            binders: &mut HashMap<Term, SectionCell>,
        ) -> FindResult {
            let sub = extend_cell(
                tail.clone(),
                &vs.iter().map(|v| v.0.clone()).collect::<Vec<_>>(),
            );
            binders.insert(t.clone(), sub.clone());
            let mut r = t.find_sections(&sub, binders, true);
            if let Some((c, _)) = r.last()
                && c.borrow().level == sub.borrow().level
            {
                r.pop();
            }
            r
        }

        let r = match self.repr() {
            ATerm::Constant(_, _) => vec![],
            ATerm::Global(_, _) => vec![],
            ATerm::Local(id) => {
                // first find the binding section
                let cell = find_bound_section(tail, id.symbol.as_str()).unwrap();
                let mut acc = vec![(cell.clone(), None)];
                let mut it = cell;
                // then we collect all the parent sections
                loop {
                    let p = if let Some(p) = it.borrow().parent.as_ref() {
                        acc.push((p.clone(), None));
                        p.clone()
                    } else {
                        break;
                    };
                    it = p;
                }
                insert = false;
                acc.reverse();
                acc
            }
            ATerm::Let(_, _) => unreachable!(), // assume let elimination
            ATerm::Exists(vs, t) | ATerm::Forall(vs, t) => {
                find_sections_binder(vs, t, tail, binders)
            }
            ATerm::Annotated(t, _) => t.find_sections(tail, binders, insert),
            ATerm::Eq(a, b) => {
                let ra = a.find_sections(tail, binders, true);
                let rb = b.find_sections(tail, binders, true);
                glb(&ra, &rb)
            }
            ATerm::App(_, ts, _)
            | ATerm::Distinct(ts)
            | ATerm::And(ts)
            | ATerm::Or(ts)
            | ATerm::Xor(ts) => find_sections_slice(ts, tail, binders),
            ATerm::Implies(a, b) => {
                let ra = find_sections_slice(a, tail, binders);
                let rb = b.find_sections(tail, binders, true);
                glb(&ra, &rb)
            }
            ATerm::Not(t) => t.find_sections(tail, binders, true),
            ATerm::Ite(b, t, e) => {
                find_sections_slice(&[b.clone(), t.clone(), e.clone()], tail, binders)
            }
            ATerm::Matching(t, cases) => {
                let tr = t.find_sections(tail, binders, true);
                let mut vc = vec![tr];
                for case in cases {
                    let sub = extend_cell(
                        tail.clone(),
                        &case
                            .pattern
                            .variables()
                            .into_iter()
                            .cloned()
                            .collect::<Vec<_>>(),
                    );
                    binders.insert(case.body.clone(), sub.clone());
                    let mut r = case.body.find_sections(tail, binders, true);
                    if let Some((c, _)) = r.last()
                        && c.borrow().level == sub.borrow().level
                    {
                        // get rid of the tail if bound variables are used.
                        // in this case, we don't want glbs to return the Section under binder
                        r.pop();
                    }
                    vc.push(r);
                }
                // unwrap here because we know it is non-empty
                glbs(&vc).unwrap()
            }
        };

        if insert && let Some((r, Some(lvl))) = r.last() {
            let mut b = r.borrow_mut();
            let rec = b
                .let_hierarchy
                .entry(self.clone())
                .or_insert_with(|| SecRecord {
                    referenced: 0,
                    level: *lvl,
                });
            rec.referenced += 1;
        }

        r
    }
}

/// Re-introduce let bindings to `Self` when appropriate
///
/// This is implementation detailed; not to be exposed
trait TopoLetIntroImpl<E> {
    /// Invariant: if a term is in let_hierarchy and referenced more than once, then it has to be in vars
    fn let_intro_body(
        &self,
        cell: SectionCell,
        binders: &mut HashMap<Term, SectionCell>,
        vars: &mut HashMap<Term, Local>,
        top: bool,
        env: &mut E,
    ) -> Self;

    /// Reconstruct Self with lets, given necessary information
    fn let_intro(
        &self,
        cell: SectionCell,
        binders: &mut HashMap<Term, SectionCell>,
        vars: &mut HashMap<Term, Local>,
        env: &mut E,
    ) -> Self;
}

impl<E, T> TopoLetIntroImpl<E> for Vec<T>
where
    E: HasArenaAlt,
    T: TopoLetIntroImpl<E>,
{
    fn let_intro_body(
        &self,
        cell: SectionCell,
        binders: &mut HashMap<Term, SectionCell>,
        vars: &mut HashMap<Term, Local>,
        top: bool,
        env: &mut E,
    ) -> Self {
        self.iter()
            .map(|t| t.let_intro_body(cell.clone(), binders, vars, top, env))
            .collect()
    }

    fn let_intro(
        &self,
        cell: SectionCell,
        binders: &mut HashMap<Term, SectionCell>,
        vars: &mut HashMap<Term, Local>,
        env: &mut E,
    ) -> Self {
        self.iter()
            .map(|t| t.let_intro(cell.clone(), binders, vars, env))
            .collect()
    }
}

impl<E> TopoLetIntroImpl<E> for Term
where
    E: HasArenaAlt,
{
    fn let_intro_body(
        &self,
        cell: SectionCell,
        binders: &mut HashMap<Term, SectionCell>,
        vars: &mut HashMap<Term, Local>,
        top: bool,
        env: &mut E,
    ) -> Self {
        if !top {
            let mut it = cell.clone();
            loop {
                if let Some(rec) = it.borrow().let_hierarchy.get(self) {
                    if rec.referenced > 1 {
                        return env.arena_alt().local(vars.get(self).unwrap().clone());
                    } else {
                        break;
                    }
                }
                let p = if let Some(p) = it.borrow().parent.as_ref() {
                    p.clone()
                } else {
                    break;
                };
                it = p;
            }
        }
        match self.repr() {
            ATerm::Constant(_, _) | ATerm::Global(_, _) | ATerm::Local(_) => self.clone(),
            ATerm::App(id, ts, sort) => {
                let args = ts.let_intro_body(cell, binders, vars, false, env);
                env.arena_alt().app(id.clone(), args, sort.clone())
            }
            ATerm::Let(_, _) => unreachable!(),
            ATerm::Exists(vs, t) => {
                let sub = binders.get(t).unwrap().clone();
                let nt = t.let_intro(sub, binders, vars, env);
                env.arena_alt().exists(vs.clone(), nt)
            }
            ATerm::Forall(vs, t) => {
                let sub = binders.get(t).unwrap().clone();
                let nt = t.let_intro(sub, binders, vars, env);
                env.arena_alt().forall(vs.clone(), nt)
            }
            ATerm::Annotated(t, ans) => {
                let nt = t.let_intro_body(cell, binders, vars, top, env);
                env.arena_alt().annotated(nt, ans.clone())
            }
            ATerm::Eq(a, b) => {
                let na = a.let_intro_body(cell.clone(), binders, vars, false, env);
                let nb = b.let_intro_body(cell, binders, vars, false, env);
                env.arena_alt().eq(na, nb)
            }
            ATerm::Distinct(ts) => {
                let nts = ts.let_intro_body(cell, binders, vars, false, env);
                env.arena_alt().distinct(nts)
            }
            ATerm::And(ts) => {
                let nts = ts.let_intro_body(cell, binders, vars, false, env);
                env.arena_alt().and(nts)
            }
            ATerm::Or(ts) => {
                let nts = ts.let_intro_body(cell, binders, vars, false, env);
                env.arena_alt().or(nts)
            }
            ATerm::Xor(ts) => {
                let nts = ts.let_intro_body(cell, binders, vars, false, env);
                env.arena_alt().xor(nts)
            }
            ATerm::Implies(a, b) => {
                let na = a.let_intro_body(cell.clone(), binders, vars, false, env);
                let nb = b.let_intro_body(cell, binders, vars, false, env);
                env.arena_alt().implies(na, nb)
            }
            ATerm::Not(t) => {
                let nt = t.let_intro_body(cell, binders, vars, false, env);
                env.arena_alt().not(nt)
            }
            ATerm::Ite(b, t, e) => {
                let nb = b.let_intro_body(cell.clone(), binders, vars, false, env);
                let nt = t.let_intro_body(cell.clone(), binders, vars, false, env);
                let ne = e.let_intro_body(cell, binders, vars, false, env);
                env.arena_alt().ite(nb, nt, ne)
            }
            ATerm::Matching(t, cases) => {
                let nt = t.let_intro_body(cell, binders, vars, false, env);
                let mut ncases = vec![];
                for case in cases {
                    let sub = binders.get(&case.body).unwrap().clone();
                    let nbody = case.body.let_intro(sub, binders, vars, env);
                    let ncase = PatternArm {
                        pattern: case.pattern.clone(),
                        body: nbody,
                    };
                    ncases.push(ncase);
                }
                env.arena_alt().matching(nt, ncases)
            }
        }
    }

    fn let_intro(
        &self,
        cell: SectionCell,
        binders: &mut HashMap<Term, SectionCell>,
        vars: &mut HashMap<Term, Local>,
        env: &mut E,
    ) -> Self {
        fn rec<E: HasArenaAlt>(
            t: &Term,
            cell: SectionCell,
            binders: &mut HashMap<Term, SectionCell>,
            vars: &mut HashMap<Term, Local>,
            env: &mut E,
            bindings: Vec<Vec<Term>>,
            i: usize,
        ) -> Term {
            if i >= bindings.len() {
                t.let_intro_body(cell, binders, vars, true, env)
            } else {
                let mut vs = vec![];
                for t in &bindings[i] {
                    let id = env.arena_alt().new_local();
                    let symbol = env.arena_alt().fresh_x();
                    let sort = t.get_sort(env);
                    let nt = t.let_intro_body(cell.clone(), binders, vars, true, env);
                    vs.push(VarBinding(symbol.clone(), id, nt.clone()));
                    let loc = Local {
                        id,
                        symbol,
                        sort: Some(sort),
                    };
                    vars.insert(t.clone(), loc);
                }
                let res = rec(t, cell, binders, vars, env, bindings, 1 + i);
                env.arena_alt().let_term(vs, res)
            }
        }

        let bindings = cell.borrow().get_let_bindings();
        rec(self, cell, binders, vars, env, bindings, 0)
    }
}

/// Re-introduce lets to a let-eliminated `Self` based on topological sorting
pub trait TopoLetIntro<E> {
    fn topo_let_intro(&self, env: &mut E) -> Self;

    fn topo_print(&self, env: &mut E) -> String;
}

impl<E> TopoLetIntro<E> for Term
where
    E: HasArenaAlt,
{
    fn topo_let_intro(&self, env: &mut E) -> Self {
        let cell = Rc::new(RefCell::new(Section::new()));
        let mut map = HashMap::new();
        let _ = self.find_sections(&cell, &mut map, false);
        let mut vars = HashMap::new();
        self.let_intro(cell, &mut map, &mut vars, env)
    }

    fn topo_print(&self, env: &mut E) -> String {
        self.topo_let_intro(env).to_string()
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::letintro::TopoLetIntro;
    use crate::ast::{Context, Typecheck};
    use crate::untyped::UntypedAst;

    fn topo_print(s: &str) -> String {
        let mut context = Context::default();
        context.ensure_logic();
        let term = UntypedAst.parse_term_str(s).unwrap();
        let term = term.type_check(&mut context).unwrap();
        term.topo_print(&mut context)
    }

    #[test]
    fn test_printing1() {
        let s = topo_print("(+ (+ 1 2) (+ 1 2))");
        assert_eq!(s, "(let ((x-0 (+ 1 2))) (+ x-0 x-0))");
    }

    #[test]
    fn test_printing2() {
        let s = topo_print("(+ (+ 1 2) (+ 1 2) (+ 3 4))");
        assert_eq!(s, "(let ((x-0 (+ 1 2))) (+ x-0 x-0 (+ 3 4)))");
    }

    #[test]
    fn test_printing3() {
        let s = topo_print("(+ (* (+ 1 2) 3) (* (+ 1 2) 3))");
        assert_eq!(
            s,
            "(let ((x-0 (+ 1 2))) (let ((x-1 (* x-0 3))) (+ x-1 x-1)))"
        );
    }

    #[test]
    fn test_printing_binder1() {
        let s = topo_print(
            "(and (forall ((x Int) (y Int)) (= (* (+ x y) (+ x y)) 10)) (or true false) (or true false))",
        );
        assert_eq!(
            s,
            "(let ((x-0 (or true false))) (and (forall ((x Int) (y Int)) (let ((x-1 (+ x y))) (= (* x-1 x-1) 10))) x-0 x-0))"
        );
    }

    #[test]
    fn test_printing_binder2() {
        let s = topo_print(
            "(and (forall ((x Int) (y Int)) (= (* (+ 1 2) (+ x y) (+ x y)) 10)) (= (+ 1 2) 10))",
        );
        assert_eq!(
            s,
            "(let ((x-0 (+ 1 2))) (and (forall ((x Int) (y Int)) (let ((x-1 (+ x y))) (= (* x-0 x-1 x-1) 10))) (= x-0 10)))"
        );
    }

    #[test]
    fn test_printing_binder3() {
        let s = topo_print(
            "(and (forall ((x Int) (y Int)) (= (+ (* (+ 1 2) (+ x y)) (* (+ 1 2) (+ x y))) 10) ) (= (+ 1 2) 10))",
        );
        assert_eq!(
            s,
            "(let ((x-0 (+ 1 2))) (and (forall ((x Int) (y Int)) (let ((x-1 (+ x y))) (let ((x-2 (* x-0 x-1))) (= (+ x-2 x-2) 10)))) (= x-0 10)))"
        );
    }
}
