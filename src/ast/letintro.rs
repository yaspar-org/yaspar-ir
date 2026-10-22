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

use crate::allocator::{LocalVarAllocator, StrAllocator, TermAllocator};
use crate::ast::alg::VarBinding;
use crate::ast::{
    ATerm, Arena, Attribute, FetchSort, HasArena, HasArenaAlt, LetElim, Local, Pattern, PatternArm,
    Sort, Str, Term,
};
use crate::traits::Repr;
use std::cell::RefCell;
use std::cmp::max;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use yaspar_macros::stack_safe;

#[derive(Debug, Clone)]
struct SecRecord {
    /// How many times a term has been referenced?
    referenced: usize,
    /// The level of let-bindings to appear for a given term;
    /// this level is the smallest possible level
    level: usize,
    /// When the term was first referenced in its section, which orders bindings of one level
    order: usize,
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
    /// Distinguishes this section from all others in one walk; the root is 0
    id: usize,
    /// Parent node
    parent: Option<SectionCell>,
    /// State of the whole walk, kept by the root only
    root: RootState,
}

/// What the root [Section] keeps for the whole walk
#[derive(Debug, Clone, Default)]
struct RootState {
    /// The id of the next [Section] to create
    next_section: usize,
    /// Symbols occurring in the term, which a let-bound variable must not shadow
    used_names: HashSet<String>,
    /// The suffix of the next let-bound variable to try
    next_name: usize,
}

type SectionCell = Rc<RefCell<Section>>;

impl Section {
    fn new() -> Self {
        Self {
            bound_variables: vec![],
            let_hierarchy: Default::default(),
            level: 0,
            id: 0,
            parent: None,
            root: RootState {
                next_section: 1,
                ..Default::default()
            },
        }
    }

    fn new_with_bound_variables(bound_variables: &[Str], parent: SectionCell) -> Self {
        let l = parent.borrow().level;
        let id = {
            let root = find_root(&parent);
            let mut root = root.borrow_mut();
            let id = root.root.next_section;
            root.root.next_section += 1;
            id
        };
        Self {
            bound_variables: bound_variables.to_vec(),
            let_hierarchy: Default::default(),
            level: l + 1,
            id,
            parent: Some(parent),
            root: Default::default(),
        }
    }

    fn get_let_bindings(&self) -> Vec<Vec<Term>> {
        let mut r: Vec<Vec<(usize, Term)>> = vec![];
        for (t, lvl, order) in self
            .let_hierarchy
            .iter()
            .filter(|(_, v)| v.referenced > 1)
            .map(|(k, v)| (k.clone(), v.level, v.order))
        {
            while r.len() <= lvl {
                r.push(vec![]);
            }
            r[lvl].push((order, t));
        }
        // a level whose terms are all referenced once has nothing to bind
        r.retain(|ts| !ts.is_empty());
        // the map's iteration order is arbitrary; bind in the order the walk met the terms
        r.into_iter()
            .map(|mut ts| {
                ts.sort_by_key(|(order, _)| *order);
                ts.into_iter().map(|(_, t)| t).collect()
            })
            .collect()
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
///
/// Walked rather than recursed: the chain is one link per enclosing binder, so its length follows
/// the input's binder nesting.
fn find_bound_section(cell: &SectionCell, n: &str) -> Option<SectionCell> {
    let mut it = cell.clone();
    loop {
        if it.borrow().bound_variables.iter().any(|v| v.as_str() == n) {
            return Some(it);
        }
        let parent = it.borrow().parent.clone();
        it = parent?;
    }
}

/// Find the root of the binding stack
fn find_root(cell: &SectionCell) -> SectionCell {
    let mut it = cell.clone();
    loop {
        let parent = it.borrow().parent.clone();
        match parent {
            Some(p) => it = p,
            None => return it,
        }
    }
}

/// A name for a let-bound variable that no symbol of the term uses, nor an earlier let-bound
/// variable. Numbered per walk from `x-0`, so the same term always prints the same.
fn fresh_let_name(cell: &SectionCell, arena: &mut Arena) -> Str {
    let root = find_root(cell);
    let mut root = root.borrow_mut();
    let st = &mut root.root;
    loop {
        let candidate = format!("x-{}", st.next_name);
        st.next_name += 1;
        if st.used_names.insert(candidate.clone()) {
            return arena.allocate_string(candidate);
        }
    }
}

/// Every symbol occurring in `t`, attributes included
///
/// A worklist over the distinct sub-terms rather than a recursion, so neither the term's depth
/// nor its tree size matters.
fn used_symbols(t: &Term) -> HashSet<String> {
    let mut used = HashSet::new();
    let mut seen: HashSet<Term> = HashSet::new();
    let mut stack = vec![t.clone()];
    while let Some(t) = stack.pop() {
        if !seen.insert(t.clone()) {
            continue;
        }
        match t.repr() {
            ATerm::Global(qid, _) | ATerm::App(qid, _, _) => {
                used.insert(qid.0.symbol.to_string());
            }
            ATerm::Local(l) => {
                used.insert(l.symbol.to_string());
            }
            ATerm::Let(vs, _) => used.extend(vs.iter().map(|v| v.0.to_string())),
            ATerm::Exists(vs, _) | ATerm::Forall(vs, _) => {
                used.extend(vs.iter().map(|v| v.0.to_string()))
            }
            ATerm::Matching(_, arms) => {
                for arm in arms {
                    match &arm.pattern {
                        Pattern::Ctor(c) | Pattern::Applied { ctor: c, .. } => {
                            used.insert(c.to_string());
                        }
                        Pattern::Wildcard(_) => {}
                    }
                    used.extend(arm.pattern.variables().into_iter().map(|v| v.to_string()));
                }
            }
            ATerm::Annotated(_, ans) => {
                for a in ans {
                    if let Attribute::Named(n) | Attribute::Symbol(_, n) = a {
                        used.insert(n.to_string());
                    }
                }
            }
            _ => {}
        }
        stack.extend(t.repr().sub_terms().cloned());
    }
    used
}

/// Lends an [Arena] to an API that asks for [HasArena]
struct ArenaRef<'a>(&'a mut Arena);

impl HasArena for ArenaRef<'_> {
    fn arena(&mut self) -> &mut Arena {
        self.0
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

/// A [None] stays: a term depends on a section only if one of its sub-terms does
fn incr_opt(o: Option<usize>) -> Option<usize> {
    o.map(|n| n + 1)
}

/// Remove the section of a binder from the result of its body, if the body uses the bound
/// variables, together with the sections it then no longer depends on. The term lands in the
/// innermost section it depends on, so the result must end there.
fn leave_section(r: &mut FindResult, sub_level: usize) {
    if let Some((c, _)) = r.last()
        && c.borrow().level == sub_level
    {
        r.pop();
    }
    while let Some((_, None)) = r.last() {
        r.pop();
    }
}

fn incr_result(f: FindResult) -> FindResult {
    f.into_iter().map(|(c, lvl)| (c, incr_opt(lvl))).collect()
}

/// The [FindResult] of each term visited so far, keyed by the term and the id of the [Section] it
/// lands in (the cell of the last element of the result).
///
/// A term is walked once per section it lands in, rather than once per occurrence, so the walk
/// follows the DAG of the term rather than its tree. A later occurrence is looked up along the
/// chain of its `tail`, since the section a term lands in is always an ancestor of the `tail`.
struct Memo {
    results: HashMap<(Term, usize), FindResult>,
}

impl Memo {
    fn new() -> Self {
        Self {
            results: HashMap::new(),
        }
    }

    fn lookup(&self, this: &Term, tail: &SectionCell) -> Option<FindResult> {
        let mut it = tail.clone();
        loop {
            let id = it.borrow().id;
            if let Some(r) = self.results.get(&(this.clone(), id)) {
                return Some(r.clone());
            }
            let parent = it.borrow().parent.clone();
            it = parent?;
        }
    }
}

/// Count one more reference to `this` in the section it lands in
fn record_reference(this: &Term, r: &FindResult) {
    if let Some((r, Some(lvl))) = r.last() {
        let mut b = r.borrow_mut();
        let order = b.let_hierarchy.len();
        let rec = b
            .let_hierarchy
            .entry(this.clone())
            .or_insert_with(|| SecRecord {
                referenced: 0,
                level: *lvl,
                order,
            });
        rec.referenced += 1;
    }
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
        insert: bool,
    ) -> FindResult {
        let mut memo = Memo::new();
        find_sections_of(self, tail, binders, &mut memo, insert)
    }
}

/// Where a slice's results end up: the greatest lower bound of the parts, or the top level when
/// there are no parts to bound. Split out of the recursion so both a slice and an `ite` can use it.
fn combine(res: Vec<FindResult>, tail: &SectionCell) -> FindResult {
    match glbs(&res) {
        Some(r) if !r.is_empty() => incr_result(r),
        _ => {
            // in this case, it means app has no argument, then we can just bubble it to the top level.
            let root = find_root(tail);
            vec![(root, Some(0))]
        }
    }
}

/// The body of [`FindSectionsImpl::find_sections`], together with the two helpers it recurses
/// through. Free functions rather than a trait method and two nested `fn`s, because `#[stack_safe]`
/// writes each rewritten body beside its member and a trait impl has no room for one; the three
/// share one driver, so a nested term never costs a native frame.
#[stack_safe(data_in_frame)]
mod sections {
    use super::*;

    pub(super) fn find_sections_of(
        this: &Term,
        tail: &SectionCell,
        binders: &mut HashMap<Term, SectionCell>,
        memo: &mut Memo,
        insert: bool,
    ) -> FindResult {
        match this.repr() {
            ATerm::Constant(_, _) | ATerm::Global(_, _) => return vec![],
            // an annotated term is never bound: a `:pattern` must stay directly under its
            // quantifier. It is walked at each occurrence, so its sub-term is referenced at each
            // occurrence too and gets bound in its place when it is shared.
            ATerm::Annotated(t, _) => return find_sections_of(t, tail, binders, memo, true),
            _ => {}
        }
        // a term already walked in this section is only referenced once more; its sub-terms have
        // been counted by its first walk
        if let Some(r) = memo.lookup(this, tail) {
            if insert {
                record_reference(this, &r);
            }
            return r;
        }
        let mut insert = insert;
        let r: FindResult = match this.repr() {
            ATerm::Constant(_, _) => vec![],
            ATerm::Global(_, _) => vec![],
            ATerm::Local(id) => {
                // first find the binding section, the only one the variable depends on
                let cell = find_bound_section(tail, id.symbol.as_str()).unwrap();
                let mut acc = vec![(cell.clone(), Some(0))];
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
                find_sections_binder(vs, t, tail, binders, memo)
            }
            ATerm::Annotated(_, _) => unreachable!(), // handled above
            ATerm::Eq(a, b) => {
                let ra = find_sections_of(a, tail, binders, memo, true);
                let rb = find_sections_of(b, tail, binders, memo, true);
                combine(vec![ra, rb], tail)
            }
            ATerm::App(_, ts, _)
            | ATerm::Distinct(ts)
            | ATerm::And(ts)
            | ATerm::Or(ts)
            | ATerm::Xor(ts) => find_sections_slice(ts, tail, binders, memo),
            ATerm::Implies(a, b) => {
                let mut res: Vec<FindResult> = Vec::with_capacity(a.len() + 1);
                let mut i = 0usize;
                while i < a.len() {
                    res.push(find_sections_of(&a[i], tail, binders, memo, true));
                    i += 1;
                }
                res.push(find_sections_of(b, tail, binders, memo, true));
                combine(res, tail)
            }
            ATerm::Not(t) => {
                let rt = find_sections_of(t, tail, binders, memo, true);
                combine(vec![rt], tail)
            }
            ATerm::Ite(b, t, e) => {
                // the three branches are combined exactly as a slice's elements are, but naming
                // them here keeps the built `[b, t, e]` out of the recursive call.
                let rb = find_sections_of(b, tail, binders, memo, true);
                let rt = find_sections_of(t, tail, binders, memo, true);
                let re = find_sections_of(e, tail, binders, memo, true);
                let res: Vec<FindResult> = vec![rb, rt, re];
                combine(res, tail)
            }
            ATerm::Matching(t, cases) => {
                let tr = find_sections_of(t, tail, binders, memo, true);
                let mut vc: Vec<FindResult> = vec![tr];
                let arms: &[PatternArm] = cases;
                let mut i = 0usize;
                while i < arms.len() {
                    let case = &arms[i];
                    let sub: SectionCell = extend_cell(
                        tail.clone(),
                        &case
                            .pattern
                            .variables()
                            .into_iter()
                            .cloned()
                            .collect::<Vec<_>>(),
                    );
                    binders.insert(case.body.clone(), sub.clone());
                    // read before the recursion, which `sub` is lent to, as in a quantifier
                    let sub_level = sub.borrow().level;
                    let mut arm_r = find_sections_of(&case.body, &sub, binders, memo, true);
                    // we don't want glbs to return the Section under binder
                    leave_section(&mut arm_r, sub_level);
                    vc.push(arm_r);
                    i += 1;
                }
                combine(vc, tail)
            }
        };

        if insert {
            record_reference(this, &r);
        }
        if let Some((c, _)) = r.last() {
            let id = c.borrow().id;
            memo.results.insert((this.clone(), id), r.clone());
        }

        r
    }

    pub(super) fn find_sections_slice(
        ts: &[Term],
        tail: &SectionCell,
        binders: &mut HashMap<Term, SectionCell>,
        memo: &mut Memo,
    ) -> FindResult {
        let mut res: Vec<FindResult> = Vec::with_capacity(ts.len());
        let mut i = 0usize;
        while i < ts.len() {
            res.push(find_sections_of(&ts[i], tail, binders, memo, true));
            i += 1;
        }
        combine(res, tail)
    }

    /// `T` is concrete where the nested `fn` this came from was generic: a cycle shares one driver,
    /// so a member's parameter has one instantiation for the whole group, and `find_sections_of`
    /// calls this at `Sort`. That was the only instantiation the nested `fn` ever had.
    pub(super) fn find_sections_binder(
        vs: &[VarBinding<Str, Sort>],
        t: &Term,
        tail: &SectionCell,
        binders: &mut HashMap<Term, SectionCell>,
        memo: &mut Memo,
    ) -> FindResult {
        let mut names: Vec<Str> = Vec::with_capacity(vs.len());
        let mut i = 0usize;
        while i < vs.len() {
            names.push(vs[i].0.clone());
            i += 1;
        }
        let sub: SectionCell = extend_cell(tail.clone(), &names);
        binders.insert(t.clone(), sub.clone());
        // Read before the recursion: `sub` is lent to it, and a section's level never changes once
        // it is built, so reading it early is the same answer.
        let sub_level = sub.borrow().level;
        let mut r = find_sections_of(t, &sub, binders, memo, true);
        leave_section(&mut r, sub_level);
        // the binder sits one level above its body, which lands in an outer section when it uses
        // none of the bound variables
        combine(vec![r], tail)
    }
}

/// Re-introduce let bindings to `Self` when appropriate
///
/// This is implementation detailed; not to be exposed
trait TopoLetIntroImpl<E> {
    /// Reconstruct Self with lets, given necessary information
    fn let_intro(
        &self,
        cell: SectionCell,
        binders: &mut HashMap<Term, SectionCell>,
        vars: &mut HashMap<Term, Local>,
        env: &mut E,
    ) -> Self;
}

impl<E> TopoLetIntroImpl<E> for Term
where
    E: HasArenaAlt,
{
    fn let_intro(
        &self,
        cell: SectionCell,
        binders: &mut HashMap<Term, SectionCell>,
        vars: &mut HashMap<Term, Local>,
        env: &mut E,
    ) -> Self {
        introduce::let_intro_scope(self, cell, binders, vars, env)
    }
}

/// The bodies of [`TopoLetIntroImpl`] for a term, and the two helpers they recurse through. Free
/// functions for the same reason as [`sections`]: `#[stack_safe]` writes each rewritten body beside
/// its member, and a trait impl has no room for one. All four share a driver, so a term's depth and
/// its let-nesting both cost heap rather than stack.
#[stack_safe(data_in_frame)]
mod introduce {
    use super::*;

    /// Invariant: if a term is in let_hierarchy and referenced more than once, then it has to be in vars
    pub(super) fn let_intro_body_of<E>(
        this: &Term,
        cell: SectionCell,
        binders: &mut HashMap<Term, SectionCell>,
        vars: &mut HashMap<Term, Local>,
        top: bool,
        env: &mut E,
    ) -> Term
    where
        E: HasArenaAlt,
    {
        if !top {
            let mut it = cell.clone();
            loop {
                if let Some(rec) = it.borrow().let_hierarchy.get(this) {
                    if rec.referenced > 1 {
                        return env.arena_alt().local(vars.get(this).unwrap().clone());
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
        match this.repr() {
            ATerm::Constant(_, _) | ATerm::Global(_, _) | ATerm::Local(_) => this.clone(),
            ATerm::App(id, ts, sort) => {
                let args = let_intro_body_vec(ts, cell, binders, vars, false, env);
                env.arena_alt().app(id.clone(), args, sort.clone())
            }
            ATerm::Let(_, _) => unreachable!(),
            ATerm::Exists(vs, t) => {
                let nt = let_intro_quantifier_body(t, binders, vars, env);
                env.arena_alt().exists(vs.clone(), nt)
            }
            ATerm::Forall(vs, t) => {
                let nt = let_intro_quantifier_body(t, binders, vars, env);
                env.arena_alt().forall(vs.clone(), nt)
            }
            ATerm::Annotated(t, ans) => {
                let nt = let_intro_body_of(t, cell, binders, vars, false, env);
                env.arena_alt().annotated(nt, ans.clone())
            }
            ATerm::Eq(a, b) => {
                let na = let_intro_body_of(a, cell.clone(), binders, vars, false, env);
                let nb = let_intro_body_of(b, cell, binders, vars, false, env);
                env.arena_alt().eq(na, nb)
            }
            ATerm::Distinct(ts) => {
                let nts = let_intro_body_vec(ts, cell, binders, vars, false, env);
                env.arena_alt().distinct(nts)
            }
            ATerm::And(ts) => {
                let nts = let_intro_body_vec(ts, cell, binders, vars, false, env);
                env.arena_alt().and(nts)
            }
            ATerm::Or(ts) => {
                let nts = let_intro_body_vec(ts, cell, binders, vars, false, env);
                env.arena_alt().or(nts)
            }
            ATerm::Xor(ts) => {
                let nts = let_intro_body_vec(ts, cell, binders, vars, false, env);
                env.arena_alt().xor(nts)
            }
            ATerm::Implies(a, b) => {
                let na = let_intro_body_vec(a, cell.clone(), binders, vars, false, env);
                let nb = let_intro_body_of(b, cell, binders, vars, false, env);
                env.arena_alt().implies(na, nb)
            }
            ATerm::Not(t) => {
                let nt = let_intro_body_of(t, cell, binders, vars, false, env);
                env.arena_alt().not(nt)
            }
            ATerm::Ite(b, t, e) => {
                let nb = let_intro_body_of(b, cell.clone(), binders, vars, false, env);
                let nt = let_intro_body_of(t, cell.clone(), binders, vars, false, env);
                let ne = let_intro_body_of(e, cell, binders, vars, false, env);
                env.arena_alt().ite(nb, nt, ne)
            }
            ATerm::Matching(t, cases) => {
                let nt = let_intro_body_of(t, cell, binders, vars, false, env);
                let mut ncases: Vec<PatternArm> = vec![];
                let arms: &[PatternArm] = cases;
                let mut i = 0usize;
                while i < arms.len() {
                    let sub = binders.get(&arms[i].body).unwrap().clone();
                    let nbody = let_intro_scope(&arms[i].body, sub, binders, vars, env);
                    let ncase = PatternArm {
                        pattern: arms[i].pattern.clone(),
                        body: nbody,
                    };
                    ncases.push(ncase);
                    i += 1;
                }
                env.arena_alt().matching(nt, ncases)
            }
        }
    }

    /// [`let_intro_body_of`] over a term's arguments. The slice's own [`TopoLetIntroImpl`] would
    /// recurse into the trait, which starts a fresh driver per level.
    pub(super) fn let_intro_body_vec<E>(
        ts: &[Term],
        cell: SectionCell,
        binders: &mut HashMap<Term, SectionCell>,
        vars: &mut HashMap<Term, Local>,
        top: bool,
        env: &mut E,
    ) -> Vec<Term>
    where
        E: HasArenaAlt,
    {
        let mut out: Vec<Term> = Vec::with_capacity(ts.len());
        let mut i = 0usize;
        while i < ts.len() {
            out.push(let_intro_body_of(
                &ts[i],
                cell.clone(),
                binders,
                vars,
                top,
                env,
            ));
            i += 1;
        }
        out
    }

    /// The body of a quantifier. An annotation on it (e.g. `:pattern`) must stay directly under
    /// the quantifier, so the lets go inside it.
    pub(super) fn let_intro_quantifier_body<E>(
        t: &Term,
        binders: &mut HashMap<Term, SectionCell>,
        vars: &mut HashMap<Term, Local>,
        env: &mut E,
    ) -> Term
    where
        E: HasArenaAlt,
    {
        let sub = binders.get(t).unwrap().clone();
        let_intro_scope(t, sub, binders, vars, env)
    }

    /// The lets of `cell` around `t`, inside `t`'s annotation if it has one: an assertion's
    /// `:named` and a quantifier's `:pattern` both stay outermost.
    pub(super) fn let_intro_scope<E>(
        t: &Term,
        cell: SectionCell,
        binders: &mut HashMap<Term, SectionCell>,
        vars: &mut HashMap<Term, Local>,
        env: &mut E,
    ) -> Term
    where
        E: HasArenaAlt,
    {
        if let ATerm::Annotated(inner, ans) = t.repr() {
            let ni = let_intro_of(inner, cell, binders, vars, env);
            env.arena_alt().annotated(ni, ans.clone())
        } else {
            let_intro_of(t, cell, binders, vars, env)
        }
    }

    pub(super) fn let_intro_of<E>(
        this: &Term,
        cell: SectionCell,
        binders: &mut HashMap<Term, SectionCell>,
        vars: &mut HashMap<Term, Local>,
        env: &mut E,
    ) -> Term
    where
        E: HasArenaAlt,
    {
        let bindings = cell.borrow().get_let_bindings();
        wrap_level(this, cell, binders, vars, env, bindings, 0)
    }

    /// Wrap one dependency level of let-bindings around `t`, then the next, innermost last.
    pub(super) fn wrap_level<E>(
        t: &Term,
        cell: SectionCell,
        binders: &mut HashMap<Term, SectionCell>,
        vars: &mut HashMap<Term, Local>,
        env: &mut E,
        bindings: Vec<Vec<Term>>,
        i: usize,
    ) -> Term
    where
        E: HasArenaAlt,
    {
        if i >= bindings.len() {
            // not `top`: a scope's body is itself bound in an outer section when it uses none of
            // the scope's variables and is shared
            let_intro_body_of(t, cell, binders, vars, false, env)
        } else {
            let mut vs = vec![];
            let mut k = 0usize;
            while k < bindings[i].len() {
                // Cloned rather than borrowed: `bindings` moves into the next level below, and a
                // term is a handle, so the clone costs nothing.
                let bt: Term = bindings[i][k].clone();
                let id = env.arena_alt().new_local();
                let symbol = fresh_let_name(&cell, env.arena_alt());
                let sort = bt.get_sort(env);
                let nt = let_intro_body_of(&bt, cell.clone(), binders, vars, true, env);
                vs.push(VarBinding(symbol.clone(), id, nt.clone()));
                let loc = Local { id, symbol, sort };
                vars.insert(bindings[i][k].clone(), loc);
                k += 1;
            }
            let res = wrap_level(t, cell, binders, vars, env, bindings, 1 + i);
            env.arena_alt().let_term(vs, res)
        }
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
        // the walk assumes no lets; eliminating them leaves a let-free term as it is
        let this = self.let_elim(&mut ArenaRef(env.arena_alt()));
        let cell = Rc::new(RefCell::new(Section::new()));
        cell.borrow_mut().root.used_names = used_symbols(&this);
        let mut map = HashMap::new();
        let _ = this.find_sections(&cell, &mut map, false);
        let mut vars = HashMap::new();
        this.let_intro(cell, &mut map, &mut vars, env)
    }

    fn topo_print(&self, env: &mut E) -> String {
        self.topo_let_intro(env).to_string()
    }
}

#[cfg(test)]
mod tests {
    use crate::allocator::TermAllocator;
    use crate::ast::letintro::TopoLetIntro;
    use crate::ast::{ATerm, Context, LetElim, Typecheck};
    use crate::traits::Repr;
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
        assert_eq!(s, "(let ((x-0 (* (+ 1 2) 3))) (+ x-0 x-0))");
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
            "(let ((x-0 (+ 1 2))) (and (forall ((x Int) (y Int)) (let ((x-1 (* x-0 (+ x y)))) (= (+ x-1 x-1) 10))) (= x-0 10)))"
        );
    }

    /// Type-check `decls` and then `s` in the same context
    fn topo_print_with(decls: &str, s: &str) -> String {
        let mut context = Context::default();
        context.ensure_logic();
        for c in UntypedAst.parse_script_str(decls).unwrap() {
            c.type_check(&mut context).unwrap();
        }
        let term = UntypedAst.parse_term_str(s).unwrap();
        let term = term.type_check(&mut context).unwrap();
        let out = term.topo_let_intro(&mut context);
        // eliminating the lets again gives back the term itself, bound variables included
        assert_eq!(out.let_elim(&mut context), term.let_elim(&mut context));
        out.to_string()
    }

    /// `=`, `not` and `=>` must sit one level above their arguments, or their binding refers to a
    /// variable of the same parallel `let`.
    #[test]
    fn test_printing_eq_not_implies() {
        let decls = "(declare-fun f (Int) Int) (declare-fun p (Int) Bool) (declare-const a Int) (declare-const b Int)";
        let s = topo_print_with(decls, "(and (= (f a) b) (= (f a) b) (p (f a)))");
        assert_eq!(
            s,
            "(let ((x-0 (f a))) (let ((x-1 (= x-0 b))) (and x-1 x-1 (p x-0))))"
        );
        let s = topo_print_with(decls, "(and (not (p (f a))) (not (p (f a))) (p (f a)))");
        assert_eq!(
            s,
            "(let ((x-0 (p (f a)))) (let ((x-1 (not x-0))) (and x-1 x-1 x-0)))"
        );
        let s = topo_print_with(
            decls,
            "(and (=> (p (f a)) (p b)) (=> (p (f a)) (p b)) (p (f a)))",
        );
        assert_eq!(
            s,
            "(let ((x-0 (p (f a)))) (let ((x-1 (=> x-0 (p b)))) (and x-1 x-1 x-0)))"
        );
    }

    /// The lets of a quantifier body go inside its `!`, so the attribute stays directly under the
    /// quantifier.
    #[test]
    fn test_printing_annotated_quantifier() {
        let decls = "(declare-fun f (Int) Int) (declare-fun g (Int Int) Int)";
        let s = topo_print_with(
            decls,
            "(forall ((x Int)) (! (and (> (g (f x) 1) 0) (< (g (f x) 1) 5)) :pattern ((f x))))",
        );
        assert_eq!(
            s,
            "(forall ((x Int)) (! (let ((x-0 (g (f x) 1))) (and (> x-0 0) (< x-0 5))) :pattern ((f x))))"
        );
    }

    /// Pattern variables are bound in the arm's own section.
    #[test]
    fn test_printing_match() {
        let decls = "(declare-datatype L ((nil) (cons (hd Int) (tl L)))) (declare-const l L)";
        let s = topo_print_with(
            decls,
            "(match l ((nil 0) ((cons h t) (+ (* h h) (* h h)))))",
        );
        assert_eq!(
            s,
            "(match l ((nil 0) ((cons h t) (let ((x-0 (* h h))) (+ x-0 x-0)))))"
        );
    }

    /// `t_{i+1} = (g t_i t_i)` has `depth + 1` distinct nodes but `2^depth` tree nodes; the walk
    /// must follow the former.
    #[test]
    fn test_printing_dag() {
        let mut context = Context::default();
        context.ensure_logic();
        for c in UntypedAst
            .parse_script_str("(declare-fun g (Int Int) Int) (declare-const a Int)")
            .unwrap()
        {
            c.type_check(&mut context).unwrap();
        }
        let mut t = UntypedAst
            .parse_term_str("a")
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        let g = UntypedAst
            .parse_term_str("(g a a)")
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        let ATerm::App(gid, _, sort) = g.repr() else {
            unreachable!()
        };
        for _ in 0..64 {
            t = context.app(gid.clone(), vec![t.clone(), t], sort.clone());
        }
        let s = t.topo_print(&mut context);
        // x-0 binds `(g a a)` and each x-i binds `(g x-(i-1) x-(i-1))`
        let mut expected = "(let ((x-0 (g a a))) ".to_string();
        for i in 1..63 {
            expected.push_str(&format!("(let ((x-{i} (g x-{} x-{}))) ", i - 1, i - 1));
        }
        expected.push_str("(g x-62 x-62)");
        expected.push_str(&")".repeat(63));
        assert_eq!(s, expected);
    }

    /// Bindings of one level come in the order the walk meets them, whatever the hash order.
    #[test]
    fn test_printing_deterministic_order() {
        let decls = "(declare-fun f (Int) Int) (declare-fun p (Int) Bool) (declare-const a Int) (declare-const b Int)";
        let s = topo_print_with(decls, "(and (p (f a)) (p (f a)) (p (f b)) (p (f b)))");
        assert_eq!(
            s,
            "(let ((x-0 (p (f a))) (x-1 (p (f b)))) (and x-0 x-0 x-1 x-1))"
        );
    }

    /// Printing twice in one context gives the same names.
    #[test]
    fn test_printing_names_per_call() {
        let mut context = Context::default();
        context.ensure_logic();
        for c in UntypedAst
            .parse_script_str("(declare-fun f (Int) Int) (declare-const a Int)")
            .unwrap()
        {
            c.type_check(&mut context).unwrap();
        }
        let t = UntypedAst
            .parse_term_str("(+ (f a) (f a))")
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        assert_eq!(
            t.topo_print(&mut context),
            "(let ((x-0 (f a))) (+ x-0 x-0))"
        );
        assert_eq!(
            t.topo_print(&mut context),
            "(let ((x-0 (f a))) (+ x-0 x-0))"
        );
    }

    /// A let-bound variable does not shadow a symbol of the term.
    #[test]
    fn test_printing_avoids_used_names() {
        let decls = "(declare-fun f (Int) Int) (declare-const a Int) (declare-const x-0 Int)";
        let s = topo_print_with(decls, "(+ x-0 (f a) (f a))");
        assert_eq!(s, "(let ((x-1 (f a))) (+ x-0 x-1 x-1))");
    }

    /// A quantifier body that uses none of its variables is bound like any other term.
    #[test]
    fn test_printing_closed_quantifier_body() {
        let decls = "(declare-fun f (Int) Int) (declare-fun p (Int) Bool) (declare-const a Int)";
        let s = topo_print_with(
            decls,
            "(and (forall ((x Int)) (p (f a))) (p (f a)) (p (f a)))",
        );
        assert_eq!(
            s,
            "(let ((x-0 (p (f a)))) (and (forall ((x Int)) x-0) x-0 x-0))"
        );
        let s = topo_print_with(
            decls,
            "(and (forall ((x Int)) (! (p (f a)) :pattern ((f x)))) (p (f a)) (p (f a)))",
        );
        assert_eq!(
            s,
            "(let ((x-0 (p (f a)))) (and (forall ((x Int)) (! x-0 :pattern ((f x)))) x-0 x-0))"
        );
    }

    /// The lets of the whole term go inside a top-level annotation.
    #[test]
    fn test_printing_named() {
        let decls = "(declare-fun f (Int) Int) (declare-fun p (Int) Bool) (declare-const a Int)";
        let s = topo_print_with(decls, "(! (and (p (f a)) (p (f a))) :named n1)");
        assert_eq!(s, "(! (let ((x-0 (p (f a)))) (and x-0 x-0)) :named n1)");
    }

    /// Lets in the input are eliminated first.
    #[test]
    fn test_printing_let_input() {
        let decls = "(declare-fun f (Int) Int) (declare-const a Int)";
        let s = topo_print_with(decls, "(let ((y (f a))) (+ y y))");
        assert_eq!(s, "(let ((x-0 (f a))) (+ x-0 x-0))");
    }

    const DECLS: &str = "(declare-fun f (Int) Int) (declare-fun g (Int Int) Int) (declare-fun p (Int) Bool) (declare-const a Int) (declare-const b Int) (declare-datatype L ((nil) (cons (hd Int) (tl L)))) (declare-const l L)";

    /// Check each `(input, expected output)`
    fn check_all(cases: &[(&str, &str)]) {
        for (t, expected) in cases {
            assert_eq!(topo_print_with(DECLS, t), *expected, "for {t}");
        }
    }

    /// The connectives not covered elsewhere
    #[test]
    fn test_printing_connectives() {
        check_all(&[
            (
                "(exists ((x Int)) (and (p (f x)) (p (f x))))",
                "(exists ((x Int)) (let ((x-0 (p (f x)))) (and x-0 x-0)))",
            ),
            (
                "(and (distinct (f a) b) (distinct (f a) b) (xor (p (f a)) (p b)) (xor (p (f a)) (p b)))",
                "(let ((x-0 (f a))) (let ((x-1 (distinct x-0 b))) (let ((x-2 (xor (p x-0) (p b)))) (and x-1 x-1 x-2 x-2))))",
            ),
            (
                "(+ (ite (p (f a)) (f a) b) (ite (p (f a)) (f a) b))",
                "(let ((x-0 (f a))) (let ((x-1 (ite (p x-0) x-0 b))) (+ x-1 x-1)))",
            ),
            // `(f a)` occurs only inside the shared `=>`, which prints it once
            (
                "(and (=> (p (f a)) (p b) (p a)) (=> (p (f a)) (p b) (p a)))",
                "(let ((x-0 (=> (p (f a)) (p b) (p a)))) (and x-0 x-0))",
            ),
            // an annotation is never bound, but what it annotates is
            (
                "(and (! (p (f a)) :weight 3) (! (p (f a)) :weight 3) (p (f a)))",
                "(let ((x-0 (p (f a)))) (and (! x-0 :weight 3) (! x-0 :weight 3) x-0))",
            ),
        ]);
    }

    /// A term is bound in the innermost section whose variables it uses
    #[test]
    fn test_printing_nested_binders() {
        check_all(&[
            // shared across sibling quantifiers
            (
                "(and (forall ((x Int)) (p (g (f a) x))) (forall ((y Int)) (p (g (f a) y))) (p (f a)))",
                "(let ((x-0 (f a))) (and (forall ((x Int)) (p (g x-0 x))) (forall ((y Int)) (p (g x-0 y))) (p x-0)))",
            ),
            // an outer variable used under inner quantifiers
            (
                "(forall ((x Int)) (and (forall ((y Int)) (= (g (f x) y) (g (f x) y))) (forall ((y Int)) (p (g (f x) y))) (p (f x))))",
                "(forall ((x Int)) (let ((x-0 (f x))) (and (forall ((y Int)) (let ((x-1 (g x-0 y))) (= x-1 x-1))) (forall ((y Int)) (p (g x-0 y))) (p x-0))))",
            ),
            // the two `(p (f x))` are of different variables
            (
                "(forall ((x Int)) (and (p (f x)) (forall ((x Int)) (and (p (f x)) (p (f x))))))",
                "(forall ((x Int)) (and (p (f x)) (forall ((x Int)) (let ((x-0 (p (f x)))) (and x-0 x-0)))))",
            ),
            // quantifiers parsed apart bind different variables, so they are not shared
            (
                "(and (forall ((x Int)) (p (f x))) (forall ((x Int)) (p (f x))))",
                "(and (forall ((x Int)) (p (f x))) (forall ((x Int)) (p (f x))))",
            ),
            (
                "(and (exists ((y Int)) (and (p y) (forall ((x Int)) (p (g (f a) x))))) (exists ((z Int)) (and (p z) (forall ((x Int)) (p (g (f a) x))))))",
                "(let ((x-0 (f a))) (and (exists ((y Int)) (and (p y) (forall ((x Int)) (p (g x-0 x))))) (exists ((z Int)) (and (p z) (forall ((x Int)) (p (g x-0 x)))))))",
            ),
        ]);
    }

    #[test]
    fn test_printing_match_sharing() {
        check_all(&[
            // shared between the arms and outside the match
            (
                "(+ (match l ((nil (f a)) ((cons h t) (+ (f a) (g h (f a)) (g h (f a)))))) (f a))",
                "(let ((x-0 (f a))) (+ (match l ((nil x-0) ((cons h t) (let ((x-1 (g h x-0))) (+ x-0 x-1 x-1))))) x-0))",
            ),
            // a quantified variable used in the arms
            (
                "(forall ((x Int)) (= 0 (match l ((nil (f x)) ((cons h t) (+ (f x) (g h h) (g h h)))))))",
                "(forall ((x Int)) (let ((x-0 (f x))) (= 0 (match l ((nil x-0) ((cons h t) (let ((x-1 (g h h))) (+ x-0 x-1 x-1))))))))",
            ),
        ]);
    }

    /// One quantifier term, shared: inside another binder and at the top
    #[test]
    fn test_printing_shared_quantifier() {
        let mut context = Context::default();
        context.ensure_logic();
        for c in UntypedAst.parse_script_str(DECLS).unwrap() {
            c.type_check(&mut context).unwrap();
        }
        let parse = |s: &str, ctx: &mut Context| {
            UntypedAst
                .parse_term_str(s)
                .unwrap()
                .type_check(ctx)
                .unwrap()
        };
        let q = parse("(forall ((x Int)) (and (p (f x)) (p (f x))))", &mut context);
        let e = parse("(exists ((y Int)) (p y))", &mut context);
        let ATerm::Exists(vs, body) = e.repr() else {
            unreachable!()
        };
        let nb = context.and(vec![body.clone(), q.clone()]);
        let e1 = context.exists(vs.clone(), nb);
        let t = context.and(vec![e1, q.clone()]);
        let out = t.topo_let_intro(&mut context);
        assert_eq!(out.let_elim(&mut context), t);
        assert_eq!(
            out.to_string(),
            "(let ((x-0 (forall ((x Int)) (let ((x-1 (p (f x)))) (and x-1 x-1))))) (and (exists ((y Int)) (and (p y) x-0)) x-0))"
        );
        let t = context.and(vec![q.clone(), q]);
        let out = t.topo_let_intro(&mut context);
        assert_eq!(out.let_elim(&mut context), t);
        assert_eq!(
            out.to_string(),
            "(let ((x-0 (forall ((x Int)) (let ((x-1 (p (f x)))) (and x-1 x-1))))) (and x-0 x-0))"
        );
    }
}

#[cfg(test)]
mod stack_safety {
    use super::*;
    use crate::allocator::ObjectAllocatorExt;
    use crate::ast::letintro::TopoLetIntro;
    use crate::ast::{Arena, FlatConnectivesExt};

    /// `(and x (or x (and x (or x …))))`, nested `depth` deep. Alternating so that `flat_and` and
    /// `flat_or` cannot collapse the nesting.
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

    /// Covers both cycles: `topo_let_intro` runs `find_sections` and then `let_intro`.
    #[test]
    fn topo_let_intro_is_flat() {
        let ok = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut arena = Arena::default();
                let t = deep_alternating(&mut arena, 20_000);
                let out = t.topo_let_intro(&mut arena);
                std::mem::forget((t, out));
                true
            })
            .expect("spawn")
            .join();
        assert_eq!(ok.ok(), Some(true));
    }
}
