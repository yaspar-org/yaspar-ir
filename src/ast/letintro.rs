// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! # Let-introduction in A Topological Order
//!
//! A hash-consed term is a DAG, but printing it expands every shared sub-term at each of its
//! occurrences. [TopoLetIntro] binds each shared sub-term to a variable instead, so that
//! ```smt2
//! (* (+ 1 2) (+ 1 2))
//! ```
//! prints as
//! ```smt2
//! (let ((x-0 (+ 1 2))) (* x-0 x-0))
//! ```
//!
//! The algorithm walks the distinct nodes of the DAG, never its tree:
//!
//! 1. **Scope.** A sub-term can only be bound where its free variables are in scope, so its scope
//!    is the innermost binder (a quantifier, or a `match` arm) of one of its free variables, or
//!    the whole term if it has none. Variables are told apart by id; each binder has its own.
//! 2. **Sharing.** A sub-term is bound when it is printed more than once, i.e. when it occurs at
//!    least twice among the sub-terms that are printed. Locals, constants and globals are never
//!    bound, nor is an annotation, since a `:pattern` must stay directly under its quantifier.
//! 3. **Layers.** A bound sub-term is placed one layer above the bound sub-terms it uses, and the
//!    bindings of a scope are wrapped around its body layer by layer, so a binding only refers to
//!    earlier ones. The lets of an annotated body go inside the annotation.
//!
//! Lets in the input are eliminated first. Every bound variable is given a fresh name, as the
//! printed text refers to variables by name and eliminating a let can put a variable under a
//! binder of the same name. Every pass is a recursion over the nodes, memoized by node and made
//! stack safe by `#[stack_safe]`, so the depth of the term costs no stack.

use crate::allocator::{LocalVarAllocator, TermAllocator};
use crate::ast::alg::{LocalId, VarBinding};
use crate::ast::{
    ATerm, Arena, Attribute, FetchSort, FreshVar, HasArena, LetElim, Local, Pattern, PatternArm,
    Sort, Str, Term,
};
use crate::traits::Repr;
use std::collections::{HashMap, HashSet};
use yaspar_macros::stack_safe;

// ── The entry point ──────────────────────────────────────────────────────────────────────────────

/// Re-introduce lets to `Self` based on topological sorting
pub trait TopoLetIntro<E> {
    fn topo_let_intro(&self, env: &mut E) -> Self;

    fn topo_print(&self, env: &mut E) -> String;
}

impl<E> TopoLetIntro<E> for Term
where
    E: HasArena,
{
    fn topo_let_intro(&self, env: &mut E) -> Self {
        let dag = Dag::new(self);
        if !dag.has_let {
            return let_intro(&dag, env.arena());
        }
        // the steps assume no lets, so they are eliminated first, and the DAG is made again
        let this = self.let_elim(env);
        let_intro(&Dag::new(&this), env.arena())
    }

    fn topo_print(&self, env: &mut E) -> String {
        self.topo_let_intro(env).to_string()
    }
}

/// Let-introduction on the DAG of a let-free term. Each step is a function of its own:
///
/// 1. [scopes]: what each node depends on, from which [Scopes::scope] finds where it may be bound;
/// 2. [shared]: which nodes are bound, being printed more than once;
/// 3. [layers] and [bindings_of]: the order of the bindings in each scope;
/// 4. [binder_names]: a fresh name for each bound variable;
/// 5. [build]: the term rebuilt with its lets, a fresh variable for each binding, and the bound
///    variables renamed.
fn let_intro(dag: &Dag, arena: &mut Arena) -> Term {
    let root = dag.order[dag.order.len() - 1];
    let scopes = scopes(dag);
    let bound = shared(dag, root);
    let layer = layers(dag, &bound);
    let bindings = bindings_of(dag, &scopes, &bound, &layer);
    let names = binder_names(dag, arena);
    let cx = Builder {
        dag,
        bindings: &bindings,
        names: &names,
    };
    wrap(None, root, &cx, &mut Built::default(), arena)
}

// ── The term as a DAG of its distinct sub-terms ──────────────────────────────────────────────────

/// The sub-terms of `t`, in order. The terms of an annotation are not among them: they are
/// printed as they are.
fn children(t: &Term) -> Vec<&Term> {
    match t.repr() {
        ATerm::Constant(_, _) | ATerm::Global(_, _) | ATerm::Local(_) => vec![],
        ATerm::App(_, ts, _)
        | ATerm::Distinct(ts)
        | ATerm::And(ts)
        | ATerm::Or(ts)
        | ATerm::Xor(ts) => ts.iter().collect(),
        ATerm::Let(vs, b) => vs.iter().map(|v| &v.2).chain([b]).collect(),
        ATerm::Exists(_, b) | ATerm::Forall(_, b) | ATerm::Not(b) | ATerm::Annotated(b, _) => {
            vec![b]
        }
        ATerm::Eq(a, b) => vec![a, b],
        ATerm::Implies(ts, b) => ts.iter().chain([b]).collect(),
        ATerm::Ite(b, t, e) => vec![b, t, e],
        ATerm::Matching(s, arms) => [s]
            .into_iter()
            .chain(arms.iter().map(|a| &a.body))
            .collect(),
    }
}

/// A term as the DAG of its distinct sub-terms. A node is borrowed from its parent, so all of
/// them live as long as the root.
///
/// For `(+ (* a a) (* a a))`: `kids` maps `(+ …)` to `[(* a a), (* a a)]`, `(* a a)` to `[a, a]`
/// and `a` to `[]`, and `order` is `[a, (* a a), (+ …)]`.
#[derive(Default)]
struct Dag<'a> {
    /// each node's children, in order and with repeats, as [children] lists them
    kids: HashMap<&'a Term, Vec<&'a Term>>,
    /// the nodes in post-order: children before their parent, left to right, and the root last.
    /// The passes do not need an order, but the output does: bindings are listed in this order,
    /// so that it does not depend on the order of a hash map.
    order: Vec<&'a Term>,
    /// the smallest depth at which [Dag::visit] reaches each node, the root being at depth 0.
    /// Only the depths of binders are compared: see [Scopes::scope].
    depths: HashMap<&'a Term, usize>,
    /// whether the term has a `let`, which the steps of [let_intro] do not expect
    has_let: bool,
}

impl<'a> Dag<'a> {
    fn new(root: &'a Term) -> Self {
        let mut dag = Dag::default();
        dag.visit(root, 0);
        dag
    }

    /// Add `t` and the nodes below it to `dag`, unless it is there already; a node is added once its
    /// children are, so `order` is a post-order
    ///
    /// `t` is at depth `depth`. A node is reached once per parent, but its children are added on
    /// the first reach only, so its depth is the smallest of those reaches.
    #[stack_safe]
    fn visit(&mut self, t: &'a Term, depth: usize) {
        if let Some(d) = self.depths.get_mut(t) {
            *d = (*d).min(depth);
            return;
        }
        self.depths.insert(t, depth);
        self.has_let |= matches!(t.repr(), ATerm::Let(..));
        let cs: Vec<&'a Term> = children(t);
        for i in 0..cs.len() {
            self.visit(cs[i], depth + 1);
        }
        self.kids.insert(t, cs);
        self.order.push(t);
    }
}

// ── Binders: the quantifiers and `match` arms, and the scopes they open ──────────────────────────

/// A binder: the quantifier `node` (with `arm` 0), or the `arm`-th arm of the `match` `node`
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Binder<'a> {
    node: &'a Term,
    arm: usize,
}

impl<'a> Binder<'a> {
    /// The binder whose body is child `k` of `t`: a quantifier's body, or a `match` arm's
    fn of_child(t: &'a Term, k: usize) -> Option<Self> {
        match t.repr() {
            ATerm::Exists(..) | ATerm::Forall(..) => Some(Binder { node: t, arm: 0 }),
            ATerm::Matching(..) if k > 0 => Some(Binder {
                node: t,
                arm: k - 1,
            }),
            _ => None,
        }
    }
}

/// Where a binding can be placed: the body of a binder, or the whole term ([None])
type Scope<'a> = Option<Binder<'a>>;

/// The variables each binder of `t` binds, with the binder's arm: a quantifier's (arm 0), or each
/// `match` arm's
fn bound_ids(t: &Term) -> Vec<(usize, Vec<LocalId>)> {
    match t.repr() {
        ATerm::Exists(vs, _) | ATerm::Forall(vs, _) => vec![(0, vs.iter().map(|v| v.1).collect())],
        ATerm::Matching(_, arms) => arms
            .iter()
            .enumerate()
            .map(|(i, a)| {
                let ids = a.pattern.variables_and_ids().into_iter().map(|v| v.1);
                (i, ids.collect())
            })
            .collect(),
        _ => vec![],
    }
}

/// The variables, as `(name, id)`, that the `arm`-th binder of `t` binds
fn bound_vars(t: &Term, arm: usize) -> Vec<(Str, LocalId)> {
    match t.repr() {
        ATerm::Exists(vs, _) | ATerm::Forall(vs, _) => {
            vs.iter().map(|v| (v.0.clone(), v.1)).collect()
        }
        ATerm::Matching(_, arms) => arms[arm].pattern.variables_and_ids(),
        _ => vec![],
    }
}

// ── Step 1: where each node may be bound ─────────────────────────────────────────────────────────

/// Step 1: the binders each node depends on, from which [Scopes::scope] finds the scope of a
/// node, i.e. where it may be bound.
fn scopes<'a>(dag: &'a Dag<'a>) -> Scopes<'a> {
    let mut binder_of: HashMap<LocalId, Binder<'a>> = HashMap::new();
    for &t in &dag.order {
        for (arm, ids) in bound_ids(t) {
            for id in ids {
                binder_of.insert(id, Binder { node: t, arm });
            }
        }
    }
    let mut used = HashMap::new();
    // the recursion reaches every node from the root
    binders_used(dag.order[dag.order.len() - 1], dag, &binder_of, &mut used);
    Scopes { dag, used }
}

/// The binders each node depends on
struct Scopes<'a> {
    dag: &'a Dag<'a>,
    used: HashMap<&'a Term, Vec<Binder<'a>>>,
}

impl<'a> Scopes<'a> {
    /// The scope of `t`, i.e. the innermost binder it depends on, or [None] for the whole term.
    /// In `(forall ((x Int)) (and (p x) (p a)))`, the scope of `(p x)` is the quantifier's body and
    /// that of `(p a)` is the whole term.
    ///
    /// `t` is inside every binder it depends on, so the deepest of those is the innermost. If `t`
    /// depends on `B1` and is inside the body of `B2`, then so does `B2`, so `B2` only occurs inside
    /// `B1`: every reach of `B2` happens while [Dag::visit] adds `B1`'s children, deeper than any
    /// reach of `B1`. The arms of one `match` share a depth, but a node is inside one arm only.
    fn scope(&self, t: &'a Term) -> Scope<'a> {
        self.used[t]
            .iter()
            .max_by_key(|b| self.dag.depths[b.node])
            .cloned()
    }
}

/// The binders `t` depends on: the quantifiers (and `match` arms) whose variables occur in it, not
/// counting binders inside `t` itself. `t` can only be let-bound where all of them are in scope.
///
/// In `(forall ((x Int)) (forall ((y Int)) (p (g x y) a)))`, `a` depends on no binder, `(g x y)`
/// on both quantifiers, and `(forall ((y Int)) …)` only on `forall x`, since `y` is bound inside
/// it.
///
/// A variable depends on its binder; any other node depends on what its children depend on,
/// except that a binder does not depend on itself.
#[stack_safe]
fn binders_used<'a>(
    t: &'a Term,
    dag: &Dag<'a>,
    binder_of: &HashMap<LocalId, Binder<'a>>,
    used: &mut HashMap<&'a Term, Vec<Binder<'a>>>,
) {
    if used.contains_key(t) {
        return;
    }
    let mut u: Vec<Binder<'a>> = vec![];
    if let ATerm::Local(l) = t.repr()
        && let Some(b) = binder_of.get(&l.id)
    {
        u.push(b.clone());
    }
    let mut k = 0usize;
    for c in &dag.kids[t] {
        binders_used(c, dag, binder_of, used);
        // the body of a binder depends on the binder, but the binder does not
        let own = Binder::of_child(t, k);
        for b in used[c].iter() {
            if own.as_ref() != Some(b) && !u.contains(b) {
                u.push(b.clone());
            }
        }
        k += 1;
    }
    used.insert(t, u);
}

// ── Step 2: which nodes are bound ────────────────────────────────────────────────────────────────

/// Step 2: the nodes that are bound to a variable, i.e. that would otherwise be printed more than
/// once. In `(+ (f (g a)) (f (g a)))`, `(f (g a))` is printed twice, so it is bound; `(g a)` is
/// then printed once, inside the binding of `(f (g a))`, so it is not.
fn shared<'a>(dag: &Dag<'a>, root: &'a Term) -> HashSet<&'a Term> {
    let mut parents: HashMap<&'a Term, Vec<&'a Term>> = HashMap::new();
    for (&p, cs) in &dag.kids {
        for &c in cs {
            parents.entry(c).or_default().push(p);
        }
    }
    let cx = Sharing { root, parents };
    let mut bound = HashSet::new();
    let mut pted = HashMap::new();
    for &t in &dag.order {
        let p = printed(t, &cx, &mut pted);
        if is_bound(t, p, root) {
            bound.insert(t);
        }
    }
    bound
}

/// Whether `t` may be bound at all. Locals, constants and globals are not, as their variable would
/// be no shorter. Neither is an annotation, as a `:pattern` must stay directly under its
/// quantifier; an annotation printed twice prints its child twice, which is then bound.
fn bindable(t: &Term) -> bool {
    !matches!(
        t.repr(),
        ATerm::Constant(..) | ATerm::Global(..) | ATerm::Local(_) | ATerm::Annotated(..)
    )
}

/// Whether `t`, printed `printed` times in place, is bound instead
fn is_bound(t: &Term, printed: usize, root: &Term) -> bool {
    t != root && printed > 1 && bindable(t)
}

/// What [printed] knows
struct Sharing<'a> {
    root: &'a Term,
    /// the parents of each node, once per occurrence as a child
    parents: HashMap<&'a Term, Vec<&'a Term>>,
}

/// How often `t` would be printed: the root once, and any other node once for each time one of
/// its parents prints it. A parent prints it as often as the parent is printed, except that a
/// bound parent is printed once, in its binding.
#[stack_safe]
fn printed<'a>(t: &'a Term, cx: &Sharing<'a>, pted: &mut HashMap<&'a Term, usize>) -> usize {
    if let Some(&n) = pted.get(t) {
        return n;
    }
    let mut n = 0;
    if t == cx.root {
        n = 1;
    } else {
        for &p in &cx.parents[t] {
            let pp = printed(p, cx, pted);
            n += if is_bound(p, pp, cx.root) { 1 } else { pp };
        }
    }
    pted.insert(t, n);
    n
}

// ── Step 3: the order of the bindings ────────────────────────────────────────────────────────────

/// Step 3: the layer of each node, so that a binding only refers to bindings of lower layers.
///
/// In `(and (= (f a) b) (= (f a) b) (p (f a)))`, `(f a)` and `(= (f a) b)` are bound. `(f a)` has
/// layer 0, and `(= (f a) b)` uses it, so has layer 1:
/// `(let ((x-0 (f a))) (let ((x-1 (= x-0 b))) (and x-1 x-1 (p x-0))))`.
fn layers<'a>(dag: &Dag<'a>, bound: &HashSet<&'a Term>) -> HashMap<&'a Term, usize> {
    let mut memo = HashMap::new();
    // the recursion reaches every node from the root
    layer(dag.order[dag.order.len() - 1], dag, bound, &mut memo);
    memo
}

/// The largest layer of the children of `t`, plus one for a bound child. An unbound child is
/// printed inside `t`, so whatever it uses `t` uses too; a bound child is referred to by its
/// variable, which must be bound in an earlier layer. Bound nodes of one layer do not use one
/// another, so they go in one parallel let.
#[stack_safe]
fn layer<'a>(
    t: &'a Term,
    dag: &Dag<'a>,
    bound: &HashSet<&'a Term>,
    memo: &mut HashMap<&'a Term, usize>,
) -> usize {
    if let Some(&l) = memo.get(t) {
        return l;
    }
    let mut l = 0;
    for c in &dag.kids[t] {
        let lc = layer(c, dag, bound, memo);
        l = l.max(lc + bound.contains(c) as usize);
    }
    memo.insert(t, l);
    l
}

/// The bound nodes of each scope, in groups of one layer each, the lowest layer first: each group
/// becomes one let, around the lets of the later groups. Only a bound node needs a scope, so it is
/// found here, for the bound nodes only. The sort is stable, so the nodes of one layer stay in
/// post-order, and the output does not depend on the order of a hash map.
fn bindings_of<'a>(
    dag: &Dag<'a>,
    scopes: &Scopes<'a>,
    bound: &HashSet<&'a Term>,
    layer: &HashMap<&'a Term, usize>,
) -> HashMap<Scope<'a>, Vec<Vec<&'a Term>>> {
    let mut bindings: HashMap<Scope<'a>, Vec<&'a Term>> = HashMap::new();
    for &t in dag.order.iter().filter(|t| bound.contains(*t)) {
        bindings.entry(scopes.scope(t)).or_default().push(t);
    }
    bindings
        .into_iter()
        .map(|(s, mut bs)| {
            bs.sort_by_key(|t| layer[t]);
            let groups = bs
                .chunk_by(|a, b| layer[a] == layer[b])
                .map(<[_]>::to_vec)
                .collect();
            (s, groups)
        })
        .collect()
}

// ── Step 4: fresh names for the bound variables ──────────────────────────────────────────────────

/// Step 4: a fresh name for each variable bound in the term, so that no binder captures a variable
/// of the same name; the original name is kept as the prefix
fn binder_names<'a>(dag: &Dag<'a>, arena: &mut Arena) -> HashMap<LocalId, Str> {
    let mut names = HashMap::new();
    for &t in &dag.order {
        for (arm, _) in bound_ids(t) {
            for (name, id) in bound_vars(t, arm) {
                names.insert(id, arena.fresh_var(name.as_str()));
            }
        }
    }
    names
}

// ── Step 5: the term rebuilt with its lets ───────────────────────────────────────────────────────

/// Step 5: what is needed to rebuild the term with its lets
struct Builder<'a> {
    dag: &'a Dag<'a>,
    /// the bindings of each scope, in groups of one layer each
    bindings: &'a HashMap<Scope<'a>, Vec<Vec<&'a Term>>>,
    /// the fresh name of each bound variable
    names: &'a HashMap<LocalId, Str>,
}

/// What [build] has made so far
#[derive(Default)]
struct Built<'a> {
    /// each node rebuilt: its definition, for a bound node
    out: HashMap<&'a Term, Term>,
    /// the variable of each bound node, made when its binding is
    vars: HashMap<&'a Term, Local>,
}

impl Builder<'_> {
    /// The new name of the bound variable `id`, or `old` for a variable bound outside the term
    fn name(&self, id: LocalId, old: &Str) -> Str {
        self.names.get(&id).unwrap_or(old).clone()
    }
}

/// Step 5: the term rebuilt with its lets, by three mutually recursive functions:
///
/// - [wrap] puts the lets of a scope around its body. It is called for the whole term, for the
///   body of each quantifier and for the body of each `match` arm. It gives each binding of the
///   scope its variable, then calls [build] for the binding's definition, and [refer] for the body.
/// - [refer] is how a node appears where it is used: its variable if it is bound, or what
///   [build] makes of it if it is printed in place.
/// - [build] rebuilds one node from its children, which it gets from [refer]; for a bound node,
///   that is its definition. A quantifier or `match` gets the body of each of its scopes from
///   [wrap], so each scope has its own lets.
///
/// They share `out`, a [Built]: each node is built once and remembered there, however often it is
/// referred to, and a binding's variable is made there before anything refers to it. Bound
/// variables are renamed along the way, by [Builder::name]. The terms of a `:pattern` are not
/// let-introduced, only renamed, by [rename_locals].
///
/// For `(and (forall ((x Int) (y Int)) (= (* (+ x y) (+ x y)) 10)) (or true false) (or true
/// false))`, where `(or true false)` is bound at the top and `(+ x y)` inside the quantifier:
///
/// ```text
/// wrap(None, (and …))
/// ├─ binding (or true false): variable x-1, then build → (or true false)
/// ├─ body: refer((and …)) → build((and …))
/// │   ├─ refer(forall …) → build(forall …)
/// │   │   └─ wrap(the forall's body, (= (* (+ x y) (+ x y)) 10))
/// │   │       ├─ binding (+ x y): variable x-2, then build → (+ x-0 y-0)
/// │   │       └─ body: refer → build → (= (* x-2 x-2) 10), wrapped in the let of x-2
/// │   ├─ refer((or true false)) → x-1
/// │   └─ refer((or true false)) → x-1
/// └─ (let ((x-1 (or true false))) (and (forall ((x-0 Int) (y-0 Int)) …) x-1 x-1))
/// ```
#[stack_safe]
mod building {
    use super::*;

    /// The body `b` of scope `s` (the whole term if `s` is [None]), with the lets of the scope
    /// around it.
    ///
    /// For each group of the scope's bindings, by layer, and each binding in it: its variable is
    /// made, before anything can refer to it, then its definition is built by [build]. The body
    /// is then made by [refer], so it is a variable if it is bound itself, and each group's let
    /// goes around it, the last group innermost. If `b` is annotated, the lets go inside the
    /// annotation, so that a `:pattern` stays directly under its quantifier.
    pub(super) fn wrap<'a>(
        s: Scope<'a>,
        b: &'a Term,
        cx: &Builder<'a>,
        out: &mut Built<'a>,
        arena: &mut Arena,
    ) -> Term {
        // one let per group of bindings
        let mut lets: Vec<Vec<VarBinding<Str, Term>>> = vec![];
        if let Some(groups) = cx.bindings.get(&s) {
            for group in groups {
                let mut vs: Vec<VarBinding<Str, Term>> = Vec::with_capacity(group.len());
                for &t in group {
                    // the variable first: the definitions of later bindings may refer to it
                    let symbol = arena.fresh_x();
                    let sort = t.get_sort(arena);
                    let id = arena.new_local();
                    out.vars.insert(
                        t,
                        Local {
                            id,
                            symbol: symbol.clone(),
                            sort,
                        },
                    );
                    let def = build(t, cx, out, arena);
                    vs.push(VarBinding(symbol, id, def));
                }
                lets.push(vs);
            }
        }
        // the lets of an annotated body go inside its annotation, so that a `:pattern` stays
        // directly under its quantifier
        let (inner, ans): (&'a Term, Option<&'a Vec<Attribute>>) = match b.repr() {
            ATerm::Annotated(_, ans) => (cx.dag.kids[b][0], Some(ans)),
            _ => (b, None),
        };
        let body = refer(inner, cx, out, arena);
        // the last group's let innermost, around the body
        let t = lets
            .into_iter()
            .rev()
            .fold(body, |t, vs| arena.let_term(vs, t));
        match ans {
            None => t,
            Some(ans) => {
                // the `:pattern`s mention the quantifier's variables, renamed like any other
                let renamed: Vec<Attribute> = ans
                    .iter()
                    .map(|a| map_attribute_terms(a, |p| rename_locals(p, cx.names, arena)))
                    .collect();
                arena.annotated(t, renamed)
            }
        }
    }

    /// How `t` appears where it is used: its variable if it is bound (made by [wrap] for the
    /// binding of `t`), or `t` rebuilt by [build] otherwise
    pub(super) fn refer<'a>(
        t: &'a Term,
        cx: &Builder<'a>,
        out: &mut Built<'a>,
        arena: &mut Arena,
    ) -> Term {
        match out.vars.get(t) {
            Some(v) => arena.local(v.clone()),
            None => build(t, cx, out, arena),
        }
    }

    /// `t` rebuilt, with its variables renamed; for a bound node, its definition. Each node is
    /// built once and remembered in `out`.
    ///
    /// - A local gets its new name.
    /// - A quantifier gets its variables renamed, and its body from [wrap], with the lets of its
    ///   own scope.
    /// - A `match` gets its scrutinee from [refer], its patterns renamed, and each arm's body from
    ///   [wrap], with the lets of that arm's scope.
    /// - An annotation gets its child from [refer], and the terms of its `:pattern`s renamed by
    ///   [rename_locals]: they are not let-introduced.
    /// - Any other node gets each child from [refer].
    pub(super) fn build<'a>(
        t: &'a Term,
        cx: &Builder<'a>,
        out: &mut Built<'a>,
        arena: &mut Arena,
    ) -> Term {
        if let Some(r) = out.out.get(t) {
            return r.clone();
        }
        let cs: &Vec<&'a Term> = &cx.dag.kids[t];
        let r = match t.repr() {
            ATerm::Local(l) => arena.local(Local {
                symbol: cx.name(l.id, &l.symbol),
                ..l.clone()
            }),
            ATerm::Exists(vs, _) | ATerm::Forall(vs, _) => {
                let vs2: Vec<VarBinding<Str, Sort>> = vs
                    .iter()
                    .map(|v| VarBinding(cx.name(v.1, &v.0), v.1, v.2.clone()))
                    .collect();
                let body = wrap(Some(Binder { node: t, arm: 0 }), cs[0], cx, out, arena);
                if matches!(t.repr(), ATerm::Exists(..)) {
                    arena.exists(vs2, body)
                } else {
                    arena.forall(vs2, body)
                }
            }
            ATerm::Matching(_, cases) => {
                let patterns: Vec<Pattern> = cases
                    .iter()
                    .map(|a| rename_pattern(&a.pattern, &|id, old| cx.name(id, old)))
                    .collect();
                let scrutinee = refer(cs[0], cx, out, arena);
                let mut arms: Vec<PatternArm> = Vec::with_capacity(patterns.len());
                let mut i = 0usize;
                for pattern in patterns {
                    let body = wrap(Some(Binder { node: t, arm: i }), cs[i + 1], cx, out, arena);
                    arms.push(PatternArm { pattern, body });
                    i += 1;
                }
                arena.matching(scrutinee, arms)
            }
            ATerm::Annotated(_, ans) => {
                // a `:pattern` mentions the quantifier's variables, renamed like any other
                let ans2: Vec<Attribute> = ans
                    .iter()
                    .map(|a| map_attribute_terms(a, |p| rename_locals(p, cx.names, arena)))
                    .collect();
                let inner = refer(cs[0], cx, out, arena);
                arena.annotated(inner, ans2)
            }
            _ => {
                let mut kids: Vec<Term> = Vec::with_capacity(cs.len());
                for &c in cs {
                    let k = refer(c, cx, out, arena);
                    kids.push(k);
                }
                rebuild(t, kids, arena)
            }
        };
        out.out.insert(t, r.clone());
        r
    }
}

// ── Rebuilding a node, and renaming the variables in it ──────────────────────────────────────────

/// `t` with its sub-terms replaced by `kids`, in the order of [children]. Binders keep their
/// variables, and annotations their attributes.
fn rebuild(t: &Term, mut kids: Vec<Term>, arena: &mut Arena) -> Term {
    match t.repr() {
        ATerm::Constant(_, _) | ATerm::Global(_, _) | ATerm::Local(_) => t.clone(),
        ATerm::App(id, _, s) => arena.app(id.clone(), kids, s.clone()),
        ATerm::Distinct(_) => arena.distinct(kids),
        ATerm::And(_) => arena.and(kids),
        ATerm::Or(_) => arena.or(kids),
        ATerm::Xor(_) => arena.xor(kids),
        ATerm::Let(vs, _) => {
            let b = kids.pop().unwrap();
            let vs = vs
                .iter()
                .zip(kids)
                .map(|(v, k)| VarBinding(v.0.clone(), v.1, k))
                .collect();
            arena.let_term(vs, b)
        }
        ATerm::Exists(vs, _) => arena.exists(vs.clone(), kids.pop().unwrap()),
        ATerm::Forall(vs, _) => arena.forall(vs.clone(), kids.pop().unwrap()),
        ATerm::Not(_) => arena.not(kids.pop().unwrap()),
        ATerm::Annotated(_, ans) => arena.annotated(kids.pop().unwrap(), ans.clone()),
        ATerm::Eq(_, _) => {
            let b = kids.pop().unwrap();
            let a = kids.pop().unwrap();
            arena.eq(a, b)
        }
        ATerm::Implies(_, _) => {
            let b = kids.pop().unwrap();
            arena.implies(kids, b)
        }
        ATerm::Ite(_, _, _) => {
            let e = kids.pop().unwrap();
            let t = kids.pop().unwrap();
            let b = kids.pop().unwrap();
            arena.ite(b, t, e)
        }
        ATerm::Matching(_, arms) => {
            let mut kids = kids.into_iter();
            let s = kids.next().unwrap();
            let arms = arms
                .iter()
                .zip(kids)
                .map(|(a, body)| PatternArm {
                    pattern: a.pattern.clone(),
                    body,
                })
                .collect();
            arena.matching(s, arms)
        }
    }
}

/// `p` with each variable named by `name`
fn rename_pattern(p: &Pattern, name: &impl Fn(LocalId, &Str) -> Str) -> Pattern {
    let var = |v: &(Str, LocalId)| (name(v.1, &v.0), v.1);
    match p {
        Pattern::Wildcard(v) => Pattern::Wildcard(v.as_ref().map(var)),
        Pattern::Ctor(c) => Pattern::Ctor(c.clone()),
        Pattern::Applied { ctor, arguments } => Pattern::Applied {
            ctor: ctor.clone(),
            arguments: arguments.iter().map(|v| v.as_ref().map(var)).collect(),
        },
    }
}

/// `a` with `f` applied to each of its terms
fn map_attribute_terms(a: &Attribute, mut f: impl FnMut(&Term) -> Term) -> Attribute {
    match a {
        Attribute::Pattern(ts) => Attribute::Pattern(ts.iter().map(&mut f).collect()),
        #[cfg(feature = "no-pattern")]
        Attribute::NoPattern(t) => Attribute::NoPattern(f(t)),
        a => a.clone(),
    }
}

/// `t` with each local renamed by `names`, for the terms of an annotation, which are printed as
/// they are rather than let-introduced
#[stack_safe]
fn rename_locals(t: &Term, names: &HashMap<LocalId, Str>, arena: &mut Arena) -> Term {
    if let ATerm::Local(l) = t.repr() {
        return match names.get(&l.id) {
            Some(n) => arena.local(Local {
                symbol: n.clone(),
                ..l.clone()
            }),
            None => t.clone(),
        };
    }
    let cs: Vec<&Term> = children(t);
    let mut kids: Vec<Term> = Vec::with_capacity(cs.len());
    for c in cs {
        let k = rename_locals(c, names, arena);
        kids.push(k);
    }
    rebuild(t, kids, arena)
}

#[cfg(test)]
mod tests {
    use crate::allocator::TermAllocator;
    use crate::ast::letintro::TopoLetIntro;
    use crate::ast::{ATerm, AlphaEquiv, Context, LetElim, Term, Typecheck};
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
            "(let ((x-1 (or true false))) (and (forall ((x-0 Int) (y-0 Int)) (let ((x-2 (+ x-0 y-0))) (= (* x-2 x-2) 10))) x-1 x-1))"
        );
    }

    #[test]
    fn test_printing_binder2() {
        let s = topo_print(
            "(and (forall ((x Int) (y Int)) (= (* (+ 1 2) (+ x y) (+ x y)) 10)) (= (+ 1 2) 10))",
        );
        assert_eq!(
            s,
            "(let ((x-1 (+ 1 2))) (and (forall ((x-0 Int) (y-0 Int)) (let ((x-2 (+ x-0 y-0))) (= (* x-1 x-2 x-2) 10))) (= x-1 10)))"
        );
    }

    #[test]
    fn test_printing_binder3() {
        let s = topo_print(
            "(and (forall ((x Int) (y Int)) (= (+ (* (+ 1 2) (+ x y)) (* (+ 1 2) (+ x y))) 10) ) (= (+ 1 2) 10))",
        );
        assert_eq!(
            s,
            "(let ((x-1 (+ 1 2))) (and (forall ((x-0 Int) (y-0 Int)) (let ((x-2 (* x-1 (+ x-0 y-0)))) (= (+ x-2 x-2) 10))) (= x-1 10)))"
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
        printed_round_trip(&mut context, &term)
    }

    /// Print `term` with lets, and check that the printed text, parsed back and with its lets
    /// eliminated, is alpha equivalent to `term` with its lets eliminated. Parsing resolves the
    /// variables by name, so this also catches a variable captured by a binder of the same name.
    fn printed_round_trip(context: &mut Context, term: &Term) -> String {
        let printed = term.topo_print(context);
        let reparsed = UntypedAst
            .parse_term_str(&printed)
            .unwrap()
            .type_check(context)
            .unwrap();
        let expected = term.let_elim(context);
        assert!(
            reparsed.let_elim(context).aeq(&expected),
            "{printed} does not mean {term}"
        );
        printed
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
            "(forall ((x-0 Int)) (! (let ((x-1 (g (f x-0) 1))) (and (> x-1 0) (< x-1 5))) :pattern ((f x-0))))"
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
            "(match l ((nil 0) ((cons h-0 t-0) (let ((x-0 (* h-0 h-0))) (+ x-0 x-0)))))"
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
            "(let ((x-1 (p (f a)))) (and (forall ((x-0 Int)) x-1) x-1 x-1))"
        );
        let s = topo_print_with(
            decls,
            "(and (forall ((x Int)) (! (p (f a)) :pattern ((f x)))) (p (f a)) (p (f a)))",
        );
        assert_eq!(
            s,
            "(let ((x-1 (p (f a)))) (and (forall ((x-0 Int)) (! x-1 :pattern ((f x-0)))) x-1 x-1))"
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
                "(exists ((x-0 Int)) (let ((x-1 (p (f x-0)))) (and x-1 x-1)))",
            ),
            (
                "(and (distinct (f a) b) (distinct (f a) b) (xor (p (f a)) (p b)) (xor (p (f a)) (p b)))",
                "(let ((x-0 (f a))) (let ((x-1 (distinct x-0 b)) (x-2 (xor (p x-0) (p b)))) (and x-1 x-1 x-2 x-2)))",
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
                "(let ((x-1 (f a))) (and (forall ((x-0 Int)) (p (g x-1 x-0))) (forall ((y-0 Int)) (p (g x-1 y-0))) (p x-1)))",
            ),
            // an outer variable used under inner quantifiers
            (
                "(forall ((x Int)) (and (forall ((y Int)) (= (g (f x) y) (g (f x) y))) (forall ((y Int)) (p (g (f x) y))) (p (f x))))",
                "(forall ((x-1 Int)) (let ((x-2 (f x-1))) (and (forall ((y-0 Int)) (let ((x-3 (g x-2 y-0))) (= x-3 x-3))) (forall ((y-1 Int)) (p (g x-2 y-1))) (p x-2))))",
            ),
            // the two `(p (f x))` are of different variables
            (
                "(forall ((x Int)) (and (p (f x)) (forall ((x Int)) (and (p (f x)) (p (f x))))))",
                "(forall ((x-1 Int)) (and (p (f x-1)) (forall ((x-0 Int)) (let ((x-2 (p (f x-0)))) (and x-2 x-2)))))",
            ),
            // quantifiers parsed apart bind different variables, so they are not shared
            (
                "(and (forall ((x Int)) (p (f x))) (forall ((x Int)) (p (f x))))",
                "(and (forall ((x-0 Int)) (p (f x-0))) (forall ((x-1 Int)) (p (f x-1))))",
            ),
            (
                "(and (exists ((y Int)) (and (p y) (forall ((x Int)) (p (g (f a) x))))) (exists ((z Int)) (and (p z) (forall ((x Int)) (p (g (f a) x))))))",
                "(let ((x-2 (f a))) (and (exists ((y-0 Int)) (and (p y-0) (forall ((x-0 Int)) (p (g x-2 x-0))))) (exists ((z-1 Int)) (and (p z-1) (forall ((x-1 Int)) (p (g x-2 x-1)))))))",
            ),
        ]);
    }

    #[test]
    fn test_printing_match_sharing() {
        check_all(&[
            // shared between the arms and outside the match
            (
                "(+ (match l ((nil (f a)) ((cons h t) (+ (f a) (g h (f a)) (g h (f a)))))) (f a))",
                "(let ((x-0 (f a))) (+ (match l ((nil x-0) ((cons h-0 t-0) (let ((x-1 (g h-0 x-0))) (+ x-0 x-1 x-1))))) x-0))",
            ),
            // a quantified variable used in the arms
            (
                "(forall ((x Int)) (= 0 (match l ((nil (f x)) ((cons h t) (+ (f x) (g h h) (g h h)))))))",
                "(forall ((x-0 Int)) (let ((x-1 (f x-0))) (= 0 (match l ((nil x-1) ((cons h-0 t-0) (let ((x-2 (g h-0 h-0))) (+ x-1 x-2 x-2))))))))",
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
        assert!(out.let_elim(&mut context).aeq(&t));
        assert_eq!(
            out.to_string(),
            "(let ((x-1 (forall ((x-0 Int)) (let ((x-2 (p (f x-0)))) (and x-2 x-2))))) (and (exists ((y-0 Int)) (and (p y-0) x-1)) x-1))"
        );
        let t = context.and(vec![q.clone(), q]);
        let out = t.topo_let_intro(&mut context);
        assert!(out.let_elim(&mut context).aeq(&t));
        assert_eq!(
            out.to_string(),
            "(let ((x-4 (forall ((x-3 Int)) (let ((x-5 (p (f x-3)))) (and x-5 x-5))))) (and x-4 x-4))"
        );
    }

    /// A variable used many times is not bound to itself.
    #[test]
    fn test_printing_repeated_variable() {
        let decls = "(declare-fun p (Int) Bool)";
        let s = topo_print_with(decls, "(forall ((x Int)) (and (p x) (> x 0) (< x 5)))");
        assert_eq!(s, "(forall ((x-0 Int)) (and (p x-0) (> x-0 0) (< x-0 5)))");
    }

    /// Eliminating the input's lets puts `x` under a binder named `x`, so the binders are renamed.
    #[test]
    fn test_printing_let_input_capture() {
        let s = topo_print_with(
            "",
            "(forall ((x Int)) (let ((y x)) (forall ((x Int)) (> y x))))",
        );
        assert_eq!(s, "(forall ((x-1 Int)) (forall ((x-0 Int)) (> x-1 x-0)))");
    }
}

#[cfg(test)]
mod stack_safety {
    use super::*;
    use crate::allocator::ObjectAllocatorExt;
    use crate::ast::letintro::TopoLetIntro;
    use crate::ast::{Arena, Context, FlatConnectivesExt};

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

    /// `topo_let_intro` on a term nested 20 000 deep, on a 256 KiB stack.
    #[test]
    fn topo_let_intro_is_flat() {
        let ok = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut context = Context::default();
                let t = deep_alternating(context.arena(), 20_000);
                let out = t.topo_let_intro(&mut context);
                std::mem::forget((t, out));
                true
            })
            .expect("spawn")
            .join();
        assert_eq!(ok.ok(), Some(true));
    }
}
