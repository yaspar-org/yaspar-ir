// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Input shapes. Each one is a recursion style:
//!
//! * a **chain** nests one node in the next, `depth` deep: one live frame per level, which is
//!   where native recursion pays for its stack and where `#[stack_safe]` is meant to win;
//! * a **balanced** tree of `height` h has 2^h leaves: many calls, never more than h live;
//! * a **wide** node has `width` children: the recursion happens from inside a loop, two deep;
//! * **mutual** shapes alternate between members of a group (a term and its annotation, a term
//!   and a definition, a term and its binder), so each level is a call across functions.
//!
//! Everything is built with the unchecked allocator API or parsed from SMT-LIB text, both of
//! which are the same in every variant. Leaves are distinct wherever hash-consing would
//! otherwise fold a tree into a chain.

use yaspar_ir::ast::alg::{BvLenExpr, QualifiedIdentifier};
use yaspar_ir::ast::*;
use yaspar_ir::untyped::UntypedAst;

/// A context with a logic set, and nothing declared.
pub fn ctx() -> Context {
    let mut c = Context::new();
    c.ensure_logic();
    c
}

/// A context after type-checking `script`, and the commands it produced.
pub fn script(src: &str) -> (Context, Vec<Command>) {
    let mut c = Context::new();
    let cmds = UntypedAst
        .parse_script_str(src)
        .unwrap_or_else(|e| panic!("parse: {e:?}"))
        .type_check(&mut c)
        .unwrap_or_else(|e| panic!("type check: {e}"));
    (c, cmds)
}

/// Parse and type-check a term in `ctx`.
pub fn term(ctx: &mut Context, src: &str) -> Term {
    UntypedAst
        .parse_term_str(src)
        .unwrap_or_else(|e| panic!("parse: {e:?}"))
        .type_check(ctx)
        .unwrap_or_else(|e| panic!("type check: {e}"))
}

pub fn bvar(ctx: &mut Context, name: &str) -> Term {
    let b = ctx.bool_sort();
    ctx.simple_sorted_symbol(name, b)
}

pub fn ivar(ctx: &mut Context, name: &str) -> Term {
    let i = ctx.int_sort();
    ctx.simple_sorted_symbol(name, i)
}

// ── Boolean terms ─────────────────────────────────────────────────────────────

/// `(or p0 (and p1 (or p2 …)))`, `depth` connectives deep. The connectives alternate so that
/// `flat_and`/`flat_or` cannot collapse the nesting. With `nest_first` the nested term is the
/// first child, which is the one an implicant search descends into.
pub fn alt_chain(ctx: &mut Context, depth: usize, nest_first: bool) -> Term {
    let mut t = bvar(ctx, "q");
    for i in 0..depth {
        let p = bvar(ctx, &format!("p{i}"));
        let kids = if nest_first { vec![t, p] } else { vec![p, t] };
        t = if i % 2 == 0 {
            ctx.flat_or(kids)
        } else {
            ctx.flat_and(kids)
        };
    }
    t
}

/// The same with one leaf `p` throughout, for consumers that need every leaf declared (cvc5).
pub fn alt_chain_one_leaf(ctx: &mut Context, depth: usize) -> Term {
    let p = bvar(ctx, "p");
    let mut t = p.clone();
    for i in 0..depth {
        let kids = vec![p.clone(), t];
        t = if i % 2 == 0 {
            ctx.flat_or(kids)
        } else {
            ctx.flat_and(kids)
        };
    }
    t
}

/// `(not (not (… p)))`.
pub fn not_chain(ctx: &mut Context, depth: usize, leaf: Term) -> Term {
    let mut t = leaf;
    for _ in 0..depth {
        t = ctx.not(t);
    }
    t
}

/// `(ite c0 p0 (ite c1 p1 …))`: nested in the else branch. With `one_leaf` every condition and
/// branch is `p`.
pub fn ite_else_chain(ctx: &mut Context, depth: usize, one_leaf: bool) -> Term {
    let mut t = bvar(ctx, "q");
    for i in 0..depth {
        let (c, p) = if one_leaf {
            (bvar(ctx, "p"), bvar(ctx, "q"))
        } else {
            (bvar(ctx, &format!("c{i}")), bvar(ctx, &format!("p{i}")))
        };
        t = ctx.ite(c, p, t);
    }
    t
}

/// `(ite c (ite c (… x) y) y)`: nested in the then branch, which is the branch
/// `FetchSort::maybe_sort` follows.
pub fn ite_then_chain(ctx: &mut Context, depth: usize) -> Term {
    let c = bvar(ctx, "c");
    let x = ivar(ctx, "x");
    let y = ivar(ctx, "y");
    let mut t = x;
    for _ in 0..depth {
        t = ctx.ite(c.clone(), t, y.clone());
    }
    t
}

/// A complete binary tree of `height` with alternating `and`/`or` and 2^height distinct leaves.
pub fn balanced_bool(ctx: &mut Context, height: usize) -> Term {
    let mut level: Vec<Term> = (0..1usize << height)
        .map(|i| bvar(ctx, &format!("p{i}")))
        .collect();
    let mut h = 0;
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len() / 2);
        let mut it = level.into_iter();
        while let (Some(a), Some(b)) = (it.next(), it.next()) {
            next.push(if h % 2 == 0 {
                ctx.or(vec![a, b])
            } else {
                ctx.and(vec![a, b])
            });
        }
        level = next;
        h += 1;
    }
    level.pop().unwrap()
}

/// `(and (or p0 q0) (or p1 q1) … )` with `width` children.
pub fn wide_bool(ctx: &mut Context, width: usize) -> Term {
    let kids = (0..width)
        .map(|i| {
            let p = bvar(ctx, &format!("p{i}"));
            let q = bvar(ctx, &format!("q{i}"));
            ctx.or(vec![p, q])
        })
        .collect();
    ctx.and(kids)
}

/// `(f (f (… x)))` over an uninterpreted `f : Int -> Int`: nesting through an argument list.
pub fn app_chain(ctx: &mut Context, depth: usize) -> Term {
    let int = ctx.int_sort();
    let f = ctx.allocate_symbol("f");
    let mut t = ivar(ctx, "x");
    for _ in 0..depth {
        t = ctx.app(QualifiedIdentifier::simple(f.clone()), vec![t], Some(int.clone()));
    }
    t
}

/// `(! x :pattern ((! x :pattern (…))))`: every level is a term inside an attribute, i.e. a call
/// from one member of a term/attribute group into the other.
pub fn pattern_chain(ctx: &mut Context, depth: usize) -> Term {
    let x = bvar(ctx, "x");
    let mut t = x.clone();
    for _ in 0..depth {
        t = ctx.annotated(x.clone(), vec![Attribute::Pattern(vec![t])]);
    }
    t
}

/// `(! (! (… x :named n0) …) :named n{depth-1})`.
pub fn named_chain(ctx: &mut Context, depth: usize) -> Term {
    let mut t = bvar(ctx, "x");
    for i in 0..depth {
        let name = ctx.allocate_symbol(&format!("n{i}"));
        t = ctx.annotated(t, vec![Attribute::Named(name)]);
    }
    t
}

/// `(and (= u1 u1) (= u2 u2) … )` where `u{i} = (h u{i-1})`: every `u{i}` is shared, and each
/// depends on the previous one, so a let-introduction binds `depth` dependency levels, one
/// inside the next. Walking it costs O(depth^2), hence the separate (smaller) parameter list.
pub fn shared_levels(ctx: &mut Context, depth: usize) -> Term {
    let int = ctx.int_sort();
    let h = ctx.allocate_symbol("h");
    let mut u = ivar(ctx, "x");
    let mut eqs = Vec::with_capacity(depth);
    for _ in 0..depth {
        u = ctx.app(QualifiedIdentifier::simple(h.clone()), vec![u], Some(int.clone()));
        eqs.push(ctx.eq(u.clone(), u.clone()));
    }
    ctx.and(eqs)
}

// ── Binders (parsed, so that local variables are real) ──────────────────────────

/// `(forall ((x0 Int)) (forall ((x1 Int)) (… (= x0 x{d-1}))))`.
pub fn forall_chain_src(depth: usize) -> String {
    let d = depth.max(1);
    let mut s = String::with_capacity(d * 24);
    for i in 0..d {
        s.push_str(&format!("(forall ((x{i} Int)) "));
    }
    s.push_str(&format!("(= x0 x{})", d - 1));
    s.push_str(&")".repeat(d));
    s
}

/// `(let ((y0 x)) (let ((y1 (+ y0 1))) (… (> y{d-1} 0))))`, with `x : Int` declared.
pub fn let_chain_src(depth: usize) -> String {
    let d = depth.max(1);
    let mut s = String::with_capacity(d * 28);
    s.push_str("(let ((y0 x)) ");
    for i in 1..d {
        s.push_str(&format!("(let ((y{i} (+ y{} 1))) ", i - 1));
    }
    s.push_str(&format!("(> y{} 0)", d - 1));
    s.push_str(&")".repeat(d));
    s
}

pub const LIST_DT: &str = "(declare-datatype L ((nil) (cons (hd Int) (tl L))))";

/// `(match l ((nil 0) ((cons h0 t0) (match t0 ((nil 1) ((cons h1 t1) (…)))))))`, with `l : L`.
pub fn match_chain_src(depth: usize) -> String {
    let d = depth.max(1);
    let mut s = String::with_capacity(d * 40);
    let mut scrut = "l".to_string();
    for i in 0..d {
        s.push_str(&format!("(match {scrut} ((nil {i}) ((cons h{i} t{i}) "));
        scrut = format!("t{i}");
    }
    s.push_str(&format!("h{}", d - 1));
    s.push_str(&")))".repeat(d));
    s
}

/// `(cons 0 (cons 0 (… nil)))`: a datatype value `depth` constructors deep.
pub fn cons_chain_src(depth: usize) -> String {
    let mut s = "(cons 0 ".repeat(depth);
    s.push_str("nil");
    s.push_str(&")".repeat(depth));
    s
}

// ── Definitions ───────────────────────────────────────────────────────────────

/// `f{i} = (+ f{i-1} 1)`: expanding `f{depth}` expands the whole chain, alternating between the
/// term being expanded and the definition it mentions.
pub fn def_chain_script(depth: usize) -> String {
    let mut s = String::with_capacity(depth * 40 + 100);
    s.push_str("(set-logic ALL)\n(declare-const x Int)\n(define-fun f0 () Int x)\n");
    for i in 1..=depth {
        s.push_str(&format!("(define-fun f{i} () Int (+ f{} 1))\n", i - 1));
    }
    s
}

/// `n` nullary Boolean definitions `d{i} = (not p{i})`, over declared `p{i}`.
pub fn many_defs_script(n: usize) -> String {
    let mut s = String::with_capacity(n * 60 + 50);
    s.push_str("(set-logic ALL)\n");
    for i in 0..n {
        s.push_str(&format!(
            "(declare-const p{i} Bool)\n(define-fun d{i} () Bool (not p{i}))\n"
        ));
    }
    s
}

// ── Sorts ─────────────────────────────────────────────────────────────────────

/// `(Array Int (Array Int (… leaf)))`.
pub fn array_chain(ctx: &mut Context, depth: usize, leaf: Sort) -> Sort {
    let mut s = leaf;
    for _ in 0..depth {
        let idx = ctx.int_sort();
        s = ctx.array_sort(idx, s);
    }
    s
}

/// `(Box (Box (… Int)))`; `Box` must be a declared sort of arity 1.
pub fn param_chain(ctx: &mut Context, depth: usize) -> Sort {
    let mut s = ctx.int_sort();
    for _ in 0..depth {
        let name = ctx.allocate_symbol("Box");
        s = ctx.sort_n(name, vec![s]);
    }
    s
}

/// A complete binary tree of `(Array T T)` of `height` over `leaf`. Hash-consing shares the two
/// halves, but none of the walks measured here memoize, so each still visits 2^height leaves.
pub fn balanced_sort(ctx: &mut Context, height: usize, leaf: Sort) -> Sort {
    let mut s = leaf;
    for _ in 0..height {
        s = ctx.array_sort(s.clone(), s);
    }
    s
}

/// `(W Int Int … Int)`, `width` arguments; `W` must be a declared sort of that arity.
pub fn wide_sort(ctx: &mut Context, width: usize, leaf: Sort) -> Sort {
    let name = ctx.allocate_symbol("W");
    ctx.sort_n(name, vec![leaf; width])
}

/// A sort variable `X`, for unification.
pub fn sort_var(ctx: &mut Context) -> (Str, Sort) {
    let x = ctx.allocate_symbol("X");
    let s = ctx.sort_n(x.clone(), vec![]);
    (x, s)
}

// ── Bit-vector length expressions ───────────────────────────────────────────────

/// `((… (1 + 1) + 1) + 1)`: nested in the left operand.
pub fn bv_left_chain(depth: usize) -> BvLenExpr {
    let mut e = BvLenExpr::fixed(1);
    for _ in 0..depth {
        e = e + BvLenExpr::fixed(1);
    }
    e
}

/// `(1 + (1 + (… + 1)))`: nested in the right operand, which is evaluated second.
pub fn bv_right_chain(depth: usize) -> BvLenExpr {
    let mut e = BvLenExpr::fixed(1);
    for _ in 0..depth {
        e = BvLenExpr::fixed(1) + e;
    }
    e
}

/// A left chain cycling through `+ 1`, `* 1`, `- 1` from `depth`, so it never underflows.
pub fn bv_mixed_chain(depth: usize) -> BvLenExpr {
    let mut e = BvLenExpr::fixed(depth + 1);
    for i in 0..depth {
        e = match i % 3 {
            0 => e + BvLenExpr::fixed(1),
            1 => e * BvLenExpr::fixed(1),
            _ => e - BvLenExpr::fixed(1),
        };
    }
    e
}

/// A complete binary tree of `+` of `height`.
pub fn bv_balanced(height: usize) -> BvLenExpr {
    if height == 0 {
        BvLenExpr::fixed(1)
    } else {
        bv_balanced(height - 1) + bv_balanced(height - 1)
    }
}
