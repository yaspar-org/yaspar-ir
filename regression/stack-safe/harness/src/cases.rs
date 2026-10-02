// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Every `#[stack_safe]`-covered function of yaspar-ir, outside the cvc5 module (for which see
//! `cvc5_cases.rs`), with the shapes that drive it.
//!
//! Each case has two sides, written once with `pair!`: `side` is `yaspar_ir::__ssbench::stacksafe`
//! (the rewritten functions) in one and `yaspar_ir::__ssbench::native` (their `_orig` copies) in
//! the other. The last
//! argument says when two results are the same: `==` for most, since both sides allocate into one
//! hash-consed context; `same_term` (`==`, else alpha-equivalence) where a result binds variables
//! the call allocated fresh.
//!
//! Which covered functions the cases reach is not declared here but measured: `run.sh coverage`
//! runs the native side of every case under LLVM coverage and requires every `_orig` to have run.

use crate::inputs::*;
use crate::registry::Registry;
use std::collections::HashSet;
use std::time::Instant;
use yaspar_ir::__ssbench as ss;
use yaspar_ir::ast::*;

/// Register a case whose body is written once, with `$side` naming the side it runs.
macro_rules! pair {
    ($r:expr, $target:expr, $shape:expr, $ps:expr, $build:expr,
     |$s:pat_param, $side:ident| $body:expr, $same:expr $(,)?) => {
        $r.pair(
            $target, $shape, $ps, $build,
            |$s| { use yaspar_ir::__ssbench::stacksafe as $side; $body },
            |$s| { use yaspar_ir::__ssbench::native as $side; $body },
            $same,
        )
    };
}

/// The same, for a case that times only part of each call.
macro_rules! pair_timed {
    ($r:expr, $target:expr, $shape:expr, $ps:expr, $build:expr,
     |$s:pat_param, $side:ident| $body:expr, $same:expr $(,)?) => {
        $r.pair_timed(
            $target, $shape, $ps, $build,
            |$s| { use yaspar_ir::__ssbench::stacksafe as $side; $body },
            |$s| { use yaspar_ir::__ssbench::native as $side; $body },
            $same,
        )
    };
}
pub(crate) use {pair, pair_timed};

fn eq<T: PartialEq>(a: &T, b: &T) -> bool {
    a == b
}

/// The same term, or alpha-equivalent to it: for results that bind variables the call allocated
/// fresh (let-introduction, a translated quantifier), whose ids differ from one call to the next.
pub fn same_term(a: &Term, b: &Term) -> bool {
    a == b || a.aeq(b)
}

pub fn register(r: &mut Registry) {
    let (d, h, w, l) = (
        r.depths.clone(),
        r.heights.clone(),
        r.widths.clone(),
        r.levels.clone(),
    );
    cnf(r, &d, &h, &w);
    implicant(r, &d, &h, &w);
    alpha_eq(r, &d, &h, &w);
    datatypes(r, &d, &h, &w);
    named(r, &d);
    letintro(r, &d, &h, &w, &l);
    gsubst(r, &d, &h, &w);
    maybe_sort(r, &d);
    tc_sort(r, &d, &h, &w);
    bv_len(r, &d, &h);
    unification(r, &d, &h, &w);
    display(r, &d, &h, &w);
}

type Tm = (Context, Term);

fn with_ctx(f: impl Fn(&mut Context, usize) -> Term) -> impl Fn(usize) -> Tm {
    move |n| {
        let mut c = ctx();
        let t = f(&mut c, n);
        (c, t)
    }
}

// ── cnf.rs: three single-function recursions, all `data_in_frame` ──────────────

fn cnf(r: &mut Registry, d: &[usize], h: &[usize], w: &[usize]) {
    let shapes: [(&'static str, &[usize], fn(&mut Context, usize) -> Term); 5] = [
        ("alt_chain", d, |c, n| alt_chain(c, n, false)),
        ("not_chain", d, |c, n| {
            let p = bvar(c, "p");
            not_chain(c, n, p)
        }),
        // an `ite` is rewritten to a freshly built `(or (and b t) (and (not b) e))` before the
        // recursion descends into it: the call-site temporary `data_in_frame` exists for
        ("ite_chain", d, |c, n| ite_else_chain(c, n, false)),
        ("balanced", h, balanced_bool),
        ("wide", w, wide_bool),
    ];
    for (shape, ps, f) in shapes {
        pair!(r, "cnf.nnf", shape, ps, with_ctx(f), |(c, t), side| side::nnf(c, t), |a, b| a.0 == b.0);
    }
    // `pg` and `tseitin` take an NNF, i.e. and/or over literals; `not_chain` would be one literal
    for (shape, ps, f) in shapes.into_iter().filter(|s| s.0 != "not_chain") {
        let nnf_input = move |n| {
            let mut c = ctx();
            let t = f(&mut c, n);
            let t = ss::stacksafe::nnf(&mut c, &t).0;
            (c, t)
        };
        // the top variable and the whole emitted formula
        pair!(r, "cnf.pg", shape, ps, nnf_input, |(c, t), side| side::pg(c, t),
            |a, b| a.0 == b.0 && a.1 == b.1);
        pair!(r, "cnf.tseitin", shape, ps, nnf_input, |(c, t), side| side::tseitin(c, t),
            |a, b| a.0 == b.0 && a.1 == b.1);
    }
}

// ── implicant.rs ─────────────────────────────────────────────────────────────

fn implicant(r: &mut Registry, d: &[usize], h: &[usize], w: &[usize]) {
    // the model says every atom is true, so an `or` follows its first child: nesting first
    let shapes: [(&'static str, &[usize], fn(&mut Context, usize) -> Term); 3] = [
        ("alt_chain", d, |c, n| alt_chain(c, n, true)),
        ("balanced", h, balanced_bool),
        ("wide", w, wide_bool),
    ];
    for (shape, ps, f) in shapes {
        pair!(r, "implicant", shape, ps, with_ctx(f), |(c, t), side| side::implicant(c, t), eq);
    }
}

// ── alpha_eq.rs: one group of five ───────────────────────────────────────────

fn alpha_eq(r: &mut Registry, d: &[usize], h: &[usize], w: &[usize]) {
    // Without binders the two sides hash-cons to one term, which `aeq` does not short-cut:
    // it walks both.
    let same_input = |f: fn(&mut Context, usize) -> Term| {
        move |n| {
            let mut c = ctx();
            let t = f(&mut c, n);
            (t.clone(), t)
        }
    };
    let shapes: [(&'static str, &[usize], fn(&mut Context, usize) -> Term); 5] = [
        ("not_chain", d, |c, n| {
            let p = bvar(c, "p");
            not_chain(c, n, p)
        }),
        ("app_chain", d, app_chain),
        ("balanced", h, balanced_bool),
        ("wide", w, wide_bool),
        ("pattern_chain", d, pattern_chain),
    ];
    for (shape, ps, f) in shapes {
        pair!(r, "alpha_eq.aeq", shape, ps, same_input(f), |(a, b), side| side::aeq(a, b, false), eq);
    }

    // With binders, two separate parses give the bound variables different ids, so the
    // comparison really has to thread a renaming through every scope.
    let twice = |decls: &'static str, src: fn(usize) -> String| {
        move |n| {
            let (mut c, _) = script(decls);
            let s = src(n);
            let a = term(&mut c, &s);
            let b = term(&mut c, &s);
            (a, b)
        }
    };
    let forall = twice("(set-logic ALL)", forall_chain_src);
    let lets = twice("(set-logic ALL)(declare-const x Int)", let_chain_src);
    pair!(r, "alpha_eq.aeq", "forall_chain", d, forall, |(a, b), side| side::aeq(a, b, false), eq);
    pair!(r, "alpha_eq.aeq", "let_chain", d, lets, |(a, b), side| side::aeq(a, b, false), eq);
    pair!(r, "alpha_eq.aeq_permissive", "forall_chain", d, forall,
        |(a, b), side| side::aeq(a, b, true), eq);
}

// ── ctx/dt.rs ──────────────────────────────────────────────────────────────────

type Sm = (Context, Sort);

/// The sort shapes shared by `wf_sort`, `tc_sort` and printing, each in a context in which it is
/// well-formed.
fn sort_shapes(d: &[usize], h: &[usize], w: &[usize]) -> Vec<(&'static str, Vec<usize>, fn(usize) -> Sm)> {
    vec![
        ("array_chain", d.to_vec(), |n| {
            let mut c = ctx();
            let int = c.int_sort();
            let s = array_chain(&mut c, n, int);
            (c, s)
        }),
        ("param_chain", d.to_vec(), |n| {
            let (mut c, _) = script("(set-logic ALL)(declare-sort Box 1)");
            let s = param_chain(&mut c, n);
            (c, s)
        }),
        ("balanced", h.to_vec(), |n| {
            let mut c = ctx();
            let int = c.int_sort();
            let s = balanced_sort(&mut c, n, int);
            (c, s)
        }),
        ("wide", w.to_vec(), |n| {
            let (mut c, _) = script(&format!("(set-logic ALL)(declare-sort W {n})"));
            let int = c.int_sort();
            let s = wide_sort(&mut c, n, int);
            (c, s)
        }),
    ]
}

fn datatypes(r: &mut Registry, d: &[usize], h: &[usize], w: &[usize]) {
    for (shape, ps, build) in sort_shapes(d, h, w) {
        pair!(r, "dt.wf_sort", shape, &ps, build, |(c, s), side| side::wf_sort(c, s), eq);
    }
}

// ── ctx/checked.rs: a tail recursion ────────────────────────────────────────────

fn named(r: &mut Registry, d: &[usize]) {
    // whether it succeeded, and every name with the term it names
    pair!(r, "checked.scan_named", "named_chain", d, with_ctx(named_chain),
        |(c, t), side| side::scan_named(c, t), eq);
}

// ── letintro.rs: two groups, three and four members ─────────────────────────────

fn letintro(r: &mut Registry, d: &[usize], h: &[usize], w: &[usize], l: &[usize]) {
    let shapes: [(&'static str, &[usize], fn(usize) -> Tm); 5] = [
        ("alt_chain", d, |n| {
            let mut c = ctx();
            let t = alt_chain(&mut c, n, false);
            (c, t)
        }),
        ("shared_levels", l, |n| {
            let mut c = ctx();
            let t = shared_levels(&mut c, n);
            (c, t)
        }),
        ("forall_chain", d, |n| {
            let (mut c, _) = script("(set-logic ALL)");
            let t = term(&mut c, &forall_chain_src(n));
            (c, t)
        }),
        ("balanced", h, |n| {
            let mut c = ctx();
            let t = balanced_bool(&mut c, n);
            (c, t)
        }),
        ("wide", w, |n| {
            let mut c = ctx();
            let t = wide_bool(&mut c, n);
            (c, t)
        }),
    ];
    for (shape, ps, build) in shapes {
        // every section, sub-term reference count and level it recorded
        pair!(r, "letintro.find_sections", shape, ps, build,
            |(_, t), side| side::find_sections(t), |a, b| a.same(b));
        // `let_intro` consumes what `find_sections` built for the same term, so that is rebuilt,
        // untimed, before every call (by the same side)
        pair_timed!(r, "letintro.let_intro", shape, ps, build,
            |(c, t), side| {
                let mut prep = side::find_sections(t);
                let t0 = Instant::now();
                let out = side::let_intro(c, t, &mut prep);
                let dt = t0.elapsed();
                (dt, out.0)
            },
            same_term);
        // both groups back to back, as `TopoLetIntro::topo_let_intro` runs them
        pair!(r, "letintro.topo_let_intro", shape, ps, build,
            |(c, t), side| side::topo_let_intro(c, t), same_term);
    }
}

// ── gsubst.rs: one group of three ───────────────────────────────────────────────

struct Gs {
    ctx: Context,
    names: HashSet<Str>,
    t: Term,
}

fn gsubst(r: &mut Registry, d: &[usize], h: &[usize], w: &[usize]) {
    // `gsubst_with_names` with every defined name: the same descent as `gsubst_all`, but with a
    // cache of expanded definitions that starts empty on every call (`gsubst_all` keeps it in the
    // context, so every call after the first would expand nothing).
    let names = |c: &mut Context, prefix: &str, n: usize| -> HashSet<Str> {
        (0..n).map(|i| c.allocate_symbol(&format!("{prefix}{i}"))).collect()
    };
    let shapes: [(&'static str, &[usize], Box<dyn Fn(usize) -> Gs>); 5] = [
        ("def_chain", d, Box::new(move |n| {
            let (mut c, _) = script(&def_chain_script(n));
            let t = term(&mut c, &format!("(= f{n} 0)"));
            let ns = names(&mut c, "f", n + 1);
            Gs { ctx: c, names: ns, t }
        })),
        ("not_chain", d, Box::new(move |n| {
            let (mut c, _) = script(&many_defs_script(1));
            let leaf = term(&mut c, "d0");
            let t = not_chain(&mut c, n, leaf);
            let ns = names(&mut c, "d", 1);
            Gs { ctx: c, names: ns, t }
        })),
        ("not_chain_no_defs", d, Box::new(move |n| {
            let mut c = ctx();
            let p = bvar(&mut c, "p");
            let t = not_chain(&mut c, n, p);
            Gs { ctx: c, names: HashSet::new(), t }
        })),
        ("wide", w, Box::new(move |n| {
            let (mut c, _) = script(&many_defs_script(n));
            let args: Vec<String> = (0..n).map(|i| format!("d{i}")).collect();
            let t = term(&mut c, &format!("(and {})", args.join(" ")));
            let ns = names(&mut c, "d", n);
            Gs { ctx: c, names: ns, t }
        })),
        ("balanced", h, Box::new(move |n| {
            let (mut c, _) = script(&many_defs_script(1 << n));
            // the tree of `balanced_bool`, over the defined `d{i}` instead of the declared `p{i}`
            let mut level: Vec<Term> = (0..1usize << n).map(|i| term(&mut c, &format!("d{i}"))).collect();
            let mut k = 0;
            while level.len() > 1 {
                let mut next = Vec::with_capacity(level.len() / 2);
                let mut it = level.into_iter();
                while let (Some(a), Some(b)) = (it.next(), it.next()) {
                    next.push(if k % 2 == 0 { c.or(vec![a, b]) } else { c.and(vec![a, b]) });
                }
                level = next;
                k += 1;
            }
            let t = level.pop().unwrap();
            let ns = names(&mut c, "d", 1 << n);
            Gs { ctx: c, names: ns, t }
        })),
    ];
    for (shape, ps, build) in shapes {
        pair!(r, "gsubst", shape, ps, &build,
            |g, side| side::gsubst(&mut g.ctx, &g.names, &g.t), same_term);
    }
}

// ── instance.rs ──────────────────────────────────────────────────────────────────

fn maybe_sort(r: &mut Registry, d: &[usize]) {
    let shapes: [(&'static str, fn(usize) -> Tm); 3] = [
        ("ite_chain", |n| {
            let mut c = ctx();
            let t = ite_then_chain(&mut c, n);
            (c, t)
        }),
        ("named_chain", |n| {
            let mut c = ctx();
            let t = named_chain(&mut c, n);
            (c, t)
        }),
        ("let_chain", |n| {
            let (mut c, _) = script("(set-logic ALL)(declare-const x Int)");
            let t = term(&mut c, &let_chain_src(n));
            (c, t)
        }),
    ];
    for (shape, build) in shapes {
        pair!(r, "instance.maybe_sort", shape, d, build, |(c, t), side| side::maybe_sort(c, t), eq);
    }
}

// ── tc.rs ──────────────────────────────────────────────────────────────────────────

fn tc_sort(r: &mut Registry, d: &[usize], h: &[usize], w: &[usize]) {
    for (shape, ps, build) in sort_shapes(d, h, w) {
        pair!(r, "tc.tc_sort", shape, &ps, build, |(c, s), side| side::tc_sort(c, s), eq);
    }
}

// ── alg.rs: two recursive calls per node, each behind a `?` ─────────────────────────

fn bv_len(r: &mut Registry, d: &[usize], h: &[usize]) {
    let shapes: [(&'static str, &[usize], fn(usize) -> alg::BvLenExpr); 4] = [
        ("left_chain", d, bv_left_chain),
        ("right_chain", d, bv_right_chain),
        ("mixed_chain", d, bv_mixed_chain),
        ("balanced", h, bv_balanced),
    ];
    for (shape, ps, build) in shapes {
        pair!(r, "alg.eval_bv_len", shape, ps, build, |e, side| side::eval_bv_len(e), eq);
    }
}

// ── tc/unif.rs ─────────────────────────────────────────────────────────────────────

struct Un {
    ctx: Context,
    vars: Vec<Str>,
    expected: Sort,
    ground: Sort,
    solved: SortSubst,
}

fn unification(r: &mut Registry, d: &[usize], h: &[usize], w: &[usize]) {
    // `expected` has the sort variable `X` at its leaves, `ground` has `Int` there.
    fn un(n: usize, decl: Option<String>, shape: fn(&mut Context, usize, Sort) -> Sort) -> Un {
        let mut c = match decl {
            Some(s) => script(&s).0,
            None => ctx(),
        };
        let (x, xs) = sort_var(&mut c);
        let int = c.int_sort();
        let expected = shape(&mut c, n, xs);
        let ground = shape(&mut c, n, int);
        let vars = vec![x];
        let mut solved = ss::empty_subst(&vars);
        assert_eq!(ss::stacksafe::sort_unification(&mut solved, &expected, &ground), Ok(true));
        Un { ctx: c, vars, expected, ground, solved }
    }
    let shapes: [(&'static str, &[usize], fn(usize) -> Un); 3] = [
        ("array_chain", d, |n| un(n, None, array_chain)),
        ("balanced", h, |n| un(n, None, balanced_sort)),
        ("wide", w, |n| un(n, Some(format!("(set-logic ALL)(declare-sort W {n})")), wide_sort)),
    ];
    for (shape, ps, build) in shapes {
        // the answer, and the substitution it built
        pair!(r, "unif.sort_unification", shape, ps, build,
            |u, side| {
                let mut subst = ss::empty_subst(&u.vars);
                let ok = side::sort_unification(&mut subst, &u.expected, &u.ground);
                (ok, subst)
            },
            eq);
        pair!(r, "unif.apply_subst", shape, ps, build,
            |u, side| side::apply_subst(&mut u.ctx, &u.solved, &u.expected), eq);
    }
}

// ── alg/display.rs: printing, i.e. `StructuredPrint` into a document and its rendering ──────

fn display(r: &mut Registry, d: &[usize], h: &[usize], w: &[usize]) {
    let terms: [(&'static str, &[usize], Box<dyn Fn(usize) -> Tm>); 9] = [
        ("not_chain", d, Box::new(with_ctx(|c, n| {
            let p = bvar(c, "p");
            not_chain(c, n, p)
        }))),
        ("app_chain", d, Box::new(with_ctx(app_chain))),
        ("ite_chain", d, Box::new(with_ctx(|c, n| ite_else_chain(c, n, false)))),
        ("balanced", h, Box::new(with_ctx(balanced_bool))),
        ("wide", w, Box::new(with_ctx(wide_bool))),
        ("forall_chain", d, Box::new(|n| {
            let (mut c, _) = script("(set-logic ALL)");
            let t = term(&mut c, &forall_chain_src(n));
            (c, t)
        })),
        ("let_chain", d, Box::new(|n| {
            let (mut c, _) = script("(set-logic ALL)(declare-const x Int)");
            let t = term(&mut c, &let_chain_src(n));
            (c, t)
        })),
        ("pattern_chain", d, Box::new(with_ctx(pattern_chain))),
        ("named_chain", d, Box::new(with_ctx(named_chain))),
    ];
    for (shape, ps, build) in terms {
        pair!(r, "display.term", shape, ps, &build, |(_, t), side| side::show_term(t), eq);
    }
    for (shape, ps, build) in sort_shapes(d, h, w) {
        pair!(r, "display.sort", shape, &ps, build, |(_, s), side| side::show_sort(s), eq);
    }
    let bvs: [(&'static str, &[usize], fn(usize) -> alg::BvLenExpr); 3] = [
        ("left_chain", d, bv_left_chain),
        ("mixed_chain", d, bv_mixed_chain),
        ("balanced", h, bv_balanced),
    ];
    for (shape, ps, build) in bvs {
        pair!(r, "display.bv_len", shape, ps, build, |e, side| side::show_bv_len(e), eq);
    }
}
