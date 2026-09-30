// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! The `#[stack_safe]`-covered functions of `src/cvc5.rs`: the forward sort translation, the
//! backward sort and term translations, and `is_const`.
//!
//! cvc5 inputs are produced the way a user produces them: a yaspar-ir term or sort, translated
//! forward once while the case is built. Each timed call then gets a *fresh* `Cvc5Env`, built
//! untimed, because an environment caches every translation in both directions and a warm one
//! would answer from the cache without recursing at all.
//!
//! A case's `TermManager` is leaked, which gives its terms a `'static` lifetime they can be stored
//! under; it is one per case and parameter.

use crate::cases::{pair, pair_timed, same_term};
use crate::inputs::*;
use crate::registry::Registry;
use cvc5::{Solver, TermManager};
use std::time::Instant;
use yaspar_ir::ast::*;
use yaspar_ir::cvc5::{CSort, CTerm, ConvertToCvc5, Cvc5Env, Cvc5EnvSolver};

type Env<'c> = Cvc5Env<'static, &'c mut Context>;

/// A case's world: the term manager, the context the input lives in, and the declarations a
/// forward translation needs replayed into its environment.
struct World {
    tm: &'static TermManager,
    ctx: Context,
    cmds: Vec<Command>,
}

impl World {
    fn new(script_src: &str) -> World {
        let (ctx, cmds) = script(script_src);
        World { tm: Box::leak(Box::new(TermManager::new())), ctx, cmds }
    }

    /// Run `f` on a fresh environment into which the script's declarations have been replayed.
    fn with_declared<R>(&mut self, f: impl FnOnce(&mut Env<'_>) -> R) -> R {
        let solver = Solver::new(self.tm);
        let mut env = Cvc5Env::new(self.tm, &mut self.ctx);
        {
            let mut es = Cvc5EnvSolver::new(&mut env, &solver);
            for c in &self.cmds {
                c.to_cvc5(&mut es).expect("declaration");
            }
        }
        let r = f(&mut env);
        drop(env);
        drop(solver);
        r
    }

    /// Translate `t` forward, for a case that measures the way back.
    fn forward_term(&mut self, t: &Term) -> CTerm<'static> {
        self.with_declared(|env| t.to_cvc5(env).expect("forward translation"))
    }

    fn forward_sort(&mut self, s: &Sort) -> CSort<'static> {
        self.with_declared(|env| s.to_cvc5(env).expect("forward translation"))
    }
}

struct Fwd {
    w: World,
    sort: Sort,
}

struct BackT {
    w: World,
    ct: CTerm<'static>,
}

struct BackS {
    w: World,
    cs: CSort<'static>,
}

fn decls(prefix: &str, sort: &str, n: usize) -> String {
    (0..n).map(|i| format!("(declare-const {prefix}{i} {sort})")).collect()
}

pub fn register(r: &mut Registry) {
    let (d, h, w) = (r.depths.clone(), r.heights.clone(), r.widths.clone());

    // ── forward: Sort -> CSort (csort_forward group) ──
    let fwd_shapes: [(&'static str, &[usize], fn(usize) -> Fwd); 3] = [
        ("array_chain", &d, |n| {
            let mut w = World::new("(set-logic ALL)");
            let int = w.ctx.int_sort();
            let sort = array_chain(&mut w.ctx, n, int);
            Fwd { w, sort }
        }),
        ("param_chain", &d, |n| {
            let mut w = World::new("(set-logic ALL)(declare-sort Box 1)");
            let sort = param_chain(&mut w.ctx, n);
            Fwd { w, sort }
        }),
        ("balanced", &h, |n| {
            let mut w = World::new("(set-logic ALL)");
            let int = w.ctx.int_sort();
            let sort = balanced_sort(&mut w.ctx, n, int);
            Fwd { w, sort }
        }),
    ];
    for (shape, ps, build) in fwd_shapes {
        // Each side declares the script's sorts into a solver of its own, and cvc5 makes a new
        // sort constructor for every declaration, so the two results are compared in yaspar-ir:
        // each translated back (untimed, through a fresh environment) and then with `==`.
        pair_timed!(r, "cvc5.sort_to_cvc5", shape, ps, build,
            |f, side| {
                let sort = f.sort.clone();
                let tm = f.w.tm;
                let (dt, out) = f.w.with_declared(|env| {
                    let t0 = Instant::now();
                    let out = side::sort_to_cvc5(&sort, env);
                    (t0.elapsed(), out)
                });
                let back = out.and_then(|cs| {
                    let mut fresh = Cvc5Env::new(tm, &mut f.w.ctx);
                    side::conv_csort(&cs, &mut fresh)
                });
                (dt, back)
            },
            |a, b| a == b);
    }

    // ── backward: CSort -> Sort (csort_cycle group) ──
    let back_sort_shapes: [(&'static str, &[usize], fn(usize) -> BackS); 3] = [
        ("array_chain", &d, |n| {
            let mut w = World::new("(set-logic ALL)");
            let int = w.ctx.int_sort();
            let s = array_chain(&mut w.ctx, n, int);
            let cs = w.forward_sort(&s);
            BackS { w, cs }
        }),
        ("param_chain", &d, |n| {
            let mut w = World::new("(set-logic ALL)(declare-sort Box 1)");
            let s = param_chain(&mut w.ctx, n);
            let cs = w.forward_sort(&s);
            BackS { w, cs }
        }),
        ("balanced", &h, |n| {
            let mut w = World::new("(set-logic ALL)");
            let int = w.ctx.int_sort();
            let s = balanced_sort(&mut w.ctx, n, int);
            let cs = w.forward_sort(&s);
            BackS { w, cs }
        }),
    ];
    for (shape, ps, build) in back_sort_shapes {
        pair_timed!(r, "cvc5.conv_csort", shape, ps, build,
            |b, side| {
                let mut env = Cvc5Env::new(b.w.tm, &mut b.w.ctx);
                let t0 = Instant::now();
                let out = side::conv_csort(&b.cs, &mut env);
                (t0.elapsed(), out)
            },
            |a, b| a == b);
    }

    // ── backward: CTerm -> Term (cterm_cycle group) ──
    fn back(script_src: String, mk: impl FnOnce(&mut Context) -> Term) -> BackT {
        let mut w = World::new(&script_src);
        let t = mk(&mut w.ctx);
        let ct = w.forward_term(&t);
        BackT { w, ct }
    }
    let back_term_shapes: [(&'static str, &[usize], fn(usize) -> BackT); 9] = [
        ("not_chain", &d, |n| {
            back("(set-logic ALL)(declare-const p Bool)".into(), |c| {
                let p = term(c, "p");
                not_chain(c, n, p)
            })
        }),
        ("alt_chain", &d, |n| {
            back("(set-logic ALL)(declare-const p Bool)".into(), |c| alt_chain_one_leaf(c, n))
        }),
        ("ite_chain", &d, |n| {
            back("(set-logic ALL)(declare-const p Bool)(declare-const q Bool)".into(), |c| {
                ite_else_chain(c, n, true)
            })
        }),
        // an uninterpreted application, whose arguments are walked by `translate_term` itself
        ("app_chain", &d, |n| {
            back(
                "(set-logic ALL)(declare-fun f (Int) Int)(declare-const x Int)".into(),
                |c| {
                    let src = format!("{}x{}", "(f ".repeat(n), ")".repeat(n));
                    let t = term(c, &src);
                    term_eq_zero(c, t)
                },
            )
        }),
        ("forall_chain", &d, |n| {
            back("(set-logic ALL)".into(), |c| term(c, &forall_chain_src(n)))
        }),
        ("match_chain", &d, |n| {
            back(format!("(set-logic ALL){LIST_DT}(declare-const l L)"), |c| {
                let t = term(c, &match_chain_src(n));
                term_eq_zero(c, t)
            })
        }),
        ("indexed_chain", &d, |n| {
            back("(set-logic ALL)(declare-const b (_ BitVec 8))".into(), |c| {
                let src = format!("{}b{}", "((_ rotate_left 1) ".repeat(n), ")".repeat(n));
                let t = term(c, &src);
                let b = term(c, "b");
                c.eq(t, b)
            })
        }),
        ("balanced", &h, |n| {
            back(format!("(set-logic ALL){}", decls("p", "Bool", 1 << n)), |c| balanced_bool(c, n))
        }),
        ("wide", &w, |n| {
            back(format!("(set-logic ALL){}{}", decls("p", "Bool", n), decls("q", "Bool", n)), |c| {
                wide_bool(c, n)
            })
        }),
    ];
    for (shape, ps, build) in back_term_shapes {
        // a translated quantifier binds fresh variables, hence alpha-equivalence
        pair_timed!(r, "cvc5.conv_cterm", shape, ps, build,
            |b, side| {
                let mut env = Cvc5Env::new(b.w.tm, &mut b.w.ctx);
                let t0 = Instant::now();
                let out = side::conv_cterm(&b.ct, &mut env);
                (t0.elapsed(), out)
            },
            |a, b| match (a, b) {
                (Ok(x), Ok(y)) => same_term(x, y),
                (x, y) => x == y,
            });
    }

    // ── is_const: a datatype value, constructor inside constructor ──
    pair!(r, "cvc5.is_const", "cons_chain", &d,
        |n| {
            let mut w = World::new(&format!("(set-logic ALL){LIST_DT}"));
            let t = term(&mut w.ctx, &cons_chain_src(n));
            let ct = w.forward_term(&t);
            BackT { w, ct }
        },
        |b, side| side::is_const(&b.ct),
        |a, b| a == b);
}

/// `(= t 0)`, to make an `Int` term an assertion-shaped `Bool` one.
fn term_eq_zero(c: &mut Context, t: Term) -> Term {
    let zero = term(c, "0");
    c.eq(t, zero)
}
