// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#![cfg(all(feature = "cvc5", feature = "finite-set"))]

use cvc5::{Kind, Solver, TermManager};
use yaspar_ir::ast::{Context, Typecheck};
use yaspar_ir::cvc5::{CTerm, ConvertFromCvc5, ConvertToCvc5, Cvc5Env, Cvc5EnvSolver};
use yaspar_ir::untyped::UntypedAst;

// ── Round-trip helpers ───────────────────────────────────────

fn run_script(script: &str) {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(script)
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    // `set.complement` and `set.universe` are extended set operators in cvc5
    // and require `sets-exp` to be enabled.
    solver.set_option("sets-exp", "true");
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
    for cmd in &cmds {
        cmd.to_cvc5(&mut es).unwrap();
    }
}

fn sort_round_trip(script: &str, sort_str: &str) {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(script)
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let sort = UntypedAst
        .parse_sort_str(sort_str)
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
    for cmd in &cmds {
        cmd.to_cvc5(&mut es).unwrap();
    }
    let csort = sort.to_cvc5(&mut *es.env).unwrap();
    let back = csort.conv_from_cvc5(&mut *es.env).unwrap();
    assert_eq!(sort.to_string(), back.to_string());
}

fn term_round_trip(script: &str, term_str: &str) {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(script)
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let term = UntypedAst
        .parse_term_str(term_str)
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
    for cmd in &cmds {
        cmd.to_cvc5(&mut es).unwrap();
    }
    let cterm = term.to_cvc5(&mut *es.env).unwrap();
    let back = cterm.conv_from_cvc5(&mut *es.env).unwrap();
    assert_eq!(term.to_string(), back.to_string());
}

// ── Forward: Set sort translates without error ───────────────

#[test]
fn fset_sort_int() {
    run_script("(set-logic QF_LIAFS) (declare-const a (Set Int))");
}

#[test]
fn fset_sort_bool() {
    run_script("(set-logic QF_UFFS) (declare-const a (Set Bool))");
}

#[test]
fn fset_sort_nested() {
    run_script("(set-logic QF_LIAFS) (declare-const a (Set (Set Int)))");
}

// ── Forward: set commands run end-to-end ────────────────────

#[test]
fn fset_union_check_sat() {
    run_script(
        "(set-logic QF_LIAFS)
         (declare-const a (Set Int))
         (declare-const b (Set Int))
         (assert (= (set.union a b) a))
         (check-sat)",
    );
}

#[test]
fn fset_inter_check_sat() {
    run_script(
        "(set-logic QF_LIAFS)
         (declare-const a (Set Int))
         (declare-const b (Set Int))
         (assert (= (set.inter a b) b))
         (check-sat)",
    );
}

#[test]
fn fset_minus_check_sat() {
    run_script(
        "(set-logic QF_LIAFS)
         (declare-const a (Set Int))
         (declare-const b (Set Int))
         (assert (= (set.minus a b) a))
         (check-sat)",
    );
}

#[test]
fn fset_member_check_sat() {
    run_script(
        "(set-logic QF_LIAFS)
         (declare-const x Int)
         (declare-const a (Set Int))
         (assert (set.member x a))
         (check-sat)",
    );
}

#[test]
fn fset_subset_check_sat() {
    run_script(
        "(set-logic QF_LIAFS)
         (declare-const a (Set Int))
         (declare-const b (Set Int))
         (assert (set.subset a b))
         (check-sat)",
    );
}

#[test]
fn fset_singleton_check_sat() {
    run_script(
        "(set-logic QF_LIAFS)
         (declare-const a (Set Int))
         (assert (= a (set.singleton 1)))
         (check-sat)",
    );
}

#[test]
fn fset_card_check_sat() {
    run_script(
        "(set-logic QF_LIAFS)
         (declare-const a (Set Int))
         (assert (= (set.card a) 3))
         (check-sat)",
    );
}

#[test]
fn fset_complement_check_sat() {
    run_script(
        "(set-logic QF_LIAFS)
         (declare-const a (Set Int))
         (assert (= (set.complement a) a))
         (check-sat)",
    );
}

#[test]
fn fset_empty_check_sat() {
    run_script(
        "(set-logic QF_LIAFS)
         (declare-const a (Set Int))
         (assert (= a (as set.empty (Set Int))))
         (check-sat)",
    );
}

#[test]
fn fset_universe_check_sat() {
    run_script(
        "(set-logic QF_LIAFS)
         (declare-const a (Set Int))
         (assert (= a (as set.universe (Set Int))))
         (check-sat)",
    );
}

#[test]
fn fset_combined_check_sat() {
    run_script(
        "(set-logic QF_LIAFS)
         (declare-const a (Set Int))
         (declare-const b (Set Int))
         (declare-const x Int)
         (assert (set.member x (set.union a b)))
         (assert (set.subset (set.inter a b) a))
         (assert (= (set.card (set.minus a b)) 2))
         (assert (= (set.complement (as set.empty (Set Int))) (as set.universe (Set Int))))
         (check-sat)",
    );
}

// ── Round-trip: Set sorts ────────────────────────────────────

#[test]
fn from_cvc5_fset_sort_int() {
    sort_round_trip("(set-logic QF_LIAFS)", "(Set Int)");
}

#[test]
fn from_cvc5_fset_sort_bool() {
    sort_round_trip("(set-logic QF_UFFS)", "(Set Bool)");
}

#[test]
fn from_cvc5_fset_sort_nested() {
    sort_round_trip("(set-logic QF_LIAFS)", "(Set (Set Int))");
}

// ── Round-trip: set terms ────────────────────────────────────

#[test]
fn from_cvc5_fset_term_union() {
    term_round_trip(
        "(set-logic QF_LIAFS) (declare-const a (Set Int)) (declare-const b (Set Int))",
        "(set.union a b)",
    );
}

#[test]
fn from_cvc5_fset_term_inter() {
    term_round_trip(
        "(set-logic QF_LIAFS) (declare-const a (Set Int)) (declare-const b (Set Int))",
        "(set.inter a b)",
    );
}

#[test]
fn from_cvc5_fset_term_minus() {
    term_round_trip(
        "(set-logic QF_LIAFS) (declare-const a (Set Int)) (declare-const b (Set Int))",
        "(set.minus a b)",
    );
}

#[test]
fn from_cvc5_fset_term_member() {
    term_round_trip(
        "(set-logic QF_LIAFS) (declare-const a (Set Int)) (declare-const x Int)",
        "(set.member x a)",
    );
}

#[test]
fn from_cvc5_fset_term_subset() {
    term_round_trip(
        "(set-logic QF_LIAFS) (declare-const a (Set Int)) (declare-const b (Set Int))",
        "(set.subset a b)",
    );
}

#[test]
fn from_cvc5_fset_term_singleton() {
    term_round_trip(
        "(set-logic QF_LIAFS) (declare-const a (Set Int))",
        "(set.singleton 1)",
    );
}

#[test]
fn from_cvc5_fset_term_card() {
    term_round_trip(
        "(set-logic QF_LIAFS) (declare-const a (Set Int))",
        "(set.card a)",
    );
}

#[test]
fn from_cvc5_fset_term_complement() {
    term_round_trip(
        "(set-logic QF_LIAFS) (declare-const a (Set Int))",
        "(set.complement a)",
    );
}

#[test]
fn from_cvc5_fset_term_empty() {
    term_round_trip(
        "(set-logic QF_LIAFS) (declare-const a (Set Int))",
        "(as set.empty (Set Int))",
    );
}

#[test]
fn from_cvc5_fset_term_universe() {
    term_round_trip(
        "(set-logic QF_LIAFS) (declare-const a (Set Int))",
        "(as set.universe (Set Int))",
    );
}

#[test]
fn from_cvc5_fset_term_nested_union_inter() {
    term_round_trip(
        "(set-logic QF_LIAFS)
         (declare-const a (Set Int))
         (declare-const b (Set Int))
         (declare-const c (Set Int))",
        "(set.union (set.inter a b) c)",
    );
}

// ── Backward translation built directly from cvc5 APIs ───────
//
// These tests construct cvc5 terms and sorts using only cvc5's own builders
// (no yaspar-ir parsing) and assert that the back-translated yaspar-ir term's
// SMT-LIB-formatted `to_string()` matches an expected literal.

fn assert_back_eq<F>(expected: &str, build: F)
where
    F: for<'tm> FnOnce(&'tm TermManager) -> CTerm<'tm>,
{
    let tm = TermManager::new();
    let mut ctx = Context::new();
    ctx.set_ctx_logic("QF_LIAFS").unwrap();
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let cterm = build(&tm);
    let back = cterm.conv_from_cvc5(&mut env).unwrap();
    assert_eq!(back.to_string(), expected);
}

#[test]
fn back_from_cvc5_api_fset_sort_int() {
    let tm = TermManager::new();
    let mut ctx = Context::new();
    ctx.set_ctx_logic("QF_LIAFS").unwrap();
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let cs = tm.mk_set_sort(tm.integer_sort());
    let back = cs.conv_from_cvc5(&mut env).unwrap();
    assert_eq!(back.to_string(), "(Set Int)");
}

#[test]
fn back_from_cvc5_api_fset_sort_bool() {
    let tm = TermManager::new();
    let mut ctx = Context::new();
    ctx.set_ctx_logic("QF_UFFS").unwrap();
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let cs = tm.mk_set_sort(tm.boolean_sort());
    let back = cs.conv_from_cvc5(&mut env).unwrap();
    assert_eq!(back.to_string(), "(Set Bool)");
}

#[test]
fn back_from_cvc5_api_fset_sort_nested() {
    let tm = TermManager::new();
    let mut ctx = Context::new();
    ctx.set_ctx_logic("QF_LIAFS").unwrap();
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let inner = tm.mk_set_sort(tm.integer_sort());
    let outer = tm.mk_set_sort(inner);
    let back = outer.conv_from_cvc5(&mut env).unwrap();
    assert_eq!(back.to_string(), "(Set (Set Int))");
}

#[test]
fn back_from_cvc5_api_fset_empty() {
    assert_back_eq("(as set.empty (Set Int))", |tm| {
        let s = tm.mk_set_sort(tm.integer_sort());
        tm.mk_empty_set(s)
    });
}

#[test]
fn back_from_cvc5_api_fset_universe() {
    assert_back_eq("(as set.universe (Set Int))", |tm| {
        let s = tm.mk_set_sort(tm.integer_sort());
        tm.mk_universe_set(s)
    });
}

#[test]
fn back_from_cvc5_api_fset_singleton() {
    assert_back_eq("(set.singleton 1)", |tm| {
        let one = tm.mk_integer(1);
        tm.mk_term(Kind::SetSingleton, &[one])
    });
}

#[test]
fn back_from_cvc5_api_fset_union() {
    assert_back_eq("(set.union a b)", |tm| {
        let s = tm.mk_set_sort(tm.integer_sort());
        let a = tm.mk_const(s.clone(), "a");
        let b = tm.mk_const(s, "b");
        tm.mk_term(Kind::SetUnion, &[a, b])
    });
}

#[test]
fn back_from_cvc5_api_fset_inter() {
    assert_back_eq("(set.inter a b)", |tm| {
        let s = tm.mk_set_sort(tm.integer_sort());
        let a = tm.mk_const(s.clone(), "a");
        let b = tm.mk_const(s, "b");
        tm.mk_term(Kind::SetInter, &[a, b])
    });
}

#[test]
fn back_from_cvc5_api_fset_minus() {
    assert_back_eq("(set.minus a b)", |tm| {
        let s = tm.mk_set_sort(tm.integer_sort());
        let a = tm.mk_const(s.clone(), "a");
        let b = tm.mk_const(s, "b");
        tm.mk_term(Kind::SetMinus, &[a, b])
    });
}

#[test]
fn back_from_cvc5_api_fset_member() {
    assert_back_eq("(set.member x a)", |tm| {
        let int = tm.integer_sort();
        let s = tm.mk_set_sort(int.clone());
        let x = tm.mk_const(int, "x");
        let a = tm.mk_const(s, "a");
        tm.mk_term(Kind::SetMember, &[x, a])
    });
}

#[test]
fn back_from_cvc5_api_fset_subset() {
    assert_back_eq("(set.subset a b)", |tm| {
        let s = tm.mk_set_sort(tm.integer_sort());
        let a = tm.mk_const(s.clone(), "a");
        let b = tm.mk_const(s, "b");
        tm.mk_term(Kind::SetSubset, &[a, b])
    });
}

#[test]
fn back_from_cvc5_api_fset_card() {
    assert_back_eq("(set.card a)", |tm| {
        let s = tm.mk_set_sort(tm.integer_sort());
        let a = tm.mk_const(s, "a");
        tm.mk_term(Kind::SetCard, &[a])
    });
}

#[test]
fn back_from_cvc5_api_fset_complement() {
    assert_back_eq("(set.complement a)", |tm| {
        let s = tm.mk_set_sort(tm.integer_sort());
        let a = tm.mk_const(s, "a");
        tm.mk_term(Kind::SetComplement, &[a])
    });
}

#[test]
fn back_from_cvc5_api_fset_nested() {
    assert_back_eq("(set.union (set.inter a b) c)", |tm| {
        let s = tm.mk_set_sort(tm.integer_sort());
        let a = tm.mk_const(s.clone(), "a");
        let b = tm.mk_const(s.clone(), "b");
        let c = tm.mk_const(s, "c");
        let inter = tm.mk_term(Kind::SetInter, &[a, b]);
        tm.mk_term(Kind::SetUnion, &[inter, c])
    });
}
