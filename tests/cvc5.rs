// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#![cfg(feature = "cvc5")]

use cvc5_rs::{Solver, TermManager};
use yaspar_ir::ast::{Context, ObjectAllocatorExt, Typecheck};
use yaspar_ir::cvc5::{ConvertToCvc5, Cvc5Env};
use yaspar_ir::untyped::UntypedAst;

/// Helper: parse + type-check a script, then translate all commands to cvc5.
fn run_script(script: &str) {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(script)
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    for cmd in &cmds {
        env.translate_command(&mut solver, cmd).unwrap();
    }
}

/// Helper: parse + type-check, translate, and return the cvc5 check-sat result.
fn check_sat(script: &str) -> bool {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(script)
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    solver.set_option("produce-models", "true");
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    for cmd in &cmds {
        env.translate_command(&mut solver, cmd).unwrap();
    }
    solver.check_sat().is_sat()
}

// ── Sort translation tests ───────────────────────────────────

#[test]
fn sort_bool() {
    run_script("(set-logic QF_UF) (declare-const p Bool)");
}

#[test]
fn sort_int() {
    run_script("(set-logic QF_LIA) (declare-const x Int)");
}

#[test]
fn sort_real() {
    run_script("(set-logic QF_LRA) (declare-const x Real)");
}

#[test]
fn sort_bv() {
    run_script("(set-logic QF_BV) (declare-const x (_ BitVec 32))");
}

#[test]
fn sort_array() {
    run_script("(set-logic QF_AUFLIA) (declare-const a (Array Int Int))");
}

// ── Satisfiability tests ─────────────────────────────────────

#[test]
fn sat_lia_simple() {
    assert!(check_sat(
        "(set-logic QF_LIA) (declare-const x Int) (assert (> x 0)) (check-sat)"
    ));
}

#[test]
fn unsat_lia_contradiction() {
    assert!(!check_sat(
        "(set-logic QF_LIA) (declare-const x Int) (assert (> x 0)) (assert (< x 0)) (check-sat)"
    ));
}

#[test]
fn sat_bool_connectives() {
    assert!(check_sat(
        "(set-logic QF_UF)
         (declare-const p Bool) (declare-const q Bool)
         (assert (and p (or q (not p))))
         (check-sat)"
    ));
}

#[test]
fn unsat_bool_contradiction() {
    assert!(!check_sat(
        "(set-logic QF_UF)
         (declare-const p Bool)
         (assert (and p (not p)))
         (check-sat)"
    ));
}

#[test]
fn sat_ite() {
    assert!(check_sat(
        "(set-logic QF_LIA)
         (declare-const x Int) (declare-const y Int)
         (assert (= y (ite (> x 0) 1 (- 1))))
         (assert (> y 0))
         (check-sat)"
    ));
}

#[test]
fn sat_eq_distinct() {
    assert!(!check_sat(
        "(set-logic QF_LIA)
         (declare-const x Int) (declare-const y Int)
         (assert (= x y))
         (assert (distinct x y))
         (check-sat)"
    ));
}

// ── Arithmetic tests ─────────────────────────────────────────

#[test]
fn sat_arithmetic() {
    assert!(check_sat(
        "(set-logic QF_LIA)
         (declare-const x Int) (declare-const y Int)
         (assert (= (+ x y) 10))
         (assert (= (- x y) 2))
         (check-sat)"
    ));
}

#[test]
fn sat_real_division() {
    assert!(check_sat(
        "(set-logic QF_LRA)
         (declare-const x Real)
         (assert (= x (/ 1.0 3.0)))
         (check-sat)"
    ));
}

// ── Bitvector tests ──────────────────────────────────────────

#[test]
fn sat_bv_add() {
    assert!(check_sat(
        "(set-logic QF_BV)
         (declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8))
         (assert (= (bvadd x y) x))
         (check-sat)"
    ));
}

#[test]
fn sat_bv_extract() {
    assert!(check_sat(
        "(set-logic QF_BV)
         (declare-const x (_ BitVec 8))
         (assert (= ((_ extract 3 0) x) #x0))
         (check-sat)"
    ));
}

// ── Uninterpreted function tests ─────────────────────────────

#[test]
fn sat_uf() {
    assert!(check_sat(
        "(set-logic QF_UFLIA)
         (declare-fun f (Int) Int)
         (declare-const a Int)
         (assert (= (f a) 42))
         (check-sat)"
    ));
}

#[test]
fn unsat_uf_congruence() {
    assert!(!check_sat(
        "(set-logic QF_UFLIA)
         (declare-fun f (Int) Int)
         (declare-const a Int) (declare-const b Int)
         (assert (= a b))
         (assert (distinct (f a) (f b)))
         (check-sat)"
    ));
}

// ── Let-binding test ─────────────────────────────────────────

#[test]
fn sat_let_binding() {
    assert!(check_sat(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (assert (let ((y (+ x 1))) (> y 0)))
         (check-sat)"
    ));
}

// ── Quantifier tests ─────────────────────────────────────────

#[test]
fn unsat_forall() {
    assert!(!check_sat(
        "(set-logic LIA)
         (declare-const a Int)
         (assert (forall ((x Int)) (> x a)))
         (check-sat)"
    ));
}

// ── Implies / xor tests ─────────────────────────────────────

#[test]
fn sat_implies() {
    assert!(check_sat(
        "(set-logic QF_UF)
         (declare-const p Bool) (declare-const q Bool)
         (assert (=> p q))
         (assert p)
         (assert q)
         (check-sat)"
    ));
}

#[test]
fn sat_xor() {
    assert!(check_sat(
        "(set-logic QF_UF)
         (declare-const p Bool) (declare-const q Bool)
         (assert (xor p q))
         (check-sat)"
    ));
}

// ── Array tests ──────────────────────────────────────────────

#[test]
fn sat_array_select_store() {
    assert!(check_sat(
        "(set-logic QF_AUFLIA)
         (declare-const a (Array Int Int))
         (assert (= (select (store a 0 42) 0) 42))
         (check-sat)"
    ));
}

// ── translate_term standalone test ───────────────────────────

#[test]
fn translate_term_standalone() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (declare-const y Int)
             (assert (= (+ x y) 10))",
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    for cmd in &cmds {
        env.translate_command(&mut solver, cmd).unwrap();
    }
    // All commands translated without error
}

// ── Error case tests ─────────────────────────────────────────

#[test]
fn error_unknown_global() {
    let mut ctx = Context::new();
    ctx.ensure_logic();
    // Build a global reference to a symbol not registered in cvc5
    let int_sort = ctx.int_sort();
    let x = ctx.simple_sorted_symbol("x", int_sort);
    let tm = TermManager::new();
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    assert!(x.to_cvc5(&mut env).is_err());
}

#[test]
fn error_unsupported_sort() {
    let mut ctx = Context::new();
    ctx.ensure_logic();
    // A custom sort that cvc5 doesn't know about
    let custom = ctx.simple_sort("MyCustomSort");
    let tm = TermManager::new();
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    assert!(custom.to_cvc5(&mut env).is_err());
}
