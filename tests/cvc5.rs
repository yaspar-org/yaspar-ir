// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#![cfg(feature = "cvc5")]

use cvc5_rs::{Solver, TermManager};
use yaspar_ir::ast::{Context, ObjectAllocatorExt, Typecheck};
use yaspar_ir::cvc5::{ConvertToCvc5, Cvc5Env, Cvc5EnvSolver};
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
    let mut env = Cvc5Env::new(&tm);
    let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
    for cmd in &cmds {
        cmd.to_cvc5(&mut es).unwrap();
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
    let mut env = Cvc5Env::new(&tm);
    let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
    for cmd in &cmds {
        cmd.to_cvc5(&mut es).unwrap();
    }
    es.solver.check_sat().is_sat()
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
    let mut env = Cvc5Env::new(&tm);
    let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
    for cmd in &cmds {
        cmd.to_cvc5(&mut es).unwrap();
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
    let mut env = Cvc5Env::new(&tm);
    assert!(x.to_cvc5(&mut env).is_err());
}

#[test]
fn error_unsupported_sort() {
    let mut ctx = Context::new();
    ctx.ensure_logic();
    // A custom sort that cvc5 doesn't know about
    let custom = ctx.simple_sort("MyCustomSort");
    let tm = TermManager::new();
    let mut env = Cvc5Env::new(&tm);
    assert!(custom.to_cvc5(&mut env).is_err());
}

// ── Locals cleanup tests ─────────────────────────────────────

/// After a failed translation inside a quantifier body, the env should not
/// retain stale local bindings — subsequent translations must still work.
#[test]
fn locals_cleaned_up_after_quantifier_error() {
    use yaspar_ir::ast::{CheckedApi, Sig};

    let mut ctx = Context::new();
    ctx.ensure_logic();
    let int = ctx.int_sort();

    // Declare y in the yaspar context so type-checking succeeds
    ctx.add_symbol("y", Sig::sort(int.clone())).unwrap();
    let mut q = ctx
        .build_quantifier_with_domain([("x", int.clone())])
        .unwrap();
    let x = q.typed_symbol("x").unwrap();
    let y = q.typed_symbol("y").unwrap();
    let body = q.typed_eq(x, y).unwrap();
    let forall = q.typed_forall(body).unwrap();

    let tm = TermManager::new();
    let mut env = Cvc5Env::new(&tm);
    // y is not registered in cvc5 — translation should fail
    assert!(forall.to_cvc5(&mut env).is_err());

    // Register y in cvc5 and retry — should succeed if locals were cleaned up
    let cs = tm.mk_const(tm.integer_sort(), "y");
    env.register_global("y", cs);
    assert!(forall.to_cvc5(&mut env).is_ok());
}

/// After a failed translation inside a let body, the env should recover.
#[test]
fn locals_cleaned_up_after_let_error() {
    use yaspar_ir::ast::{CheckedApi, Sig};

    let mut ctx = Context::new();
    ctx.ensure_logic();
    let int = ctx.int_sort();

    // Declare x in yaspar context but not in cvc5
    ctx.add_symbol("x", Sig::sort(int.clone())).unwrap();
    let x = ctx.typed_symbol("x").unwrap();
    let one = ctx.numeral(1u8.into()).unwrap();
    let mut l = ctx.build_let([("a", one)]).unwrap();
    let a = l.typed_symbol("a").unwrap();
    let body = l.typed_simp_app("+", [a, x]).unwrap();
    let let_term = l.typed_let(body);

    let tm = TermManager::new();
    let mut env = Cvc5Env::new(&tm);
    assert!(let_term.to_cvc5(&mut env).is_err());

    // Register x and retry — should succeed if locals were cleaned up
    let cx = tm.mk_const(tm.integer_sort(), "x");
    env.register_global("x", cx);
    assert!(let_term.to_cvc5(&mut env).is_ok());
}

/// After a failed define-fun translation, the env should recover.
#[test]
fn locals_cleaned_up_after_define_fun_error() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            "(set-logic QF_LIA)
             (declare-const y Int)
             (define-fun f ((x Int)) Int (+ x y))",
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    let mut env = Cvc5Env::new(&tm);
    let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
    cmds[0].to_cvc5(&mut es).unwrap();
    // Skip declare-const y

    // define-fun should fail because y is not registered
    assert!(cmds[2].to_cvc5(&mut es).is_err());

    // Register y and retry
    cmds[1].to_cvc5(&mut es).unwrap();
    assert!(cmds[2].to_cvc5(&mut es).is_ok());
}

/// :named annotations in assert should register the term as a global,
/// making it available for later reference (e.g. in get-value).
#[test]
fn named_annotation_registers_global() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (! (> x 0) :named pos))
             (assert (=> pos (> x 1)))",
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    let mut env = Cvc5Env::new(&tm);
    let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
    // All commands should succeed — "pos" from :named must be usable in the second assert
    for cmd in &cmds {
        cmd.to_cvc5(&mut es).unwrap();
    }
}
