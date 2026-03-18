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
        cmd.to_cvc5(&mut es, &mut ctx).unwrap();
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
        cmd.to_cvc5(&mut es, &mut ctx).unwrap();
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
        cmd.to_cvc5(&mut es, &mut ctx).unwrap();
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
    assert!(x.to_cvc5(&mut env, &mut ctx).is_err());
}

#[test]
fn error_unsupported_sort() {
    let mut ctx = Context::new();
    ctx.ensure_logic();
    // A custom sort that cvc5 doesn't know about
    let custom = ctx.simple_sort("MyCustomSort");
    let tm = TermManager::new();
    let mut env = Cvc5Env::new(&tm);
    assert!(custom.to_cvc5(&mut env, &mut ctx).is_err());
}

// ── Locals cleanup tests ─────────────────────────────────────

/// After a failed translation inside a quantifier body, the env should not
/// retain stale local bindings — subsequent translations must still work.
#[test]
fn locals_cleaned_up_after_quantifier_error() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            "(set-logic LIA)
             (declare-const y Int)
             (assert (forall ((x Int)) (= x y)))",
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    let mut env = Cvc5Env::new(&tm);

    // Translate set-logic only — skip declare-const y
    cmds[0]
        .to_cvc5(&mut Cvc5EnvSolver::new(&mut env, &mut solver), &mut ctx)
        .unwrap();

    // Extract the forall term from the assert command and translate it directly
    use yaspar_ir::traits::Repr;
    let forall = match cmds[2].repr() {
        yaspar_ir::ast::ACommand::Assert(t) => t.clone(),
        _ => unreachable!(),
    };

    // Should fail because y is not registered
    assert!(forall.to_cvc5(&mut env, &mut ctx).is_err());

    // Now register y and retry — env should be clean (no stale locals from x)
    cmds[1]
        .to_cvc5(&mut Cvc5EnvSolver::new(&mut env, &mut solver), &mut ctx)
        .unwrap();
    assert!(forall.to_cvc5(&mut env, &mut ctx).is_ok());
}

/// After a failed translation inside a let body, the env should recover.
#[test]
fn locals_cleaned_up_after_let_error() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            "(set-logic QF_LIA)
             (declare-const y Int)
             (assert (let ((a 1)) (> (+ a y) 0)))",
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    let mut env = Cvc5Env::new(&tm);
    let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
    cmds[0].to_cvc5(&mut es, &mut ctx).unwrap();
    // Skip declare-const y

    // assert with let should fail because y is not registered
    assert!(cmds[2].to_cvc5(&mut es, &mut ctx).is_err());

    // Register y and retry
    cmds[1].to_cvc5(&mut es, &mut ctx).unwrap();
    assert!(cmds[2].to_cvc5(&mut es, &mut ctx).is_ok());
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
    cmds[0].to_cvc5(&mut es, &mut ctx).unwrap();
    // Skip declare-const y

    // define-fun should fail because y is not registered
    assert!(cmds[2].to_cvc5(&mut es, &mut ctx).is_err());

    // Register y and retry
    cmds[1].to_cvc5(&mut es, &mut ctx).unwrap();
    assert!(cmds[2].to_cvc5(&mut es, &mut ctx).is_ok());
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
        cmd.to_cvc5(&mut es, &mut ctx).unwrap();
    }
}

/// Parametric datatypes should translate correctly via mk_param_sort.
#[test]
fn parametric_datatype() {
    run_script(
        "(set-logic ALL)
         (declare-datatypes ((List 1))
           ((par (X) ((nil) (cons (car X) (cdr (List X)))))))
         (declare-const l1 (List Int))
         (declare-const l2 (List Bool))
         (check-sat)",
    );
}

/// Parametric datatype with multiple sort parameters.
#[test]
fn parametric_datatype_multi_param() {
    run_script(
        "(set-logic ALL)
         (declare-datatypes ((Pair 2))
           ((par (A B) ((mk-pair (fst A) (snd B))))))
         (declare-const p (Pair Int Bool))
         (assert (= (fst p) 42))
         (assert (snd p))
         (check-sat)",
    );
}

/// Nested parametric instantiation: List of Pairs.
#[test]
fn parametric_datatype_nested() {
    run_script(
        "(set-logic ALL)
         (declare-datatypes ((Pair 2) (List 1))
           ((par (A B) ((mk-pair (fst A) (snd B))))
            (par (X) ((nil) (cons (car X) (cdr (List X)))))))
         (declare-const ps (List (Pair Int Bool)))
         (declare-const nested (Pair (List Int) Bool))
         (check-sat)",
    );
}

/// Monomorphic and parametric datatypes declared together.
#[test]
fn parametric_datatype_mixed() {
    run_script(
        "(set-logic ALL)
         (declare-datatypes ((Color 0) (Option 1))
           (((red) (green) (blue))
            (par (X) ((none) (some (val X))))))
         (declare-const c Color)
         (declare-const o1 (Option Int))
         (declare-const o2 (Option Color))
         (assert (= c red))
         (check-sat)",
    );
}

/// Parametric datatype: constructors, selectors, and (_ is X) tester.
#[test]
fn parametric_datatype_constructor_selector_tester() {
    assert!(check_sat(
        "(set-logic ALL)
         (declare-datatypes ((Option 1))
           ((par (X) ((none) (some (val X))))))
         (declare-const o (Option Int))
         (assert (= o (some 42)))
         (assert ((_ is some) o))
         (assert (= (val o) 42))"
    ));
}

/// Parametric datatype: is-X style tester.
#[test]
fn parametric_datatype_is_dash_tester() {
    assert!(check_sat(
        "(set-logic ALL)
         (declare-datatypes ((Option 1))
           ((par (X) ((none) (some (val X))))))
         (declare-const o (Option Int))
         (assert (= o (as none (Option Int))))
         (assert (is-none o))"
    ));
}

/// Parametric List: cons constructor, car/cdr selectors, nil tester.
#[test]
fn parametric_list_constructors_selectors() {
    assert!(check_sat(
        "(set-logic ALL)
         (declare-datatypes ((List 1))
           ((par (X) ((nil) (cons (car X) (cdr (List X)))))))
         (declare-const l (List Int))
         (assert (= l (cons 1 (cons 2 (as nil (List Int))))))
         (assert (= (car l) 1))
         (assert (= (car (cdr l)) 2))
         (assert ((_ is nil) (cdr (cdr l))))"
    ));
}

// ── Match expression tests ───────────────────────────────────

/// Simple match on a monomorphic enum datatype.
#[test]
fn match_mono_enum() {
    assert!(check_sat(
        "(set-logic ALL)
         (declare-datatypes ((Color 0)) (((red) (green) (blue))))
         (declare-const c Color)
         (assert (= c green))
         (assert (= 2 (match c ((red 1) (green 2) (blue 3)))))"
    ));
}

/// Match on a datatype with constructors that have selectors.
#[test]
fn match_mono_applied() {
    assert!(check_sat(
        "(set-logic ALL)
         (declare-datatypes ((Option 1))
           ((par (X) ((none) (some (val X))))))
         (declare-const o (Option Int))
         (assert (= o (some 42)))
         (assert (= 42 (match o (((some v) v) (none 0)))))"
    ));
}

/// Match on a parametric datatype (List Int).
#[test]
fn match_parametric() {
    assert!(check_sat(
        "(set-logic ALL)
         (declare-datatypes ((List 1))
           ((par (X) ((nil) (cons (car X) (cdr (List X)))))))
         (declare-const l (List Int))
         (assert (= l (cons 5 (as nil (List Int)))))
         (assert (= 5 (match l (((cons h t) h) (nil 0)))))"
    ));
}

/// Match with a wildcard arm.
#[test]
fn match_wildcard() {
    assert!(check_sat(
        "(set-logic ALL)
         (declare-datatypes ((Color 0)) (((red) (green) (blue))))
         (declare-const c Color)
         (assert (= c blue))
         (assert (= 99 (match c ((red 1) (x 99)))))"
    ));
}

/// Match used inside a define-fun with a non-recursive body.
#[test]
fn match_in_define_fun_rec() {
    assert!(check_sat(
        "(set-logic ALL)
         (declare-datatypes ((Option 1))
           ((par (X) ((none) (some (val X))))))
         (define-fun unwrap-or ((o (Option Int)) (d Int)) Int
           (match o (((some v) v) (none d))))
         (declare-const o (Option Int))
         (assert (= o (some 42)))
         (assert (= (unwrap-or o 0) 42))"
    ));
}
