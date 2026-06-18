// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#![cfg(feature = "cvc5-dep")]

use cvc5::{Kind, Solver, TermManager};
use yaspar_ir::ast::{Context, ObjectAllocatorExt, Typecheck};
use yaspar_ir::cvc5::{CTerm, ConvertFromCvc5, ConvertToCvc5, Cvc5Env, Cvc5EnvSolver};
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
    let mut env = Cvc5Env::new(&tm, &mut ctx);
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
    let mut env = Cvc5Env::new(&tm, &mut ctx);
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
    let mut env = Cvc5Env::new(&tm, &mut ctx);

    // Translate set-logic only — skip declare-const y
    cmds[0]
        .to_cvc5(&mut Cvc5EnvSolver::new(&mut env, &mut solver))
        .unwrap();

    // Extract the forall term from the assert command and translate it directly
    use yaspar_ir::traits::Repr;
    let forall = match cmds[2].repr() {
        yaspar_ir::ast::ACommand::Assert(t) => t.clone(),
        _ => unreachable!(),
    };

    // Should fail because y is not registered
    assert!(forall.to_cvc5(&mut env).is_err());

    // Now register y and retry — env should be clean (no stale locals from x)
    cmds[1]
        .to_cvc5(&mut Cvc5EnvSolver::new(&mut env, &mut solver))
        .unwrap();
    assert!(forall.to_cvc5(&mut env).is_ok());
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
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
    cmds[0].to_cvc5(&mut es).unwrap();
    // Skip declare-const y

    // assert with let should fail because y is not registered
    assert!(cmds[2].to_cvc5(&mut es).is_err());

    // Register y and retry
    cmds[1].to_cvc5(&mut es).unwrap();
    assert!(cmds[2].to_cvc5(&mut es).is_ok());
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
    let mut env = Cvc5Env::new(&tm, &mut ctx);
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
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
    // All commands should succeed — "pos" from :named must be usable in the second assert
    for cmd in &cmds {
        cmd.to_cvc5(&mut es).unwrap();
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

/// Match with anonymous variables `_` in a constructor pattern.
#[test]
fn match_anonymous_vars() {
    assert!(check_sat(
        "(set-logic ALL)
         (declare-datatypes ((List 1))
           ((par (X) ((nil) (cons (car X) (cdr (List X)))))))
         (declare-const l (List Int))
         (assert (= l (cons 5 (as nil (List Int)))))
         (assert (= 1 (match l (((cons _ _) 1) (nil 0)))))"
    ));
}

// ── CommandResult tests ──────────────────────────────────────

use yaspar_ir::cvc5::CommandResult;

/// Helper: run a script and pass each CommandResult to a callback.
/// Results are inspected before the solver is dropped, avoiding use-after-free
/// of cvc5 objects that reference solver-internal state.
fn with_script_results(script: &str, options: &[(&str, &str)], f: impl FnOnce(&[CommandResult])) {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(script)
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    for (k, v) in options {
        solver.set_option(k, v);
    }
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
    let results: Vec<_> = cmds
        .iter()
        .map(|cmd| cmd.to_cvc5(&mut es).unwrap())
        .collect();
    f(&results);
}

#[test]
fn command_result_none_for_declarations() {
    with_script_results(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (assert (> x 0))",
        &[],
        |results| assert!(results.iter().all(|r| matches!(r, CommandResult::None))),
    );
}

#[test]
fn command_result_check_sat_sat() {
    with_script_results(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (assert (> x 0))
         (check-sat)",
        &[],
        |results| match results.last().unwrap() {
            CommandResult::CheckSat(r) => assert!(r.is_sat()),
            other => panic!("expected CheckSat, got {other:?}"),
        },
    );
}

#[test]
fn command_result_check_sat_unsat() {
    with_script_results(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (assert (> x 0))
         (assert (< x 0))
         (check-sat)",
        &[],
        |results| match results.last().unwrap() {
            CommandResult::CheckSat(r) => assert!(r.is_unsat()),
            other => panic!("expected CheckSat, got {other:?}"),
        },
    );
}

#[test]
fn command_result_check_sat_assuming() {
    with_script_results(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (assert (> x 0))
         (check-sat-assuming ((< x 0)))",
        &[],
        |results| match results.last().unwrap() {
            CommandResult::CheckSat(r) => assert!(r.is_unsat()),
            other => panic!("expected CheckSat, got {other:?}"),
        },
    );
}

#[test]
fn command_result_get_value() {
    with_script_results(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (assert (= x 42))
         (check-sat)
         (get-value (x))",
        &[("produce-models", "true")],
        |results| match results.last().unwrap() {
            CommandResult::GetValue(vals) => assert_eq!(vals.len(), 1),
            other => panic!("expected GetValue, got {other:?}"),
        },
    );
}

#[test]
fn command_result_get_model() {
    with_script_results(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (assert (= x 42))
         (check-sat)
         (get-model)",
        &[("produce-models", "true")],
        |results| match results.last().unwrap() {
            CommandResult::GetModel(m) => assert_eq!(m, "(\n(define-fun x () Int 42)\n)\n"),
            other => panic!("expected GetModel, got {other:?}"),
        },
    );
}

#[test]
fn command_result_get_assertions() {
    with_script_results(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (assert (> x 0))
         (get-assertions)",
        &[("produce-assertions", "true")],
        |results| match results.last().unwrap() {
            CommandResult::Terms(ts) => assert_eq!(ts.len(), 1),
            other => panic!("expected Terms, got {other:?}"),
        },
    );
}

#[test]
fn command_result_get_unsat_core() {
    with_script_results(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (assert (! (> x 0) :named a1))
         (assert (! (< x 0) :named a2))
         (check-sat)
         (get-unsat-core)",
        &[("produce-unsat-cores", "true")],
        |results| match results.last().unwrap() {
            CommandResult::Terms(ts) => assert_eq!(ts.len(), 2),
            other => panic!("expected Terms, got {other:?}"),
        },
    );
}

#[test]
fn command_result_get_value_returns_term_value() {
    with_script_results(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (assert (= x 42))
         (check-sat)
         (get-value (x))",
        &[("produce-models", "true")],
        |results| match results.last().unwrap() {
            CommandResult::GetValue(vals) => {
                assert_eq!(vals.len(), 1);
                assert_eq!(vals[0].to_string(), "42");
            }
            other => panic!("expected GetValue, got {other:?}"),
        },
    );
}

#[test]
fn command_result_get_value_multiple() {
    with_script_results(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (declare-const y Int)
         (assert (= x 7))
         (assert (= y 13))
         (check-sat)
         (get-value (x y (+ x y)))",
        &[("produce-models", "true")],
        |results| match results.last().unwrap() {
            CommandResult::GetValue(vals) => {
                assert_eq!(vals.len(), 3);
                assert_eq!(vals[0].to_string(), "7");
                assert_eq!(vals[1].to_string(), "13");
                assert_eq!(vals[2].to_string(), "20");
            }
            other => panic!("expected GetValue, got {other:?}"),
        },
    );
}

#[test]
fn command_result_get_value_bool() {
    with_script_results(
        "(set-logic QF_LIA)
         (declare-const p Bool)
         (assert p)
         (check-sat)
         (get-value (p))",
        &[("produce-models", "true")],
        |results| match results.last().unwrap() {
            CommandResult::GetValue(vals) => {
                assert_eq!(vals.len(), 1);
                assert_eq!(vals[0].to_string(), "true");
            }
            other => panic!("expected GetValue, got {other:?}"),
        },
    );
}

#[test]
fn command_result_get_assertions_preserves_terms() {
    with_script_results(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (assert (> x 0))
         (assert (< x 10))
         (get-assertions)",
        &[("produce-assertions", "true")],
        |results| match results.last().unwrap() {
            CommandResult::Terms(ts) => {
                assert_eq!(ts.len(), 2);
                let s: Vec<String> = ts.iter().map(|t| t.to_string()).collect();
                let a = "(> x 0)";
                let b = "(< x 10)";
                assert!(
                    (s[0] == a && s[1] == b) || (s[0] == b && s[1] == a),
                    "expected {{ {a:?}, {b:?} }} in some order, got {s:?}"
                );
            }
            other => panic!("expected Terms, got {other:?}"),
        },
    );
}

#[test]
fn command_result_get_unsat_core_returns_named_labels() {
    with_script_results(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (assert (! (> x 0) :named a1))
         (assert (! (< x 0) :named a2))
         (check-sat)
         (get-unsat-core)",
        &[("produce-unsat-cores", "true")],
        |results| match results.last().unwrap() {
            CommandResult::Terms(ts) => {
                assert_eq!(ts.len(), 2);
                let s: Vec<String> = ts.iter().map(|t| t.to_string()).collect();
                let a = "a1";
                let b = "a2";
                assert!(
                    (s[0] == a && s[1] == b) || (s[0] == b && s[1] == a),
                    "expected {{ {a:?}, {b:?} }} in some order, got {s:?}"
                );
            }
            other => panic!("expected Terms, got {other:?}"),
        },
    );
}

#[test]
fn command_result_get_unsat_core_mixes_named_and_unnamed() {
    with_script_results(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (assert (! (> x 0) :named pos))
         (assert (< x 0))
         (check-sat)
         (get-unsat-core)",
        &[("produce-unsat-cores", "true")],
        |results| match results.last().unwrap() {
            CommandResult::Terms(ts) => {
                assert_eq!(ts.len(), 2);
                let s: Vec<String> = ts.iter().map(|t| t.to_string()).collect();
                let a = "pos";
                let b = "(< x 0)";
                assert!(
                    (s[0] == a && s[1] == b) || (s[0] == b && s[1] == a),
                    "expected {{ {a:?}, {b:?} }} in some order, got {s:?}"
                );
            }
            other => panic!("expected Terms, got {other:?}"),
        },
    );
}

#[test]
fn command_result_get_unsat_assumptions_returns_terms() {
    with_script_results(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (declare-const p Bool)
         (declare-const q Bool)
         (assert (=> p (> x 0)))
         (assert (=> q (< x 0)))
         (check-sat-assuming (p q))
         (get-unsat-assumptions)",
        &[("produce-unsat-assumptions", "true")],
        |results| match results.last().unwrap() {
            CommandResult::Terms(ts) => {
                assert!(!ts.is_empty(), "expected at least one assumption");
                let names: Vec<String> = ts.iter().map(|t| t.to_string()).collect();
                assert!(names.iter().all(|n| n == "p" || n == "q"));
            }
            other => panic!("expected Terms, got {other:?}"),
        },
    );
}

#[test]
fn command_result_get_info() {
    with_script_results(
        "(set-logic QF_LIA)
         (get-info :name)",
        &[],
        |results| match results.last().unwrap() {
            CommandResult::Info(s) => assert!(!s.is_empty()),
            other => panic!("expected Info, got {other:?}"),
        },
    );
}

#[test]
fn command_result_get_option() {
    with_script_results(
        "(set-logic QF_LIA)
         (get-option :produce-models)",
        &[],
        |results| match results.last().unwrap() {
            CommandResult::Info(s) => assert!(!s.is_empty()),
            other => panic!("expected Info, got {other:?}"),
        },
    );
}

/// get-model with multiple arity-0 uninterpreted sorts and a two-argument function.
#[test]
fn command_result_get_model_uninterpreted_sort_multi_arg_fun() {
    with_script_results(
        "(set-logic QF_UF)
         (declare-sort U 0)
         (declare-sort V 0)
         (declare-fun f (U U) V)
         (declare-const a U)
         (declare-const b U)
         (declare-const c V)
         (assert (= (f a b) c))
         (assert (not (= (f b a) c)))
         (check-sat)
         (get-model)",
        &[("produce-models", "true")],
        |results| match results.last().unwrap() {
            CommandResult::GetModel(m) => {
                assert!(
                    m.contains("define-fun"),
                    "model should contain definitions: {m}"
                );
            }
            other => panic!("expected GetModel, got {other:?}"),
        },
    );
}

/// get-model with a three-argument function over uninterpreted sorts.
#[test]
fn command_result_get_model_uninterpreted_sort_three_arg_fun() {
    with_script_results(
        "(set-logic QF_UF)
         (declare-sort S 0)
         (declare-fun g (S S S) S)
         (declare-const a S)
         (declare-const b S)
         (declare-const c S)
         (assert (= (g a b c) a))
         (assert (not (= (g c b a) a)))
         (check-sat)
         (get-model)",
        &[("produce-models", "true")],
        |results| match results.last().unwrap() {
            CommandResult::GetModel(m) => {
                assert!(
                    m.contains("define-fun"),
                    "model should contain definitions: {m}"
                );
            }
            other => panic!("expected GetModel, got {other:?}"),
        },
    );
}

/// get-model with uninterpreted sorts mixed with integers and a multi-argument function.
#[test]
fn command_result_get_model_uninterpreted_sort_mixed_with_ints() {
    with_script_results(
        "(set-logic ALL)
         (declare-sort T 0)
         (declare-fun wrap (Int) T)
         (declare-fun unwrap (T) Int)
         (declare-fun combine (T T Int) T)
         (declare-const a T)
         (declare-const b T)
         (assert (= (unwrap a) 42))
         (assert (= (unwrap b) 7))
         (assert (= (combine a b (+ (unwrap a) (unwrap b))) (wrap 49)))
         (check-sat)
         (get-model)",
        &[("produce-models", "true")],
        |results| match results.last().unwrap() {
            CommandResult::GetModel(m) => {
                assert!(
                    m.contains("define-fun"),
                    "model should contain definitions: {m}"
                );
            }
            other => panic!("expected GetModel, got {other:?}"),
        },
    );
}

/// get-model with arity-1 uninterpreted sort and a two-argument function.
#[test]
fn command_result_get_model_uninterpreted_sort_arity1() {
    with_script_results(
        "(set-logic QF_UF)
         (declare-sort F 1)
         (declare-sort U 0)
         (declare-const a (F U))
         (declare-const b (F U))
         (declare-fun g ((F U) (F U)) Bool)
         (assert (g a b))
         (assert (not (g b a)))
         (check-sat)
         (get-model)",
        &[("produce-models", "true")],
        |results| match results.last().unwrap() {
            CommandResult::GetModel(m) => {
                assert!(
                    m.contains("define-fun"),
                    "model should contain definitions: {m}"
                );
            }
            other => panic!("expected GetModel, got {other:?}"),
        },
    );
}

/// get-model with arity-2 uninterpreted sort and projection functions.
#[test]
fn command_result_get_model_uninterpreted_sort_arity2() {
    with_script_results(
        "(set-logic QF_UF)
         (declare-sort Pair 2)
         (declare-sort A 0)
         (declare-sort B 0)
         (declare-fun mk (A B) (Pair A B))
         (declare-fun fst ((Pair A B)) A)
         (declare-fun snd ((Pair A B)) B)
         (declare-const x A)
         (declare-const y B)
         (assert (= (fst (mk x y)) x))
         (assert (= (snd (mk x y)) y))
         (check-sat)
         (get-model)",
        &[("produce-models", "true")],
        |results| match results.last().unwrap() {
            CommandResult::GetModel(m) => {
                assert!(
                    m.contains("define-fun"),
                    "model should contain definitions: {m}"
                );
            }
            other => panic!("expected GetModel, got {other:?}"),
        },
    );
}

/// get-model with nested parameterized uninterpreted sorts.
#[test]
fn command_result_get_model_uninterpreted_sort_nested() {
    with_script_results(
        "(set-logic QF_UF)
         (declare-sort F 1)
         (declare-sort U 0)
         (declare-const a (F (F U)))
         (declare-const b (F U))
         (declare-fun h ((F (F U)) (F U)) (F U))
         (assert (= (h a b) b))
         (check-sat)
         (get-model)",
        &[("produce-models", "true")],
        |results| match results.last().unwrap() {
            CommandResult::GetModel(m) => {
                assert!(
                    m.contains("define-fun"),
                    "model should contain definitions: {m}"
                );
            }
            other => panic!("expected GetModel, got {other:?}"),
        },
    );
}

// ── ConvertFromCvc5 sort round-trip tests ────────────────────

/// Helper: translate a yaspar-ir Sort to cvc5 and back, asserting the round-trip
/// produces the same string representation.
fn sort_round_trip(script: &str, sort_str: &str) {
    let mut ctx = Context::new();
    let _cmds = UntypedAst
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
    for cmd in &_cmds {
        cmd.to_cvc5(&mut es).unwrap();
    }
    let csort = sort.to_cvc5(&mut *es.env).unwrap();
    let back = csort.conv_from_cvc5(&mut *es.env).unwrap();
    assert_eq!(sort.to_string(), back.to_string());
}

#[test]
fn from_cvc5_sort_bool() {
    sort_round_trip("(set-logic QF_UF)", "Bool");
}

#[test]
fn from_cvc5_sort_int() {
    sort_round_trip("(set-logic QF_LIA)", "Int");
}

#[test]
fn from_cvc5_sort_real() {
    sort_round_trip("(set-logic QF_LRA)", "Real");
}

#[test]
fn from_cvc5_sort_string() {
    sort_round_trip("(set-logic QF_S)", "String");
}

#[test]
fn from_cvc5_sort_bv() {
    sort_round_trip("(set-logic QF_BV)", "(_ BitVec 32)");
}

#[test]
fn from_cvc5_sort_array() {
    sort_round_trip("(set-logic QF_AUFLIA)", "(Array Int Int)");
}

#[test]
fn from_cvc5_sort_uninterpreted() {
    sort_round_trip("(set-logic QF_UF) (declare-sort U 0)", "U");
}

#[test]
fn from_cvc5_sort_datatype() {
    sort_round_trip(
        "(set-logic ALL)
         (declare-datatype Color ((red) (green) (blue)))",
        "Color",
    );
}

#[test]
fn from_cvc5_sort_parametric_datatype() {
    sort_round_trip(
        "(set-logic ALL)
         (declare-datatype List (par (X) ((nil) (cons (car X) (cdr (List X))))))",
        "(List Int)",
    );
}

#[test]
fn from_cvc5_sort_cache_hit() {
    let tm = TermManager::new();
    let csort = tm.integer_sort();
    let mut ctx = Context::new();
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let back1 = csort.conv_from_cvc5(&mut env).unwrap();
    let back2 = csort.conv_from_cvc5(&mut env).unwrap();
    assert_eq!(back1, back2);
}

#[test]
fn const_array_translation() {
    // Verify that ((as const (Array Int Int)) 0) translates to cvc5 successfully
    run_script(
        "(set-logic ALL)
         (set-option :arrays-exp true)
         (declare-const a (Array Int Int))
         (assert (= a ((as const (Array Int Int)) 0)))
         (check-sat)",
    );
}

#[test]
fn const_array_nested() {
    // Verify const array in a select expression
    run_script(
        "(set-logic ALL)
         (set-option :arrays-exp true)
         (declare-const x Int)
         (assert (= x (select ((as const (Array Int Int)) 42) 7)))
         (check-sat)",
    );
}

#[test]
fn const_array_bool() {
    // Verify const array with Bool element sort
    run_script(
        "(set-logic ALL)
         (set-option :arrays-exp true)
         (declare-const a (Array Int Bool))
         (assert (= a ((as const (Array Int Bool)) true)))
         (check-sat)",
    );
}

#[test]
fn const_array_negative() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            "(set-logic ALL)
         (set-option :arrays-exp true)
         (declare-const a (Array Int Bool))
         (declare-const b Bool)
         ",
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let term = UntypedAst
        .parse_term_str("(= a ((as const (Array Int Bool)) b))")
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
    assert!(term.to_cvc5(&mut env).is_err());
}
/// Helper: translate a yaspar-ir Term to cvc5 and back, asserting the round-trip
/// produces the same string representation.
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

#[test]
fn from_cvc5_term_bool_true() {
    term_round_trip("(set-logic QF_UF)", "true");
}

#[test]
fn from_cvc5_term_bool_false() {
    term_round_trip("(set-logic QF_UF)", "false");
}

#[test]
fn from_cvc5_term_integer() {
    term_round_trip("(set-logic QF_LIA) (declare-const x Int)", "x");
}

#[test]
fn from_cvc5_term_and() {
    term_round_trip(
        "(set-logic QF_UF) (declare-const a Bool) (declare-const b Bool)",
        "(and a b)",
    );
}

#[test]
fn from_cvc5_term_or() {
    term_round_trip(
        "(set-logic QF_UF) (declare-const a Bool) (declare-const b Bool)",
        "(or a b)",
    );
}

#[test]
fn from_cvc5_term_not() {
    term_round_trip("(set-logic QF_UF) (declare-const a Bool)", "(not a)");
}

#[test]
fn from_cvc5_term_implies() {
    term_round_trip(
        "(set-logic QF_UF) (declare-const a Bool) (declare-const b Bool)",
        "(=> a b)",
    );
}

#[test]
fn from_cvc5_term_eq() {
    term_round_trip(
        "(set-logic QF_LIA) (declare-const x Int) (declare-const y Int)",
        "(= x y)",
    );
}

#[test]
fn from_cvc5_term_ite() {
    term_round_trip(
        "(set-logic QF_LIA) (declare-const a Bool) (declare-const x Int) (declare-const y Int)",
        "(ite a x y)",
    );
}

#[test]
fn from_cvc5_term_add() {
    term_round_trip(
        "(set-logic QF_LIA) (declare-const x Int) (declare-const y Int)",
        "(+ x y)",
    );
}

#[test]
fn from_cvc5_term_gt() {
    term_round_trip(
        "(set-logic QF_LIA) (declare-const x Int) (declare-const y Int)",
        "(> x y)",
    );
}

#[test]
fn from_cvc5_term_bv_add() {
    term_round_trip(
        "(set-logic QF_BV) (declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8))",
        "(bvadd x y)",
    );
}

#[test]
fn from_cvc5_term_numeral() {
    term_round_trip("(set-logic QF_LIA) (declare-const x Int)", "(+ x 42)");
}

#[test]
fn from_cvc5_term_bv_literal() {
    term_round_trip(
        "(set-logic QF_BV) (declare-const x (_ BitVec 8))",
        "(bvadd x #b00101010)",
    );
}

#[test]
fn from_cvc5_term_forall() {
    term_round_trip(
        "(set-logic LIA) (declare-const y Int)",
        "(forall ((x Int)) (> x y))",
    );
}

#[test]
fn from_cvc5_term_exists() {
    term_round_trip(
        "(set-logic LIA) (declare-const y Int)",
        "(exists ((x Int)) (= x y))",
    );
}

#[test]
fn from_cvc5_term_regexp_none() {
    term_round_trip(
        "(set-logic QF_S) (declare-const s String)",
        "(str.in_re s re.none)",
    );
}

#[test]
fn from_cvc5_term_regexp_all() {
    term_round_trip(
        "(set-logic QF_S) (declare-const s String)",
        "(str.in_re s re.all)",
    );
}

#[test]
fn from_cvc5_term_regexp_allchar() {
    term_round_trip(
        "(set-logic QF_S) (declare-const s String)",
        "(str.in_re s re.allchar)",
    );
}

#[test]
fn from_cvc5_term_bv2nat() {
    // cvc5 normalizes BitvectorToNat to BitvectorUbvToInt internally,
    // so we test the ubv_to_int round-trip which exercises the same path.
    term_round_trip(
        "(set-logic ALL) (declare-const x (_ BitVec 8))",
        "(ubv_to_int x)",
    );
}

#[test]
fn from_cvc5_term_match() {
    term_round_trip(
        "(set-logic ALL) (declare-datatypes ((Color 0)) (((Red) (Green) (Blue)))) (declare-const c Color)",
        "(match c ((Red 1) (Green 2) (Blue 3)))",
    );
}

#[test]
fn from_cvc5_term_match_applied() {
    term_round_trip(
        "(set-logic ALL) (declare-datatypes ((Pair 0)) (((mkpair (fst Int) (snd Int))))) (declare-const p Pair)",
        "(match p (((mkpair x y) (+ x y))))",
    );
}

// ── Comprehensive backward translation tests ─────────────────

#[test]
fn from_cvc5_term_forall_pattern() {
    term_round_trip(
        "(set-logic ALL) (declare-fun f (Int) Int)",
        "(forall ((x Int)) (! (> (f x) 0) :pattern ((f x))))",
    );
}

#[test]
fn from_cvc5_term_forall_multi_pattern() {
    term_round_trip(
        "(set-logic ALL) (declare-fun f (Int) Int) (declare-fun g (Int) Int)",
        "(forall ((x Int)) (! (> (f x) (g x)) :pattern ((f x)) :pattern ((g x))))",
    );
}

#[test]
fn from_cvc5_term_forall_multi_var() {
    term_round_trip(
        "(set-logic ALL) (declare-fun f (Int Int) Int)",
        "(forall ((x Int) (y Int)) (> (f x y) 0))",
    );
}

#[test]
fn from_cvc5_term_nested_quantifier() {
    term_round_trip(
        "(set-logic ALL) (declare-const a Int)",
        "(forall ((x Int)) (exists ((y Int)) (= (+ x y) a)))",
    );
}

#[test]
fn from_cvc5_term_xor() {
    term_round_trip(
        "(set-logic QF_UF) (declare-const a Bool) (declare-const b Bool)",
        "(xor a b)",
    );
}

#[test]
fn from_cvc5_term_distinct() {
    term_round_trip(
        "(set-logic QF_LIA) (declare-const x Int) (declare-const y Int) (declare-const z Int)",
        "(distinct x y z)",
    );
}

#[test]
fn from_cvc5_term_chained_eq() {
    // (= x y z) in cvc5 is n-ary; reverse translates to (and (= x y) (= y z))
    let mut ctx = Context::new();
    let _cmds = UntypedAst
        .parse_script_str(
            "(set-logic QF_LIA) (declare-const x Int) (declare-const y Int) (declare-const z Int)",
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let x = UntypedAst
        .parse_term_str("x")
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let y = UntypedAst
        .parse_term_str("y")
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let z = UntypedAst
        .parse_term_str("z")
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
    for cmd in &_cmds {
        cmd.to_cvc5(&mut es).unwrap();
    }
    let cx = x.to_cvc5(&mut *es.env).unwrap();
    let cy = y.to_cvc5(&mut *es.env).unwrap();
    let cz = z.to_cvc5(&mut *es.env).unwrap();
    let eq_xyz = tm.mk_term(Kind::Equal, &[cx, cy, cz]);
    let back = eq_xyz.conv_from_cvc5(&mut *es.env).unwrap();
    assert_eq!(back.to_string(), "(and (= x y) (= y z))");
}

#[test]
fn from_cvc5_term_unary_minus() {
    term_round_trip("(set-logic QF_LIA) (declare-const x Int)", "(- x)");
}

#[test]
fn from_cvc5_term_sub() {
    term_round_trip(
        "(set-logic QF_LIA) (declare-const x Int) (declare-const y Int)",
        "(- x y)",
    );
}

#[test]
fn from_cvc5_term_mul() {
    term_round_trip(
        "(set-logic QF_LIA) (declare-const x Int) (declare-const y Int)",
        "(* x y)",
    );
}

#[test]
fn from_cvc5_term_div() {
    term_round_trip(
        "(set-logic QF_LRA) (declare-const x Real) (declare-const y Real)",
        "(/ x y)",
    );
}

#[test]
fn from_cvc5_term_idiv() {
    term_round_trip(
        "(set-logic QF_LIA) (declare-const x Int) (declare-const y Int)",
        "(div x y)",
    );
}

#[test]
fn from_cvc5_term_mod() {
    term_round_trip(
        "(set-logic QF_LIA) (declare-const x Int) (declare-const y Int)",
        "(mod x y)",
    );
}

#[test]
fn from_cvc5_term_le() {
    term_round_trip(
        "(set-logic QF_LIA) (declare-const x Int) (declare-const y Int)",
        "(<= x y)",
    );
}

#[test]
fn from_cvc5_term_lt() {
    term_round_trip(
        "(set-logic QF_LIA) (declare-const x Int) (declare-const y Int)",
        "(< x y)",
    );
}

#[test]
fn from_cvc5_term_ge() {
    term_round_trip(
        "(set-logic QF_LIA) (declare-const x Int) (declare-const y Int)",
        "(>= x y)",
    );
}

#[test]
fn from_cvc5_term_select_store() {
    term_round_trip(
        "(set-logic QF_AUFLIA) (declare-const a (Array Int Int)) (declare-const i Int) (declare-const v Int)",
        "(select (store a i v) i)",
    );
}

#[test]
fn from_cvc5_term_bv_extract() {
    term_round_trip(
        "(set-logic QF_BV) (declare-const x (_ BitVec 8))",
        "((_ extract 3 0) x)",
    );
}

#[test]
fn from_cvc5_term_bv_zero_extend() {
    term_round_trip(
        "(set-logic QF_BV) (declare-const x (_ BitVec 8))",
        "((_ zero_extend 8) x)",
    );
}

#[test]
fn from_cvc5_term_bv_sign_extend() {
    term_round_trip(
        "(set-logic QF_BV) (declare-const x (_ BitVec 8))",
        "((_ sign_extend 8) x)",
    );
}

#[test]
fn from_cvc5_term_bv_concat() {
    term_round_trip(
        "(set-logic QF_BV) (declare-const x (_ BitVec 4)) (declare-const y (_ BitVec 4))",
        "(concat x y)",
    );
}

#[test]
fn from_cvc5_term_bv_not() {
    term_round_trip(
        "(set-logic QF_BV) (declare-const x (_ BitVec 8))",
        "(bvnot x)",
    );
}

#[test]
fn from_cvc5_term_bv_neg() {
    term_round_trip(
        "(set-logic QF_BV) (declare-const x (_ BitVec 8))",
        "(bvneg x)",
    );
}

#[test]
fn from_cvc5_term_bv_and() {
    term_round_trip(
        "(set-logic QF_BV) (declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8))",
        "(bvand x y)",
    );
}

#[test]
fn from_cvc5_term_bv_or() {
    term_round_trip(
        "(set-logic QF_BV) (declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8))",
        "(bvor x y)",
    );
}

#[test]
fn from_cvc5_term_bv_ult() {
    term_round_trip(
        "(set-logic QF_BV) (declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8))",
        "(bvult x y)",
    );
}

#[test]
fn from_cvc5_term_string_concat() {
    term_round_trip(
        "(set-logic QF_S) (declare-const s1 String) (declare-const s2 String)",
        "(str.++ s1 s2)",
    );
}

#[test]
fn from_cvc5_term_string_len() {
    term_round_trip("(set-logic QF_S) (declare-const s String)", "(str.len s)");
}

#[test]
fn from_cvc5_term_string_literal() {
    term_round_trip(
        "(set-logic QF_S) (declare-const s String)",
        "(str.++ s \"hello\")",
    );
}

#[test]
fn from_cvc5_term_str_to_re() {
    term_round_trip(
        "(set-logic QF_S) (declare-const s String)",
        "(str.in_re s (str.to_re \"abc\"))",
    );
}

#[test]
fn from_cvc5_term_re_star() {
    term_round_trip(
        "(set-logic QF_S) (declare-const s String)",
        "(str.in_re s (re.* (str.to_re \"a\")))",
    );
}

#[test]
fn from_cvc5_term_uf_application() {
    term_round_trip(
        "(set-logic QF_UFLIA) (declare-fun f (Int Int) Int) (declare-const x Int) (declare-const y Int)",
        "(f x y)",
    );
}

#[test]
fn from_cvc5_term_datatype_constructor_nullary() {
    term_round_trip(
        "(set-logic ALL) (declare-datatypes ((Color 0)) (((Red) (Green) (Blue))))",
        "Red",
    );
}

#[test]
fn from_cvc5_term_datatype_constructor_applied() {
    term_round_trip(
        "(set-logic ALL) (declare-datatypes ((Pair 0)) (((mkpair (fst Int) (snd Int))))) (declare-const x Int)",
        "(mkpair x 42)",
    );
}

#[test]
fn from_cvc5_term_datatype_selector() {
    term_round_trip(
        "(set-logic ALL) (declare-datatypes ((Pair 0)) (((mkpair (fst Int) (snd Int))))) (declare-const p Pair)",
        "(fst p)",
    );
}

#[test]
fn from_cvc5_term_datatype_tester() {
    term_round_trip(
        "(set-logic ALL) (declare-datatypes ((Color 0)) (((Red) (Green) (Blue)))) (declare-const c Color)",
        "((_ is Red) c)",
    );
}

#[test]
fn from_cvc5_term_match_wildcard() {
    term_round_trip(
        "(set-logic ALL) (declare-datatypes ((Color 0)) (((Red) (Green) (Blue)))) (declare-const c Color)",
        "(match c ((Red 1) (x 0)))",
    );
}

#[test]
fn from_cvc5_term_real_literal() {
    // The forward-cached round-trip returns the original Term unchanged.
    let mut ctx = Context::new();
    let _cmds = UntypedAst
        .parse_script_str("(set-logic QF_LRA) (declare-const x Real)")
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let term = UntypedAst
        .parse_term_str("(+ x 1.5)")
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
    for cmd in &_cmds {
        cmd.to_cvc5(&mut es).unwrap();
    }
    let cterm = term.to_cvc5(&mut *es.env).unwrap();
    let back = cterm.conv_from_cvc5(&mut *es.env).unwrap();
    assert_eq!(back.to_string(), "(+ x 1.5)");
}

#[test]
fn from_cvc5_term_let_eliminated() {
    // let bindings are eliminated during forward translation; the reverse should still work
    term_round_trip(
        "(set-logic QF_LIA) (declare-const x Int)",
        "(+ (+ x 1) (+ x 1))",
    );
}

#[test]
fn from_cvc5_term_deeply_nested() {
    term_round_trip(
        "(set-logic QF_LIA) (declare-const x Int)",
        "(+ (+ (+ (+ x 1) 2) 3) 4)",
    );
}

#[test]
fn from_cvc5_term_implies_chain() {
    // cvc5 normalizes (=> a b c) to (=> a (=> b c))
    term_round_trip(
        "(set-logic QF_UF) (declare-const a Bool) (declare-const b Bool) (declare-const c Bool)",
        "(=> a (=> b c))",
    );
}

#[test]
fn from_cvc5_term_real_integer_value() {
    // Real value that is integral (no division) — should produce a decimal
    let mut ctx = Context::new();
    let _cmds = UntypedAst
        .parse_script_str("(set-logic QF_LRA) (declare-const x Real)")
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let term = UntypedAst
        .parse_term_str("(+ x 3.0)")
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
    for cmd in &_cmds {
        cmd.to_cvc5(&mut es).unwrap();
    }
    let cterm = term.to_cvc5(&mut *es.env).unwrap();
    let back = cterm.conv_from_cvc5(&mut *es.env).unwrap();
    // cvc5 returns "3" for the real value 3.0; reverse produces (/ 3 1) or 3.0
    assert!(back.to_string().contains("3"));
}

#[test]
fn from_cvc5_term_real_in_lira() {
    // The forward-cached round-trip returns the original Term unchanged.
    let mut ctx = Context::new();
    let _cmds = UntypedAst
        .parse_script_str("(set-logic AUFLIRA) (declare-const x Real)")
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let term = UntypedAst
        .parse_term_str("(+ x 1.5)")
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
    for cmd in &_cmds {
        cmd.to_cvc5(&mut es).unwrap();
    }
    let cterm = term.to_cvc5(&mut *es.env).unwrap();
    let back = cterm.conv_from_cvc5(&mut *es.env).unwrap();
    assert_eq!(back.to_string(), "(+ x 1.5)");
}

#[test]
fn from_cvc5_term_bv_rotate_left() {
    term_round_trip(
        "(set-logic QF_BV) (declare-const x (_ BitVec 8))",
        "((_ rotate_left 3) x)",
    );
}

#[test]
fn from_cvc5_term_bv_rotate_right() {
    term_round_trip(
        "(set-logic QF_BV) (declare-const x (_ BitVec 8))",
        "((_ rotate_right 3) x)",
    );
}

#[test]
fn from_cvc5_term_bv_repeat() {
    term_round_trip(
        "(set-logic QF_BV) (declare-const x (_ BitVec 4))",
        "((_ repeat 2) x)",
    );
}

#[test]
fn from_cvc5_term_int2bv() {
    term_round_trip("(set-logic ALL) (declare-const x Int)", "((_ int2bv 8) x)");
}

#[test]
fn from_cvc5_term_re_power() {
    term_round_trip(
        "(set-logic QF_S) (declare-const s String)",
        "(str.in_re s ((_ re.^ 3) (str.to_re \"a\")))",
    );
}

#[test]
fn from_cvc5_term_re_loop() {
    term_round_trip(
        "(set-logic QF_S) (declare-const s String)",
        "(str.in_re s ((_ re.loop 2 5) (str.to_re \"a\")))",
    );
}

#[test]
fn from_cvc5_term_string_contains() {
    term_round_trip(
        "(set-logic QF_S) (declare-const s String)",
        "(str.contains s \"hello\")",
    );
}

#[test]
fn from_cvc5_term_abs() {
    term_round_trip("(set-logic QF_NIA) (declare-const x Int)", "(abs x)");
}

#[test]
fn from_cvc5_term_to_real() {
    term_round_trip("(set-logic AUFLIRA) (declare-const x Int)", "(to_real x)");
}

#[test]
fn from_cvc5_term_to_int() {
    term_round_trip("(set-logic AUFLIRA) (declare-const x Real)", "(to_int x)");
}

#[test]
fn from_cvc5_term_bv_slt() {
    term_round_trip(
        "(set-logic QF_BV) (declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8))",
        "(bvslt x y)",
    );
}

#[test]
fn from_cvc5_term_bv_sdiv() {
    term_round_trip(
        "(set-logic QF_BV) (declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8))",
        "(bvsdiv x y)",
    );
}

#[test]
fn from_cvc5_term_re_union() {
    term_round_trip(
        "(set-logic QF_S) (declare-const s String)",
        "(str.in_re s (re.union (str.to_re \"a\") (str.to_re \"b\")))",
    );
}

#[test]
fn from_cvc5_term_re_inter() {
    term_round_trip(
        "(set-logic QF_S) (declare-const s String)",
        "(str.in_re s (re.inter (re.* (str.to_re \"a\")) (re.* (str.to_re \"b\"))))",
    );
}

#[test]
fn from_cvc5_term_re_comp() {
    term_round_trip(
        "(set-logic QF_S) (declare-const s String)",
        "(str.in_re s (re.comp (str.to_re \"a\")))",
    );
}

#[test]
fn from_cvc5_term_str_replace() {
    term_round_trip(
        "(set-logic QF_S) (declare-const s String)",
        "(str.replace s \"a\" \"b\")",
    );
}

#[test]
fn from_cvc5_term_str_indexof() {
    term_round_trip(
        "(set-logic QF_S) (declare-const s String)",
        "(str.indexof s \"a\" 0)",
    );
}

#[test]
fn from_cvc5_term_str_substr() {
    term_round_trip(
        "(set-logic QF_S) (declare-const s String)",
        "(str.substr s 0 3)",
    );
}

#[test]
fn from_cvc5_term_str_prefixof() {
    term_round_trip(
        "(set-logic QF_S) (declare-const s String)",
        "(str.prefixof \"he\" s)",
    );
}

#[test]
fn from_cvc5_term_hex_bv_literal() {
    // The forward-cached round-trip returns the original Term unchanged.
    let mut ctx = Context::new();
    let _cmds = UntypedAst
        .parse_script_str("(set-logic QF_BV) (declare-const x (_ BitVec 8))")
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let term = UntypedAst
        .parse_term_str("(bvadd x #xab)")
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
    for cmd in &_cmds {
        cmd.to_cvc5(&mut es).unwrap();
    }
    let cterm = term.to_cvc5(&mut *es.env).unwrap();
    let back = cterm.conv_from_cvc5(&mut *es.env).unwrap();
    assert_eq!(back.to_string(), "(bvadd x #xab)");
}

#[test]
fn from_cvc5_term_exists_with_pattern() {
    term_round_trip(
        "(set-logic ALL) (declare-fun f (Int) Int)",
        "(exists ((x Int)) (! (= (f x) 0) :pattern ((f x))))",
    );
}

#[test]
fn from_cvc5_term_match_wildcard_catchall() {
    term_round_trip(
        "(set-logic ALL) (declare-datatypes ((Color 0)) (((Red) (Green) (Blue)))) (declare-const c Color)",
        "(match c ((Red 1) (x 0)))",
    );
}

#[test]
fn from_cvc5_term_parametric_datatype_constructor() {
    term_round_trip(
        "(set-logic ALL)
         (declare-datatypes ((List 1)) ((par (T) ((nil) (cons (head T) (tail (List T)))))))
         (declare-const x Int)",
        "(cons x (as nil (List Int)))",
    );
}

#[test]
fn from_cvc5_term_parametric_datatype_selector() {
    term_round_trip(
        "(set-logic ALL)
         (declare-datatypes ((List 1)) ((par (T) ((nil) (cons (head T) (tail (List T)))))))
         (declare-const l (List Int))",
        "(head l)",
    );
}

#[test]
fn from_cvc5_term_parametric_datatype_tester() {
    term_round_trip(
        "(set-logic ALL)
         (declare-datatypes ((List 1)) ((par (T) ((nil) (cons (head T) (tail (List T)))))))
         (declare-const l (List Int))",
        "((_ is cons) l)",
    );
}

#[test]
fn from_cvc5_term_match_anonymous_wildcard() {
    // Wildcard without a variable name: (_ 0)
    term_round_trip(
        "(set-logic ALL) (declare-datatypes ((Color 0)) (((Red) (Green) (Blue)))) (declare-const c Color)",
        "(match c ((Red 1) (_ 0)))",
    );
}

#[test]
fn from_cvc5_term_match_applied_with_anonymous_arg() {
    // Applied pattern with anonymous wildcard in selector position
    term_round_trip(
        "(set-logic ALL) (declare-datatypes ((Pair 0)) (((mkpair (fst Int) (snd Int))))) (declare-const p Pair)",
        "(match p (((mkpair x _) x)))",
    );
}

#[test]
fn from_cvc5_term_match_multiple_arms() {
    term_round_trip(
        "(set-logic ALL) (declare-datatypes ((Color 0)) (((Red) (Green) (Blue)))) (declare-const c Color)",
        "(match c ((Red 10) (Green 20) (Blue 30)))",
    );
}

#[test]
fn from_cvc5_term_match_nested() {
    term_round_trip(
        "(set-logic ALL)
         (declare-datatypes ((List 1)) ((par (T) ((nil) (cons (head T) (tail (List T)))))))
         (declare-const l (List Int))",
        "(match l ((nil 0) ((cons h t) (match t ((nil h) ((cons h2 t2) (+ h h2)))))))",
    );
}

#[test]
fn from_cvc5_term_const_array() {
    term_round_trip(
        "(set-logic ALL) (set-option :arrays-exp true) (declare-const a (Array Int Int))",
        "((as const (Array Int Int)) 0)",
    );
}

#[test]
fn from_cvc5_term_const_array_bool() {
    term_round_trip(
        "(set-logic ALL) (set-option :arrays-exp true) (declare-const a (Array Int Bool))",
        "((as const (Array Int Bool)) true)",
    );
}

// ── Tests for parametric match pattern constructor resolution ─────────
// These exercise the else branch in translate_match_case_from_cvc5 where
// ctor_term.has_symbol() is false (parametric/instantiated constructors).

#[test]
fn from_cvc5_match_parametric_nullary_single() {
    // Parametric List with nil (nullary) in a match pattern
    term_round_trip(
        "(set-logic ALL)
         (declare-datatypes ((List 1)) ((par (T) ((nil) (cons (head T) (tail (List T)))))))
         (declare-const l (List Int))",
        "(match l ((nil 0) ((cons h t) 1)))",
    );
}

#[test]
fn from_cvc5_match_parametric_multi_nullary() {
    // Parametric datatype with multiple nullary constructors — the key regression case.
    // The old code would always pick the first nullary constructor; this verifies each
    // nullary constructor is correctly identified.
    term_round_trip(
        "(set-logic ALL)
         (declare-datatypes ((Maybe 1)) ((par (T) ((nothing) (just (val T)) (unknown)))))
         (declare-const m (Maybe Int))",
        "(match m ((nothing 0) ((just x) x) (unknown (- 1))))",
    );
}

#[test]
fn from_cvc5_match_parametric_second_nullary() {
    // Match where the second nullary constructor appears — ensures we don't just pick the first.
    term_round_trip(
        "(set-logic ALL)
         (declare-datatypes ((Maybe 1)) ((par (T) ((nothing) (just (val T)) (unknown)))))
         (declare-const m (Maybe Int))",
        "(match m (((just x) x) (nothing 1) (unknown 2)))",
    );
}

#[test]
fn from_cvc5_match_parametric_bool_instantiation() {
    // Same parametric datatype instantiated at Bool
    term_round_trip(
        "(set-logic ALL)
         (declare-datatypes ((List 1)) ((par (T) ((nil) (cons (head T) (tail (List T)))))))
         (declare-const l (List Bool))",
        "(match l ((nil false) ((cons h t) h)))",
    );
}

// ── Backward translation built directly from cvc5 APIs ───────
//
// These tests construct cvc5 terms using only cvc5's own builders
// (no yaspar-ir parsing or term construction), then back-translate via
// `conv_from_cvc5` and compare the resulting yaspar-ir term's
// SMT-LIB-formatted `to_string()` against an expected literal.

/// Build a cvc5 environment, run a closure that constructs a CTerm using cvc5
/// APIs only, and assert that the back-translated yaspar-ir term's string
/// representation matches `expected`.
fn assert_back_eq<F>(expected: &str, build: F)
where
    F: for<'tm> FnOnce(&'tm TermManager) -> CTerm<'tm>,
{
    let tm = TermManager::new();
    let mut ctx = Context::new();
    ctx.ensure_logic();
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let cterm = build(&tm);
    let back = cterm.conv_from_cvc5(&mut env).unwrap();
    assert_eq!(back.to_string(), expected);
}

#[test]
fn back_from_cvc5_api_bool_true() {
    assert_back_eq("true", |tm| tm.mk_true());
}

#[test]
fn back_from_cvc5_api_bool_false() {
    assert_back_eq("false", |tm| tm.mk_false());
}

#[test]
fn back_from_cvc5_api_integer_literal() {
    assert_back_eq("42", |tm| tm.mk_integer(42));
}

#[test]
fn back_from_cvc5_api_const_int() {
    assert_back_eq("x", |tm| tm.mk_const(tm.integer_sort(), "x"));
}

#[test]
fn back_from_cvc5_api_add() {
    assert_back_eq("(+ x 1)", |tm| {
        let x = tm.mk_const(tm.integer_sort(), "x");
        let one = tm.mk_integer(1);
        tm.mk_term(Kind::Add, &[x, one])
    });
}

#[test]
fn back_from_cvc5_api_sub() {
    assert_back_eq("(- x y)", |tm| {
        let int = tm.integer_sort();
        let x = tm.mk_const(int.clone(), "x");
        let y = tm.mk_const(int, "y");
        tm.mk_term(Kind::Sub, &[x, y])
    });
}

#[test]
fn back_from_cvc5_api_mul() {
    assert_back_eq("(* x y)", |tm| {
        let int = tm.integer_sort();
        let x = tm.mk_const(int.clone(), "x");
        let y = tm.mk_const(int, "y");
        tm.mk_term(Kind::Mult, &[x, y])
    });
}

#[test]
fn back_from_cvc5_api_neg() {
    assert_back_eq("(- x)", |tm| {
        let x = tm.mk_const(tm.integer_sort(), "x");
        tm.mk_term(Kind::Neg, &[x])
    });
}

#[test]
fn back_from_cvc5_api_lt() {
    assert_back_eq("(< x y)", |tm| {
        let int = tm.integer_sort();
        let x = tm.mk_const(int.clone(), "x");
        let y = tm.mk_const(int, "y");
        tm.mk_term(Kind::Lt, &[x, y])
    });
}

#[test]
fn back_from_cvc5_api_le() {
    assert_back_eq("(<= x y)", |tm| {
        let int = tm.integer_sort();
        let x = tm.mk_const(int.clone(), "x");
        let y = tm.mk_const(int, "y");
        tm.mk_term(Kind::Leq, &[x, y])
    });
}

#[test]
fn back_from_cvc5_api_gt() {
    assert_back_eq("(> x y)", |tm| {
        let int = tm.integer_sort();
        let x = tm.mk_const(int.clone(), "x");
        let y = tm.mk_const(int, "y");
        tm.mk_term(Kind::Gt, &[x, y])
    });
}

#[test]
fn back_from_cvc5_api_ge() {
    assert_back_eq("(>= x y)", |tm| {
        let int = tm.integer_sort();
        let x = tm.mk_const(int.clone(), "x");
        let y = tm.mk_const(int, "y");
        tm.mk_term(Kind::Geq, &[x, y])
    });
}

#[test]
fn back_from_cvc5_api_and() {
    assert_back_eq("(and a b)", |tm| {
        let bool_sort = tm.boolean_sort();
        let a = tm.mk_const(bool_sort.clone(), "a");
        let b = tm.mk_const(bool_sort, "b");
        tm.mk_term(Kind::And, &[a, b])
    });
}

#[test]
fn back_from_cvc5_api_or() {
    assert_back_eq("(or a b)", |tm| {
        let bool_sort = tm.boolean_sort();
        let a = tm.mk_const(bool_sort.clone(), "a");
        let b = tm.mk_const(bool_sort, "b");
        tm.mk_term(Kind::Or, &[a, b])
    });
}

#[test]
fn back_from_cvc5_api_not() {
    assert_back_eq("(not a)", |tm| {
        let a = tm.mk_const(tm.boolean_sort(), "a");
        tm.mk_term(Kind::Not, &[a])
    });
}

#[test]
fn back_from_cvc5_api_xor() {
    assert_back_eq("(xor a b)", |tm| {
        let bool_sort = tm.boolean_sort();
        let a = tm.mk_const(bool_sort.clone(), "a");
        let b = tm.mk_const(bool_sort, "b");
        tm.mk_term(Kind::Xor, &[a, b])
    });
}

#[test]
fn back_from_cvc5_api_implies() {
    assert_back_eq("(=> a b)", |tm| {
        let bool_sort = tm.boolean_sort();
        let a = tm.mk_const(bool_sort.clone(), "a");
        let b = tm.mk_const(bool_sort, "b");
        tm.mk_term(Kind::Implies, &[a, b])
    });
}

#[test]
fn back_from_cvc5_api_eq() {
    assert_back_eq("(= x y)", |tm| {
        let int = tm.integer_sort();
        let x = tm.mk_const(int.clone(), "x");
        let y = tm.mk_const(int, "y");
        tm.mk_term(Kind::Equal, &[x, y])
    });
}

#[test]
fn back_from_cvc5_api_eq_chain_three() {
    // n-ary cvc5 equality back-translates to a conjunction of pairwise equalities
    assert_back_eq("(and (= x y) (= y z))", |tm| {
        let int = tm.integer_sort();
        let x = tm.mk_const(int.clone(), "x");
        let y = tm.mk_const(int.clone(), "y");
        let z = tm.mk_const(int, "z");
        tm.mk_term(Kind::Equal, &[x, y, z])
    });
}

#[test]
fn back_from_cvc5_api_distinct() {
    assert_back_eq("(distinct x y z)", |tm| {
        let int = tm.integer_sort();
        let x = tm.mk_const(int.clone(), "x");
        let y = tm.mk_const(int.clone(), "y");
        let z = tm.mk_const(int, "z");
        tm.mk_term(Kind::Distinct, &[x, y, z])
    });
}

#[test]
fn back_from_cvc5_api_ite() {
    assert_back_eq("(ite a x y)", |tm| {
        let int = tm.integer_sort();
        let a = tm.mk_const(tm.boolean_sort(), "a");
        let x = tm.mk_const(int.clone(), "x");
        let y = tm.mk_const(int, "y");
        tm.mk_term(Kind::Ite, &[a, x, y])
    });
}

#[test]
fn back_from_cvc5_api_uf_application() {
    assert_back_eq("(f x y)", |tm| {
        let int = tm.integer_sort();
        let fun_sort = tm.mk_fun_sort(&[int.clone(), int.clone()], int.clone());
        let f = tm.mk_const(fun_sort, "f");
        let x = tm.mk_const(int.clone(), "x");
        let y = tm.mk_const(int, "y");
        tm.mk_term(Kind::ApplyUf, &[f, x, y])
    });
}

#[test]
fn back_from_cvc5_api_select_store() {
    assert_back_eq("(select (store a i v) i)", |tm| {
        let int = tm.integer_sort();
        let arr = tm.mk_array_sort(int.clone(), int.clone());
        let a = tm.mk_const(arr, "a");
        let i = tm.mk_const(int.clone(), "i");
        let v = tm.mk_const(int, "v");
        let store = tm.mk_term(Kind::Store, &[a, i.clone(), v]);
        tm.mk_term(Kind::Select, &[store, i])
    });
}

#[test]
fn back_from_cvc5_api_bv_add() {
    assert_back_eq("(bvadd x y)", |tm| {
        let bv8 = tm.mk_bv_sort(8);
        let x = tm.mk_const(bv8.clone(), "x");
        let y = tm.mk_const(bv8, "y");
        tm.mk_term(Kind::BitvectorAdd, &[x, y])
    });
}

#[test]
fn back_from_cvc5_api_bv_not() {
    assert_back_eq("(bvnot x)", |tm| {
        let x = tm.mk_const(tm.mk_bv_sort(8), "x");
        tm.mk_term(Kind::BitvectorNot, &[x])
    });
}

#[test]
fn back_from_cvc5_api_bv_concat() {
    assert_back_eq("(concat x y)", |tm| {
        let bv4 = tm.mk_bv_sort(4);
        let x = tm.mk_const(bv4.clone(), "x");
        let y = tm.mk_const(bv4, "y");
        tm.mk_term(Kind::BitvectorConcat, &[x, y])
    });
}

#[test]
fn back_from_cvc5_api_bv_extract() {
    assert_back_eq("((_ extract 3 0) x)", |tm| {
        let x = tm.mk_const(tm.mk_bv_sort(8), "x");
        let op = tm.mk_op(Kind::BitvectorExtract, &[3, 0]);
        tm.mk_term_from_op(op, &[x])
    });
}

#[test]
fn back_from_cvc5_api_bv_zero_extend() {
    assert_back_eq("((_ zero_extend 8) x)", |tm| {
        let x = tm.mk_const(tm.mk_bv_sort(8), "x");
        let op = tm.mk_op(Kind::BitvectorZeroExtend, &[8]);
        tm.mk_term_from_op(op, &[x])
    });
}

#[test]
fn back_from_cvc5_api_bv_repeat() {
    assert_back_eq("((_ repeat 2) x)", |tm| {
        let x = tm.mk_const(tm.mk_bv_sort(4), "x");
        let op = tm.mk_op(Kind::BitvectorRepeat, &[2]);
        tm.mk_term_from_op(op, &[x])
    });
}

#[test]
fn back_from_cvc5_api_bv_rotate_left() {
    assert_back_eq("((_ rotate_left 3) x)", |tm| {
        let x = tm.mk_const(tm.mk_bv_sort(8), "x");
        let op = tm.mk_op(Kind::BitvectorRotateLeft, &[3]);
        tm.mk_term_from_op(op, &[x])
    });
}

#[test]
fn back_from_cvc5_api_string_concat() {
    assert_back_eq("(str.++ s1 s2)", |tm| {
        let str_sort = tm.string_sort();
        let s1 = tm.mk_const(str_sort.clone(), "s1");
        let s2 = tm.mk_const(str_sort, "s2");
        tm.mk_term(Kind::StringConcat, &[s1, s2])
    });
}

#[test]
fn back_from_cvc5_api_string_len() {
    assert_back_eq("(str.len s)", |tm| {
        let s = tm.mk_const(tm.string_sort(), "s");
        tm.mk_term(Kind::StringLength, &[s])
    });
}

#[test]
fn back_from_cvc5_api_re_none() {
    assert_back_eq("re.none", |tm| tm.mk_regexp_none());
}

#[test]
fn back_from_cvc5_api_re_all() {
    assert_back_eq("re.all", |tm| tm.mk_regexp_all());
}

#[test]
fn back_from_cvc5_api_re_allchar() {
    assert_back_eq("re.allchar", |tm| tm.mk_regexp_allchar());
}

#[test]
fn back_from_cvc5_api_forall() {
    assert_back_eq("(forall ((x Int)) (> x 0))", |tm| {
        let int = tm.integer_sort();
        let x = tm.mk_var(int, "x");
        let zero = tm.mk_integer(0);
        let body = tm.mk_term(Kind::Gt, &[x.clone(), zero]);
        let bound = tm.mk_term(Kind::VariableList, std::slice::from_ref(&x));
        tm.mk_term(Kind::Forall, &[bound, body])
    });
}

#[test]
fn back_from_cvc5_api_exists() {
    assert_back_eq("(exists ((x Int)) (= x 0))", |tm| {
        let int = tm.integer_sort();
        let x = tm.mk_var(int, "x");
        let zero = tm.mk_integer(0);
        let body = tm.mk_term(Kind::Equal, &[x.clone(), zero]);
        let bound = tm.mk_term(Kind::VariableList, std::slice::from_ref(&x));
        tm.mk_term(Kind::Exists, &[bound, body])
    });
}

#[test]
fn back_from_cvc5_api_nested_arithmetic() {
    assert_back_eq("(+ (* x 2) y)", |tm| {
        let int = tm.integer_sort();
        let x = tm.mk_const(int.clone(), "x");
        let y = tm.mk_const(int, "y");
        let two = tm.mk_integer(2);
        let mul = tm.mk_term(Kind::Mult, &[x, two]);
        tm.mk_term(Kind::Add, &[mul, y])
    });
}

#[test]
fn back_from_cvc5_api_datatype_nullary_constructor() {
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    solver.set_logic("ALL");
    let red = tm.mk_dt_cons_decl("Red");
    let green = tm.mk_dt_cons_decl("Green");
    let blue = tm.mk_dt_cons_decl("Blue");
    let color_sort = solver.declare_dt("Color", &[red, green, blue]);
    let dt = color_sort.datatype();
    let ctor = dt.constructor(0).term();
    let red_term = tm.mk_term(Kind::ApplyConstructor, &[ctor]);

    let mut ctx = Context::new();
    ctx.ensure_logic();
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let back = red_term.conv_from_cvc5(&mut env).unwrap();
    assert_eq!(back.to_string(), "Red");
}

#[test]
fn back_from_cvc5_api_datatype_applied_constructor() {
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    solver.set_logic("ALL");
    let int = tm.integer_sort();
    let mut mkpair = tm.mk_dt_cons_decl("mkpair");
    mkpair.add_selector("fst", int.clone());
    mkpair.add_selector("snd", int.clone());
    let pair_sort = solver.declare_dt("Pair", &[mkpair]);
    let dt = pair_sort.datatype();
    let ctor = dt.constructor(0).term();
    let one = tm.mk_integer(1);
    let two = tm.mk_integer(2);
    let pair = tm.mk_term(Kind::ApplyConstructor, &[ctor, one, two]);

    let mut ctx = Context::new();
    ctx.ensure_logic();
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let back = pair.conv_from_cvc5(&mut env).unwrap();
    assert_eq!(back.to_string(), "(mkpair 1 2)");
}

#[test]
fn back_from_cvc5_api_datatype_selector() {
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    solver.set_logic("ALL");
    let int = tm.integer_sort();
    let mut mkpair = tm.mk_dt_cons_decl("mkpair");
    mkpair.add_selector("fst", int.clone());
    mkpair.add_selector("snd", int.clone());
    let pair_sort = solver.declare_dt("Pair", &[mkpair]);
    let dt = pair_sort.datatype();
    let sel = dt.constructor(0).selector(0).term();
    let p = tm.mk_const(pair_sort, "p");
    let fst_p = tm.mk_term(Kind::ApplySelector, &[sel, p]);

    let mut ctx = Context::new();
    ctx.ensure_logic();
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let back = fst_p.conv_from_cvc5(&mut env).unwrap();
    assert_eq!(back.to_string(), "(fst p)");
}

#[test]
fn back_from_cvc5_api_datatype_tester() {
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    solver.set_logic("ALL");
    let red = tm.mk_dt_cons_decl("Red");
    let green = tm.mk_dt_cons_decl("Green");
    let blue = tm.mk_dt_cons_decl("Blue");
    let color_sort = solver.declare_dt("Color", &[red, green, blue]);
    let dt = color_sort.datatype();
    let tester = dt.constructor(0).tester_term();
    let c = tm.mk_const(color_sort, "c");
    let is_red = tm.mk_term(Kind::ApplyTester, &[tester, c]);

    let mut ctx = Context::new();
    ctx.ensure_logic();
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let back = is_red.conv_from_cvc5(&mut env).unwrap();
    assert_eq!(back.to_string(), "((_ is Red) c)");
}

#[test]
fn back_from_cvc5_api_const_array() {
    assert_back_eq("((as const (Array Int Int)) 0)", |tm| {
        let int = tm.integer_sort();
        let arr = tm.mk_array_sort(int.clone(), int);
        let zero = tm.mk_integer(0);
        tm.mk_const_array(arr, zero)
    });
}
