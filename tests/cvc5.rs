// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#![cfg(feature = "cvc5")]

use cvc5::{Solver, TermManager};
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
    let mut env = Cvc5Env::create(&tm);
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
    let mut env = Cvc5Env::create(&tm);
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
    let mut env = Cvc5Env::create(&tm);
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
    let mut env = Cvc5Env::create(&tm);
    assert!(x.to_cvc5(&mut env).is_err());
}

#[test]
fn error_unsupported_sort() {
    let mut ctx = Context::new();
    ctx.ensure_logic();
    // A custom sort that cvc5 doesn't know about
    let custom = ctx.simple_sort("MyCustomSort");
    let tm = TermManager::new();
    let mut env = Cvc5Env::create(&tm);
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
    let mut env = Cvc5Env::create(&tm);

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
    let mut env = Cvc5Env::create(&tm);
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
    let mut env = Cvc5Env::create(&tm);
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
    let mut env = Cvc5Env::create(&tm);
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
    let mut env = Cvc5Env::create(&tm);
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

use yaspar_ir::cvc5::{ConvertFromCvc5, FromCvc5Env};

/// Helper: translate a yaspar-ir Sort to cvc5 and back, asserting the round-trip
/// produces the same string representation.
fn sort_round_trip(script: &str, sort_str: &str) {
    let mut ctx = Context::new();
    let _cmds = UntypedAst
        .parse_script_str(script)
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    let mut env = Cvc5Env::create(&tm);
    let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
    for cmd in &_cmds {
        cmd.to_cvc5(&mut es).unwrap();
    }
    let sort = UntypedAst
        .parse_sort_str(sort_str)
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let csort = sort.to_cvc5(&mut *es.env).unwrap();
    let mut from_env = FromCvc5Env::new(&mut ctx);
    let back = csort.conv_from_cvc5(&mut from_env).unwrap();
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
    let mut from_env = FromCvc5Env::new(&mut ctx);
    let back1 = csort.conv_from_cvc5(&mut from_env).unwrap();
    let back2 = csort.conv_from_cvc5(&mut from_env).unwrap();
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
