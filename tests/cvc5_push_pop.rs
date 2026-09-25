// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! `push`, `pop`, `reset-assertions` and `reset` through the cvc5 backend.

#![cfg(feature = "cvc5-dep")]

use cvc5::{Solver, TermManager};
use yaspar_ir::ast::{Command, Context, Term, Typecheck};
use yaspar_ir::cvc5::{CommandResult, ConvertToCvc5, Cvc5Env, Cvc5EnvSolver};
use yaspar_ir::untyped::UntypedAst;

fn tc(ctx: &mut Context, script: &str) -> Vec<Command> {
    UntypedAst
        .parse_script_str(script)
        .unwrap()
        .type_check(ctx)
        .unwrap()
}

/// Run a script through cvc5 and collect the `check-sat` results (`true` for sat) and the
/// `get-value` results.
fn run(script: &str) -> (Vec<bool>, Vec<Vec<Term>>) {
    let mut ctx = Context::new();
    let cmds = tc(&mut ctx, script);
    let tm = TermManager::new();
    let solver = Solver::new(&tm);
    solver.set_option("produce-models", "true");
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let mut es = Cvc5EnvSolver::new(&mut env, &solver);
    let mut sats = vec![];
    let mut values = vec![];
    for cmd in &cmds {
        match cmd.to_cvc5(&mut es).unwrap() {
            CommandResult::CheckSat(r) => {
                assert!(r.is_sat() || r.is_unsat());
                sats.push(r.is_sat());
            }
            CommandResult::GetValue(ts) => values.push(ts),
            _ => {}
        }
    }
    (sats, values)
}

#[test]
fn test_push_pop_assertions() {
    let (sats, _) = run(r#"
        (set-logic ALL)
        (declare-const x Int)
        (assert (> x 0))
        (push 1)
        (assert (< x 0))
        (check-sat)
        (pop 1)
        (check-sat)
        (push 2)
        (assert (< x 0))
        (push 1)
        (check-sat)
        (pop 1)
        (check-sat)
        (pop 2)
        (check-sat)
    "#);
    assert_eq!(sats, vec![false, true, false, false, true]);
}

#[test]
fn test_pop_redeclarations() {
    // `y` and `D` are declared again after being popped; the new declarations must be used,
    // even though they are the same hash-consed yaspar-ir objects as the popped ones
    let (sats, values) = run(r#"
        (set-logic ALL)
        (push 1)
        (declare-const y Int)
        (assert (= y 1))
        (declare-datatype D ((A) (B)))
        (declare-const d D)
        (assert (= d A))
        (check-sat)
        (get-value (y d))
        (pop 1)
        (declare-const y Int)
        (assert (= y 2))
        (declare-datatype D ((C) (E)))
        (declare-const d D)
        (assert (= d E))
        (check-sat)
        (get-value (y d))
    "#);
    assert_eq!(sats, vec![true, true]);
    let values = values
        .iter()
        .map(|ts| ts.iter().map(|t| t.to_string()).collect::<Vec<_>>())
        .collect::<Vec<_>>();
    assert_eq!(values, vec![vec!["1", "A"], vec!["2", "E"]]);
}

#[test]
fn test_pop_named_assertions() {
    let mut ctx = Context::new();
    let cmds = tc(
        &mut ctx,
        r#"
        (set-logic ALL)
        (set-option :produce-unsat-cores true)
        (declare-const x Int)
        (assert (! (> x 0) :named pos))
        (push 1)
        (assert (! (< x 0) :named neg))
        (check-sat)
        (get-unsat-core)
        (pop 1)
        (assert (! (< x 0) :named neg2))
        (check-sat)
        (get-unsat-core)
    "#,
    );
    let tm = TermManager::new();
    let solver = Solver::new(&tm);
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let mut es = Cvc5EnvSolver::new(&mut env, &solver);
    let mut cores = vec![];
    for cmd in &cmds {
        if let CommandResult::Terms(ts) = cmd.to_cvc5(&mut es).unwrap() {
            let mut names = ts.iter().map(|t| t.to_string()).collect::<Vec<_>>();
            names.sort();
            cores.push(names);
        }
    }
    assert_eq!(cores, vec![vec!["neg", "pos"], vec!["neg2", "pos"]]);
}

#[test]
fn test_reset_assertions_pops_levels() {
    let mut ctx = Context::new();
    let cmds = tc(
        &mut ctx,
        "(set-logic ALL) (push 2) (reset-assertions) (pop 1)",
    );
    let tm = TermManager::new();
    let solver = Solver::new(&tm);
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let mut es = Cvc5EnvSolver::new(&mut env, &solver);
    cmds[0].to_cvc5(&mut es).unwrap();
    cmds[1].to_cvc5(&mut es).unwrap();
    assert_eq!(es.env.assertion_level(), 2);
    cmds[2].to_cvc5(&mut es).unwrap();
    assert_eq!(es.env.assertion_level(), 0);
    // nothing is left to pop
    assert!(cmds[3].to_cvc5(&mut es).is_err());
}

#[test]
fn test_pop_too_many() {
    let mut ctx = Context::new();
    let cmds = tc(&mut ctx, "(set-logic ALL) (push 1) (pop 1)");
    let tm = TermManager::new();
    let solver = Solver::new(&tm);
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    let mut es = Cvc5EnvSolver::new(&mut env, &solver);
    for cmd in &cmds {
        cmd.to_cvc5(&mut es).unwrap();
    }
    assert!(cmds[2].to_cvc5(&mut es).is_err());
    assert_eq!(es.env.assertion_level(), 0);
}

#[test]
fn test_reset_with_fresh_solver() {
    let mut ctx = Context::new();
    let cmds = tc(
        &mut ctx,
        r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 0))
        (push 1)
        (reset)
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (< x 0))
        (check-sat)
    "#,
    );
    let tm = TermManager::new();
    let mut env = Cvc5Env::new(&tm, &mut ctx);
    {
        let solver = Solver::new(&tm);
        let mut es = Cvc5EnvSolver::new(&mut env, &solver);
        for cmd in &cmds[..4] {
            cmd.to_cvc5(&mut es).unwrap();
        }
        // cvc5 cannot reset a solver in place
        assert!(cmds[4].to_cvc5(&mut es).is_err());
    }
    env.reset_env();
    assert_eq!(env.assertion_level(), 0);
    let solver = Solver::new(&tm);
    let mut es = Cvc5EnvSolver::new(&mut env, &solver);
    for cmd in &cmds[5..8] {
        cmd.to_cvc5(&mut es).unwrap();
    }
    match cmds[8].to_cvc5(&mut es).unwrap() {
        CommandResult::CheckSat(r) => assert!(r.is_sat()),
        r => panic!("unexpected result {r:?}"),
    }
}
