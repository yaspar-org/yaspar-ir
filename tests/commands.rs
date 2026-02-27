// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use yaspar_ir::ast::{Context, Typecheck};
use yaspar_ir::untyped::UntypedAst;

#[test]
fn test_set_info() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (set-info :source "test")
        (set-info :smt-lib-version 2.6)
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    assert_eq!(cmds.len(), 3);
    assert_eq!(cmds[0].to_string(), "(set-logic ALL)");
    assert_eq!(cmds[1].to_string(), "(set-info :source \"test\")");
    assert_eq!(cmds[2].to_string(), "(set-info :smt-lib-version 2.6)");
}

#[test]
fn test_set_option() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (set-option :produce-models true)
        (set-option :produce-unsat-cores true)
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    assert_eq!(cmds.len(), 3);
    assert_eq!(cmds[0].to_string(), "(set-logic ALL)");
    assert_eq!(cmds[1].to_string(), "(set-option :produce-models true)");
    assert_eq!(
        cmds[2].to_string(),
        "(set-option :produce-unsat-cores true)"
    );
}

#[test]
fn test_push_pop() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-const x Int)
        (push 1)
        (assert (> x 0))
        (pop 1)
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    assert_eq!(cmds.len(), 5);
    assert_eq!(cmds[0].to_string(), "(set-logic ALL)");
    assert_eq!(cmds[1].to_string(), "(declare-const x Int)");
    assert_eq!(cmds[2].to_string(), "(push 1)");
    assert_eq!(cmds[3].to_string(), "(assert (> x 0))");
    assert_eq!(cmds[4].to_string(), "(pop 1)");
}

#[test]
fn test_check_sat() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-const p Bool)
        (assert p)
        (check-sat)
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    assert_eq!(cmds.len(), 4);
    assert_eq!(cmds[0].to_string(), "(set-logic ALL)");
    assert_eq!(cmds[1].to_string(), "(declare-const p Bool)");
    assert_eq!(cmds[2].to_string(), "(assert p)");
    assert_eq!(cmds[3].to_string(), "(check-sat)");
}

#[test]
fn test_get_model() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-const x Int)
        (assert (= x 5))
        (check-sat)
        (get-model)
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    assert_eq!(cmds.len(), 5);
    assert_eq!(cmds[0].to_string(), "(set-logic ALL)");
    assert_eq!(cmds[1].to_string(), "(declare-const x Int)");
    assert_eq!(cmds[2].to_string(), "(assert (= x 5))");
    assert_eq!(cmds[3].to_string(), "(check-sat)");
    assert_eq!(cmds[4].to_string(), "(get-model)");
}

#[test]
fn test_get_value() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-const x Int)
        (assert (= x 5))
        (check-sat)
        (get-value (x))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    assert_eq!(cmds.len(), 5);
    assert_eq!(cmds[0].to_string(), "(set-logic ALL)");
    assert_eq!(cmds[1].to_string(), "(declare-const x Int)");
    assert_eq!(cmds[2].to_string(), "(assert (= x 5))");
    assert_eq!(cmds[3].to_string(), "(check-sat)");
    assert_eq!(cmds[4].to_string(), "(get-value (x))");
}

#[test]
fn test_get_assertions() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-const p Bool)
        (assert p)
        (get-assertions)
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    assert_eq!(cmds.len(), 4);
    assert_eq!(cmds[0].to_string(), "(set-logic ALL)");
    assert_eq!(cmds[1].to_string(), "(declare-const p Bool)");
    assert_eq!(cmds[2].to_string(), "(assert p)");
    assert_eq!(cmds[3].to_string(), "(get-assertions)");
}

#[test]
fn test_reset() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-const x Int)
        (reset)
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    assert_eq!(cmds.len(), 3);
    assert_eq!(cmds[0].to_string(), "(set-logic ALL)");
    assert_eq!(cmds[1].to_string(), "(declare-const x Int)");
    assert_eq!(cmds[2].to_string(), "(reset)");
}

#[test]
fn test_exit() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (exit)
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    assert_eq!(cmds.len(), 2);
    assert_eq!(cmds[0].to_string(), "(set-logic ALL)");
    assert_eq!(cmds[1].to_string(), "(exit)");
}
