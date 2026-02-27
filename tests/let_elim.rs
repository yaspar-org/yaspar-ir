// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use yaspar_ir::ast::{Context, LetElim, Typecheck};
use yaspar_ir::traits::Repr;
use yaspar_ir::untyped::UntypedAst;

#[test]
fn test_let_elim_simple() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (assert (let ((x 1)) (= x 1)))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    if let yaspar_ir::ast::ACommand::Assert(t) = cmds[1].repr() {
        let elim = t.let_elim(&mut ctx);
        assert_eq!(elim.to_string(), "(= 1 1)");
    }
}

#[test]
fn test_let_elim_nested() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (assert (let ((x 1)) (let ((y 2)) (= (+ x y) 3))))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    if let yaspar_ir::ast::ACommand::Assert(t) = cmds[1].repr() {
        let elim = t.let_elim(&mut ctx);
        assert_eq!(elim.to_string(), "(= (+ 1 2) 3)");
    }
}

#[test]
fn test_let_elim_multiple_bindings() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (assert (let ((x 1) (y 2) (z 3)) (= (+ x (+ y z)) 6)))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    if let yaspar_ir::ast::ACommand::Assert(t) = cmds[1].repr() {
        let elim = t.let_elim(&mut ctx);
        assert_eq!(elim.to_string(), "(= (+ 1 (+ 2 3)) 6)");
    }
}
