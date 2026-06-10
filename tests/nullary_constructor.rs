// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use yaspar_ir::ast::{CheckedApi, Context, Typecheck};
use yaspar_ir::untyped::UntypedAst;

#[test]
fn nullary_constructor() {
    let mut ctx = Context::new();
    ctx.ensure_logic();

    // Declare a datatype with a nullary constructor
    let cmd = UntypedAst
        .parse_command_str("(declare-datatype Color ((Red) (Green) (Blue)))")
        .unwrap();
    cmd.type_check(&mut ctx).unwrap();

    // Apply the nullary constructor via the typed API (same path the solver client uses)
    let term = ctx.typed_simp_app("Red", std::iter::empty());
    assert!(term.is_err());
}
