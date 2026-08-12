// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use yaspar_ir::ast::alg::QualifiedIdentifier;
use yaspar_ir::ast::{CheckedApi, Context, ScopedSortApi, StrAllocator, TermAllocator, Typecheck};
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

#[test]
fn displays_inferred_sort_for_parametric_nullary_constructor() {
    let mut ctx = Context::new();
    ctx.ensure_logic();

    UntypedAst
        .parse_script_str(
            "(declare-sort Val 0)
             (declare-datatypes ((Option 1))
               ((par (T) ((None) (Some (value T))))))",
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let val = ctx.wf_sort("Val").unwrap();
    let option_val = ctx.wf_sort_n("Option", [val]).unwrap();
    let none = ctx.allocate_symbol("None");
    let term = ctx.global(QualifiedIdentifier::simple(none), Some(option_val));
    let formatted = term.to_string();

    assert_eq!(formatted, "(as None (Option Val))");
    UntypedAst
        .parse_term_str(&formatted)
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
}
