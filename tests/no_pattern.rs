// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for the `no-pattern` feature: parsing the non-standard
//! `:no-pattern <term>` quantifier attribute emitted by Dafny/Boogie.
//!
//! These tests only run when the `no-pattern` feature is enabled (the attribute
//! is not part of the SMT-LIB 2.7 grammar otherwise). See issue #122.

#![cfg(feature = "no-pattern")]

use yaspar_ir::ast::{Context, Typecheck};
use yaspar_ir::untyped::UntypedAst;

/// A quantifier carrying both `:pattern` and `:no-pattern` (the Dafny/Boogie
/// shape) parses and type-checks.
#[test]
fn parses_no_pattern_attribute() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-fun p (Int) Bool)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int))
            (! (p (f x)) :pattern ((p (f x))) :no-pattern (f x))))
    "#,
        )
        .expect("script with :no-pattern should parse")
        .type_check(&mut ctx)
        .expect("script with :no-pattern should type-check");
    assert_eq!(cmds.len(), 4);
}

/// The `:no-pattern` term is preserved (not dropped): the parsed AST round-trips
/// through `Display` with the annotated term still present.
#[test]
fn no_pattern_term_is_preserved() {
    let cmds = UntypedAst
        .parse_script_str("(assert (forall ((x Int)) (! (p x) :no-pattern (f x))))")
        .expect("parse");
    let printed = format!("{}", cmds[0]);
    assert!(
        printed.contains(":no-pattern"),
        "expected :no-pattern to survive Display, got: {printed}"
    );
    assert!(
        printed.contains("f x") || printed.contains("(f x)"),
        "expected the excluded term (f x) to survive Display, got: {printed}"
    );
}
