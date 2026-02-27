// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use dashu::integer::UBig;
use yaspar_ir::ast::{Context, FetchSort, ObjectAllocatorExt, Typecheck};
use yaspar_ir::untyped::UntypedAst;

#[test]
fn test_sort_equality() {
    let mut ctx = Context::new();
    ctx.ensure_logic();

    let int1 = ctx.int_sort();
    let int2 = ctx.int_sort();

    assert_eq!(int1, int2);
}

#[test]
fn test_term_get_sort() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-const x Int)
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let int_sort = ctx.int_sort();
    let x = ctx.simple_sorted_symbol("x", int_sort.clone());
    let sort = x.get_sort(&mut ctx);

    assert_eq!(sort, int_sort);
}

#[test]
fn test_string_sort() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-const s String)
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let string_sort = ctx.string_sort();
    let s = ctx.simple_sorted_symbol("s", string_sort.clone());
    let sort = s.get_sort(&mut ctx);

    assert_eq!(sort, string_sort);
}

#[test]
fn test_bitvector_sort() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-const bv (_ BitVec 8))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let bv_sort = ctx.bv_sort(UBig::from(8u32));
    let bv = ctx.simple_sorted_symbol("bv", bv_sort.clone());
    let sort = bv.get_sort(&mut ctx);

    assert_eq!(sort, bv_sort);
}

#[test]
fn test_real_sort() {
    let mut ctx = Context::new();
    ctx.ensure_logic();

    let real_sort = ctx.real_sort();
    assert_eq!(real_sort.to_string(), "Real");
}
