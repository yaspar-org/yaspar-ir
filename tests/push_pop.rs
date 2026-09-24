// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Scoping of declarations under `push`, `pop` and `reset`.

use yaspar_ir::ast::{
    Command, Context, GlobalSubst, ObjectAllocatorExt, Repr, Sig, StrAllocator, TC, Term,
    Typecheck, alg,
};
use yaspar_ir::untyped::UntypedAst;

fn tc(ctx: &mut Context, script: &str) -> TC<Vec<Command>> {
    UntypedAst.parse_script_str(script).unwrap().type_check(ctx)
}

#[test]
fn test_pop_discards_declarations() {
    let mut ctx = Context::new();
    tc(
        &mut ctx,
        r#"
        (set-logic ALL)
        (declare-const x Int)
        (push 1)
        (declare-sort S 0)
        (declare-const y S)
        (assert (! (> x 0) :named a))
    "#,
    )
    .unwrap();
    assert_eq!(ctx.assertion_level(), 1);
    tc(&mut ctx, "(pop 1)").unwrap();
    assert_eq!(ctx.assertion_level(), 0);

    assert!(tc(&mut ctx, "(assert (> x 1))").is_ok());
    assert!(tc(&mut ctx, "(declare-const z S)").is_err());
    assert!(tc(&mut ctx, "(assert a)").is_err());
    // popped names can be declared again
    tc(
        &mut ctx,
        r#"
        (declare-const y Bool)
        (declare-sort S 1)
        (assert y)
    "#,
    )
    .unwrap();
}

#[test]
fn test_nested_levels() {
    let mut ctx = Context::new();
    tc(
        &mut ctx,
        r#"
        (set-logic ALL)
        (push 1)
        (declare-const x Int)
        (push 2)
        (declare-const y Int)
        (pop 1)
        (declare-const z Int)
    "#,
    )
    .unwrap();
    assert_eq!(ctx.assertion_level(), 2);
    // `y` is gone, `x` survives
    assert!(tc(&mut ctx, "(assert (> y 0))").is_err());
    tc(&mut ctx, "(assert (> x z))").unwrap();
    tc(&mut ctx, "(pop 1)").unwrap();
    assert!(tc(&mut ctx, "(assert (> z 0))").is_err());
    tc(&mut ctx, "(assert (> x 0))").unwrap();
    tc(&mut ctx, "(pop 1)").unwrap();
    assert!(tc(&mut ctx, "(assert (> x 0))").is_err());
}

#[test]
fn test_push_pop_zero() {
    let mut ctx = Context::new();
    tc(
        &mut ctx,
        r#"
        (set-logic ALL)
        (push 0)
        (declare-const x Int)
        (pop 0)
        (assert (> x 0))
    "#,
    )
    .unwrap();
    assert_eq!(ctx.assertion_level(), 0);
}

#[test]
fn test_pop_too_many() {
    let mut ctx = Context::new();
    tc(&mut ctx, "(set-logic ALL) (push 2)").unwrap();
    assert!(tc(&mut ctx, "(pop 3)").is_err());
    // a failed pop leaves the levels untouched
    assert_eq!(ctx.assertion_level(), 2);
    tc(&mut ctx, "(pop 2)").unwrap();
    assert!(tc(&mut ctx, "(pop 1)").is_err());
}

fn last_assert(cmds: &[Command]) -> Term {
    cmds.iter()
        .rev()
        .find_map(|c| match c.repr() {
            alg::Command::Assert(t) => Some(t.clone()),
            _ => None,
        })
        .unwrap()
}

#[test]
fn test_pop_restores_definitions() {
    let mut ctx = Context::new();
    let cmds = tc(
        &mut ctx,
        r#"
        (set-logic ALL)
        (declare-const x Int)
        (push 1)
        (define-fun f () Int (+ x 1))
        (assert (> f 0))
    "#,
    )
    .unwrap();
    // expanding here populates the definition cache with the first `f`
    let t = last_assert(&cmds).gsubst_all(&mut ctx);
    assert_eq!(t.to_string(), "(> (+ x 1) 0)");
    let cmds = tc(
        &mut ctx,
        r#"
        (pop 1)
        (define-fun f () Int (+ x 2))
        (assert (> f 0))
    "#,
    )
    .unwrap();
    // expanding must not pick up the popped definition of `f`
    let t = last_assert(&cmds).gsubst_all(&mut ctx);
    assert_eq!(t.to_string(), "(> (+ x 2) 0)");
}

#[test]
fn test_reset() {
    let mut ctx = Context::new();
    tc(
        &mut ctx,
        r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (push 3)
        (declare-const y Int)
    "#,
    )
    .unwrap();
    tc(&mut ctx, "(reset)").unwrap();
    assert_eq!(ctx.assertion_level(), 0);
    assert!(ctx.check_logic().is_err());
    // logic can be set again, and previous declarations are gone
    tc(&mut ctx, "(set-logic QF_BV)").unwrap();
    assert_eq!(ctx.get_logic(), "QF_BV");
    assert!(tc(&mut ctx, "(assert (= x x))").is_err());
    tc(
        &mut ctx,
        r#"
        (declare-const x (_ BitVec 4))
        (assert (= x #b0000))
    "#,
    )
    .unwrap();
}

#[test]
fn test_pop_datatypes() {
    let mut ctx = Context::new();
    tc(
        &mut ctx,
        r#"
        (set-logic ALL)
        (declare-datatype Color ((red) (green)))
        (push 1)
        (declare-datatype Shape ((circle (radius Int)) (square (side Int))))
        (declare-const s Shape)
        (assert ((_ is circle) s))
        (assert (> (radius s) 0))
        (assert ((_ is red) red))
    "#,
    )
    .unwrap();
    tc(&mut ctx, "(pop 1)").unwrap();
    // the testers of the surviving datatype are still there, the popped ones are gone
    tc(&mut ctx, "(assert ((_ is red) green))").unwrap();
    assert!(tc(&mut ctx, "(assert ((_ is circle) (circle 1)))").is_err());
    assert!(tc(&mut ctx, "(declare-const t Shape)").is_err());
    // and the popped datatype can be declared again
    tc(
        &mut ctx,
        r#"
        (declare-datatype Shape ((circle (radius Real))))
        (assert (> (radius (circle 1.0)) 0.0))
    "#,
    )
    .unwrap();
}

#[test]
fn test_pop_overloads() {
    let mut ctx = Context::new();
    tc(&mut ctx, "(set-logic ALL)").unwrap();
    let int = ctx.int_sort();
    let bool = ctx.bool_sort();
    ctx.extend_symbol("g", Sig::func(vec![int.clone()], int.clone()))
        .unwrap();
    let count = ctx.symbol_count();
    ctx.push_levels(1);
    // overload `g` from a lower level
    ctx.extend_symbol("g", Sig::func(vec![bool.clone()], int))
        .unwrap();
    assert_eq!(ctx.symbol_count(), count + 1);
    let g = ctx.allocate_symbol("g");
    assert_eq!(ctx.get_symbol_binding(&g).unwrap().len(), 2);
    tc(&mut ctx, "(assert (= (g true) (g 1)))").unwrap();
    ctx.pop_levels(1).unwrap();
    assert_eq!(ctx.symbol_count(), count);
    assert_eq!(ctx.get_symbol_binding(&g).unwrap().len(), 1);
    tc(&mut ctx, "(assert (= (g 2) 1))").unwrap();
    assert!(tc(&mut ctx, "(assert (= (g true) 1))").is_err());
}
