// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use dashu::integer::UBig;
use std::collections::HashSet;
use yaspar_ir::ast::fv::FreeLocalVars;
use yaspar_ir::ast::{
    CheckedApi, Context, ObjectAllocatorExt, ScopedSortApi, StrAllocator, Typecheck,
};
use yaspar_ir::traits::Repr;
use yaspar_ir::untyped::UntypedAst;

#[test]
fn test_quantifiers() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-const x Int)
        (assert (forall ((y Int)) (= x y)))
        (assert (exists ((z Int)) (> z 0)))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    if let yaspar_ir::ast::ACommand::Assert(t) = cmds[2].repr() {
        let fv = t.free_loc_vars();
        assert_eq!(fv, HashSet::new());
    }

    if let yaspar_ir::ast::ACommand::Assert(t) = cmds[3].repr() {
        let fv = t.free_loc_vars();
        assert_eq!(fv, HashSet::new());
    }
}

#[test]
fn test_let_bindings() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (assert (let ((x 1) (y 2)) (= (+ x y) 3)))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    if let yaspar_ir::ast::ACommand::Assert(t) = cmds[1].repr() {
        let fv = t.free_loc_vars();
        assert_eq!(fv, HashSet::new());
    }
}

#[test]
fn test_nested_quantifiers() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (assert (forall ((x Int)) (exists ((y Int)) (= x y))))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    if let yaspar_ir::ast::ACommand::Assert(t) = cmds[1].repr() {
        let fv = t.free_loc_vars();
        assert_eq!(fv, HashSet::new());
    }
}

#[test]
fn test_free_vars_in_quantifier() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-const y Int)
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let int = ctx.int_sort();
    let mut q_ctx = ctx.build_quantifier_with_domain([("x", int)]).unwrap();
    let t = UntypedAst
        .parse_term_str("(= x y)")
        .unwrap()
        .type_check(&mut q_ctx)
        .unwrap();
    let forall = q_ctx.typed_forall(t).unwrap();

    let fv = forall.free_loc_vars();
    assert_eq!(fv, HashSet::new());
}

#[test]
fn test_free_vars_in_let() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-const w Int)
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let int = ctx.int_sort();
    let mut q_ctx = ctx
        .build_quantifier_with_domain([("x", int.clone()), ("y", int)])
        .unwrap();
    let x = q_ctx.typed_symbol("x").unwrap();
    let mut l_ctx = q_ctx.build_let([("z", x)]).unwrap();
    let t = UntypedAst
        .parse_term_str("(= z (+ y w))")
        .unwrap()
        .type_check(&mut l_ctx)
        .unwrap();
    let let_term = l_ctx.typed_let(t);

    let fv = let_term.free_loc_vars();
    let y_sym = ctx.allocate_symbol("y");
    assert_eq!(fv, HashSet::from([y_sym]));
}

#[test]
fn test_two_free_vars() {
    let mut ctx = Context::new();
    ctx.ensure_logic();
    let int = ctx.int_sort();
    let mut outer_ctx = ctx
        .build_quantifier_with_domain([("a", int.clone()), ("b", int.clone())])
        .unwrap();
    let mut inner_ctx = outer_ctx
        .build_quantifier_with_domain([("x", int)])
        .unwrap();
    let t = UntypedAst
        .parse_term_str("(= (+ x a) b)")
        .unwrap()
        .type_check(&mut inner_ctx)
        .unwrap();
    let forall_t = inner_ctx.typed_forall(t).unwrap();

    let fv = forall_t.free_loc_vars();
    let a_sym = ctx.allocate_symbol("a");
    let b_sym = ctx.allocate_symbol("b");
    assert_eq!(fv, HashSet::from([a_sym, b_sym]));
}

#[test]
fn test_three_free_vars() {
    let mut ctx = Context::new();
    ctx.ensure_logic();
    let int = ctx.int_sort();
    let mut outer_ctx = ctx
        .build_quantifier_with_domain([("a", int.clone()), ("b", int.clone()), ("c", int.clone())])
        .unwrap();
    let mut inner_ctx = outer_ctx
        .build_quantifier_with_domain([("x", int)])
        .unwrap();
    let t = UntypedAst
        .parse_term_str("(= (+ x a) (* b c))")
        .unwrap()
        .type_check(&mut inner_ctx)
        .unwrap();
    let forall_t = inner_ctx.typed_forall(t).unwrap();

    let fv = forall_t.free_loc_vars();
    let a_sym = ctx.allocate_symbol("a");
    let b_sym = ctx.allocate_symbol("b");
    let c_sym = ctx.allocate_symbol("c");
    assert_eq!(fv, HashSet::from([a_sym, b_sym, c_sym]));
}

#[test]
fn test_free_vars_distinct() {
    let mut ctx = Context::new();
    ctx.ensure_logic();
    let int = ctx.int_sort();
    let mut outer_ctx = ctx
        .build_quantifier_with_domain([("a", int.clone()), ("b", int.clone())])
        .unwrap();
    let mut inner_ctx = outer_ctx
        .build_quantifier_with_domain([("x", int.clone()), ("y", int)])
        .unwrap();
    let t = UntypedAst
        .parse_term_str("(distinct x a b)")
        .unwrap()
        .type_check(&mut inner_ctx)
        .unwrap();
    let forall = inner_ctx.typed_forall(t).unwrap();

    let fv = forall.free_loc_vars();
    let a_sym = ctx.allocate_symbol("a");
    let b_sym = ctx.allocate_symbol("b");
    assert_eq!(fv, HashSet::from([a_sym, b_sym]));
}

#[test]
fn test_free_vars_and_or_xor() {
    let mut ctx = Context::new();
    ctx.ensure_logic();
    let bool = ctx.bool_sort();
    let a_sym = ctx.allocate_symbol("a");
    let b_sym = ctx.allocate_symbol("b");
    let mut outer_ctx = ctx
        .build_quantifier_with_domain([("a", bool.clone()), ("b", bool.clone())])
        .unwrap();
    let mut inner_ctx = outer_ctx
        .build_quantifier_with_domain([("p", bool.clone())])
        .unwrap();

    let t_and = UntypedAst
        .parse_term_str("(and p a b)")
        .unwrap()
        .type_check(&mut inner_ctx)
        .unwrap();
    let forall_and = inner_ctx.typed_forall(t_and).unwrap();
    let fv = forall_and.free_loc_vars();
    assert_eq!(fv, HashSet::from([a_sym.clone(), b_sym.clone()]));

    let mut inner_ctx2 = outer_ctx
        .build_quantifier_with_domain([("p", bool.clone())])
        .unwrap();
    let t_or = UntypedAst
        .parse_term_str("(or p a)")
        .unwrap()
        .type_check(&mut inner_ctx2)
        .unwrap();
    let forall_or = inner_ctx2.typed_forall(t_or).unwrap();
    let fv = forall_or.free_loc_vars();
    assert_eq!(fv, HashSet::from([a_sym.clone()]));

    let mut inner_ctx3 = outer_ctx
        .build_quantifier_with_domain([("p", bool)])
        .unwrap();
    let t_xor = UntypedAst
        .parse_term_str("(xor p b)")
        .unwrap()
        .type_check(&mut inner_ctx3)
        .unwrap();
    let forall_xor = inner_ctx3.typed_forall(t_xor).unwrap();
    let fv = forall_xor.free_loc_vars();
    assert_eq!(fv, HashSet::from([b_sym]));
}

#[test]
fn test_free_vars_not() {
    let mut ctx = Context::new();
    ctx.ensure_logic();
    let bool = ctx.bool_sort();
    let a_sym = ctx.allocate_symbol("a");
    let mut outer_ctx = ctx
        .build_quantifier_with_domain([("a", bool.clone())])
        .unwrap();
    let mut inner_ctx = outer_ctx
        .build_quantifier_with_domain([("p", bool)])
        .unwrap();
    let t = UntypedAst
        .parse_term_str("(not a)")
        .unwrap()
        .type_check(&mut inner_ctx)
        .unwrap();
    let forall = inner_ctx.typed_forall(t).unwrap();

    let fv = forall.free_loc_vars();
    assert_eq!(fv, HashSet::from([a_sym]));
}

#[test]
fn test_free_vars_implies() {
    let mut ctx = Context::new();
    ctx.ensure_logic();
    let bool = ctx.bool_sort();
    let a_sym = ctx.allocate_symbol("a");
    let b_sym = ctx.allocate_symbol("b");
    let mut outer_ctx = ctx
        .build_quantifier_with_domain([("a", bool.clone()), ("b", bool.clone())])
        .unwrap();
    let mut inner_ctx = outer_ctx
        .build_quantifier_with_domain([("p", bool)])
        .unwrap();
    let t = UntypedAst
        .parse_term_str("(=> a b p)")
        .unwrap()
        .type_check(&mut inner_ctx)
        .unwrap();
    let forall = inner_ctx.typed_forall(t).unwrap();

    let fv = forall.free_loc_vars();
    assert_eq!(fv, HashSet::from([a_sym, b_sym]));
}

#[test]
fn test_free_vars_ite() {
    let mut ctx = Context::new();
    ctx.ensure_logic();
    let int = ctx.int_sort();
    let bool = ctx.bool_sort();
    let a_sym = ctx.allocate_symbol("a");
    let b_sym = ctx.allocate_symbol("b");
    let mut outer_ctx = ctx
        .build_quantifier_with_domain([("a", bool), ("b", int.clone())])
        .unwrap();
    let mut inner_ctx = outer_ctx
        .build_quantifier_with_domain([("x", int)])
        .unwrap();
    let t = UntypedAst
        .parse_term_str("(= (ite a x b) 0)")
        .unwrap()
        .type_check(&mut inner_ctx)
        .unwrap();
    let forall = inner_ctx.typed_forall(t).unwrap();

    let fv = forall.free_loc_vars();
    assert_eq!(fv, HashSet::from([a_sym, b_sym]));
}

#[test]
fn test_free_vars_match() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-datatype List (par (X) ((nil) (cons (car X) (cdr (List X))))))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let int = ctx.int_sort();
    let list_int = ctx.wf_sort_n("List", [int]).unwrap();
    let a_sym = ctx.allocate_symbol("a");
    let b_sym = ctx.allocate_symbol("b");
    let mut outer_ctx = ctx
        .build_quantifier_with_domain([("a", list_int.clone()), ("b", list_int.clone())])
        .unwrap();
    let mut inner_ctx = outer_ctx
        .build_quantifier_with_domain([("l", list_int)])
        .unwrap();
    let t = UntypedAst
        .parse_term_str("(= (match l ((nil a) ((cons h t) b))) l)")
        .unwrap()
        .type_check(&mut inner_ctx)
        .unwrap();
    let forall = inner_ctx.typed_forall(t).unwrap();

    let fv = forall.free_loc_vars();
    assert_eq!(fv, HashSet::from([a_sym, b_sym]));
}

#[test]
fn test_is_closed() {
    let mut ctx = Context::new();
    ctx.ensure_logic();

    let int = ctx.int_sort();
    let mut q_ctx = ctx
        .build_quantifier_with_domain([("x", int.clone())])
        .unwrap();
    let x = q_ctx.typed_symbol("x").unwrap();
    let one = q_ctx.numeral(UBig::from(1u8)).unwrap();
    let eq = q_ctx.typed_eq(x, one).unwrap();
    let forall = q_ctx.typed_forall(eq).unwrap();

    assert!(yaspar_ir::ast::fv::is_closed(&forall));

    let mut outer_ctx = ctx
        .build_quantifier_with_domain([("a", int.clone())])
        .unwrap();
    let mut inner_ctx = outer_ctx
        .build_quantifier_with_domain([("y", int)])
        .unwrap();
    let t_open = UntypedAst
        .parse_term_str("(= a 1)")
        .unwrap()
        .type_check(&mut inner_ctx)
        .unwrap();
    assert!(!yaspar_ir::ast::fv::is_closed(&t_open));
}
