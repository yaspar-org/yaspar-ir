// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use dashu::integer::UBig;
use yaspar_ir::ast::gsubst::{GlobalSubstInplace, GlobalSubstPreproc};
use yaspar_ir::ast::subst::{Substitute, Substitution};
use yaspar_ir::ast::{Context, ObjectAllocatorExt, Typecheck, TypedApi};
use yaspar_ir::untyped::UntypedAst;

#[test]
fn test_substitutions() {
    let mut context = Context::new();
    context.ensure_logic();
    let one = context.numeral(UBig::from(1u8)).unwrap();

    let int = context.int_sort();
    let mut q_ctx = context
        .build_quantifier_with_domain([("x", int.clone()), ("y", int)])
        .unwrap();
    let t = UntypedAst
        .parse_term_str("(* x y 3)")
        .unwrap()
        .type_check(&mut q_ctx)
        .unwrap();
    let plus = UntypedAst
        .parse_term_str("(+ 1 2)")
        .unwrap()
        .type_check(&mut q_ctx)
        .unwrap();
    let subst = Substitution::new([("x", plus), ("z", one)], &mut q_ctx);
    let t = t.subst(&subst, &mut q_ctx);
    assert_eq!(t.to_string(), "(* (+ 1 2) y 3)");

    // more complex ones
    let t = UntypedAst
        .parse_term_str("(* x y 3 x)")
        .unwrap()
        .type_check(&mut q_ctx)
        .unwrap();
    let t = t.subst(&subst, &mut q_ctx);
    assert_eq!(t.to_string(), "(* (+ 1 2) y 3 (+ 1 2))");

    let t = UntypedAst
        .parse_term_str("(let ((z (div x 100))) (* z y 3 x))")
        .unwrap()
        .type_check(&mut q_ctx)
        .unwrap();
    let t = t.subst(&subst, &mut q_ctx);
    assert_eq!(
        t.to_string(),
        "(let ((z (div (+ 1 2) 100))) (* z y 3 (+ 1 2)))"
    );
}

#[test]
fn test_substitutions_shadow() {
    let mut context = Context::new();
    context.ensure_logic();

    let int = context.int_sort();
    let mut q_ctx = context
        .build_quantifier_with_domain([("x", int.clone()), ("y", int)])
        .unwrap();
    let plus = UntypedAst
        .parse_term_str("(+ 1 2)")
        .unwrap()
        .type_check(&mut q_ctx)
        .unwrap();
    let subst = Substitution::new([("x", plus)], &mut q_ctx);
    let t = UntypedAst
        .parse_term_str("(forall ((x Int)) (= x 10))")
        .unwrap()
        .type_check(&mut q_ctx)
        .unwrap();
    let nt = t.subst(&subst, &mut q_ctx);
    assert_eq!(nt, t);

    let t = UntypedAst
        .parse_term_str("(exists ((x Int)) (= x 10))")
        .unwrap()
        .type_check(&mut q_ctx)
        .unwrap();
    let nt = t.subst(&subst, &mut q_ctx);
    assert_eq!(nt, t);

    let t = UntypedAst
        .parse_term_str("(let ((x (* y 10))) (* x y 3))")
        .unwrap()
        .type_check(&mut q_ctx)
        .unwrap();
    let nt = t.subst(&subst, &mut q_ctx);
    assert_eq!(nt, t);

    let t = UntypedAst
        .parse_term_str("(xor (= x 5) (= y 10))")
        .unwrap()
        .type_check(&mut q_ctx)
        .unwrap();
    let nt = t.subst(&subst, &mut q_ctx);
    assert_eq!(nt.to_string(), "(xor (= (+ 1 2) 5) (= y 10))");
}

#[test]
fn test_global_substitutions() {
    let mut context = Context::new();
    context.ensure_logic();

    UntypedAst
        .parse_script_str(
            r#"
        (declare-const x Real)
        (define-fun y () Real (/ x 100.1))
        (define-fun max ((a Real) (b Real)) Real (ite (> a b) a b))
        (define-fun z () Real (max (* x y) y))
        (declare-datatype List (par (X) ( (nil) (cons (car X) (cdr (List X))) ) ))
        (define-fun-rec append ((l1 (List Real)) (l2 (List Real))) (List Real)
          (match l1 ((nil l2) ((cons a l1) (cons a (append l1 l2))))))
        "#,
        )
        .unwrap()
        .type_check(&mut context)
        .unwrap();

    // preproc
    let z = context.typed_symbol("z").unwrap();
    let nz = z.gsubst_preproc(["y"], &mut context);
    assert_eq!(nz.to_string(), "z");
    let nz = z.gsubst_preproc(["z", "max"], &mut context);
    assert_eq!(nz.to_string(), "(ite (> (* x y) y) (* x y) y)");
    let nz = z.gsubst_preproc(["z", "max", "y"], &mut context);
    assert_eq!(
        nz.to_string(),
        "(ite (> (* x (/ x 100.1)) (/ x 100.1)) (* x (/ x 100.1)) (/ x 100.1))"
    );
    let all = context.all_defined_symbols();
    let nz = z.gsubst_preproc(&all, &mut context);
    assert_eq!(
        nz.to_string(),
        "(ite (> (* x (/ x 100.1)) (/ x 100.1)) (* x (/ x 100.1)) (/ x 100.1))"
    );

    let real_list = UntypedAst
        .parse_sort_str("(List Real)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    let nil = context.typed_symbol_with_sort("nil", real_list).unwrap();
    let app = context
        .typed_simp_app("append", [nil.clone(), nil.clone()])
        .unwrap();
    let napp = app.gsubst_preproc(["append"], &mut context);
    assert_eq!(
        napp.to_string(),
        "(match (as nil (List Real)) ((nil (as nil (List Real))) ((cons a l1) (cons a (append l1 (as nil (List Real)))))))"
    );

    // inplace
    let z = context.typed_symbol("z").unwrap();
    let nz = z.gsubst_inplace(["y"], &mut context);
    assert_eq!(nz.to_string(), "z");
    let nz = z.gsubst_inplace(["z", "max"], &mut context);
    assert_eq!(nz.to_string(), "(ite (> (* x y) y) (* x y) y)");
    let nz = z.gsubst_inplace(["z", "max", "y"], &mut context);
    assert_eq!(
        nz.to_string(),
        "(ite (> (* x (/ x 100.1)) (/ x 100.1)) (* x (/ x 100.1)) (/ x 100.1))"
    );
    let all = context.all_defined_symbols();
    let nz = z.gsubst_inplace(&all, &mut context);
    assert_eq!(
        nz.to_string(),
        "(ite (> (* x (/ x 100.1)) (/ x 100.1)) (* x (/ x 100.1)) (/ x 100.1))"
    );

    let real_list = UntypedAst
        .parse_sort_str("(List Real)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    let nil = context.typed_symbol_with_sort("nil", real_list).unwrap();
    let app = context
        .typed_simp_app("append", [nil.clone(), nil.clone()])
        .unwrap();
    let napp = app.gsubst_inplace(["append"], &mut context);
    assert_eq!(
        napp.to_string(),
        "(match (as nil (List Real)) ((nil (as nil (List Real))) ((cons a l1) (cons a (append l1 (as nil (List Real)))))))"
    );
}
