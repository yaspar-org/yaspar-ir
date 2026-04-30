// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use dashu::integer::UBig;
use yaspar_ir::ast::{
    CheckedApi, Context, GlobalSubst, LetElim, Local, LocalVarAllocator, ObjectAllocatorExt,
    StrAllocator, SubstituteV2, SubstitutionV2, Typecheck,
};
use yaspar_ir::untyped::UntypedAst;

#[test]
fn test_substitutions() {
    let mut context = Context::new();
    context.ensure_logic();
    let one = context.numeral(UBig::from(1u8)).unwrap();

    let int = context.int_sort();
    let mut q_ctx = context
        .build_quantifier_with_domain([("x", int.clone()), ("y", int.clone())])
        .unwrap();
    let bindings = q_ctx.get_direct_bindings();
    let x_local = bindings[0].clone().into();

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
    let mut subst = SubstitutionV2::new([(x_local, plus)]);
    let z_sym = q_ctx.allocate_symbol("z");
    let z_id = q_ctx.new_local(); // a non-existent local id
    let loc = Local {
        id: z_id,
        symbol: z_sym,
        sort: int.clone(),
    };
    subst.push(loc, one);
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
    let x_local = q_ctx.get_direct_bindings()[0].clone().into();

    let plus = UntypedAst
        .parse_term_str("(+ 1 2)")
        .unwrap()
        .type_check(&mut q_ctx)
        .unwrap();
    let subst = SubstitutionV2::new([(x_local, plus)]);
    let t = UntypedAst
        .parse_term_str("(forall ((x Int)) (= x 10))")
        .unwrap()
        .type_check(&mut q_ctx)
        .unwrap();
    let nt = t.subst(&subst, &mut q_ctx);
    // v2 substituter reassigns id for bound variables, so compare by string
    assert_eq!(nt.to_string(), t.to_string());

    let t = UntypedAst
        .parse_term_str("(exists ((x Int)) (= x 10))")
        .unwrap()
        .type_check(&mut q_ctx)
        .unwrap();
    let nt = t.subst(&subst, &mut q_ctx);
    assert_eq!(nt.to_string(), t.to_string());

    let t = UntypedAst
        .parse_term_str("(let ((x (* y 10))) (* x y 3))")
        .unwrap()
        .type_check(&mut q_ctx)
        .unwrap();
    let nt = t.subst(&subst, &mut q_ctx);
    assert_eq!(nt.to_string(), t.to_string());

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

    let z = context.typed_symbol("z").unwrap();
    let nz = z.gsubst(["y"], &mut context);
    assert_eq!(nz.to_string(), "z");
    let nz = z.gsubst(["z", "max"], &mut context);
    assert_eq!(nz.to_string(), "(ite (> (* x y) y) (* x y) y)");
    let nz = z.gsubst(["z", "max", "y"], &mut context);
    assert_eq!(
        nz.to_string(),
        "(ite (> (* x (/ x 100.1)) (/ x 100.1)) (* x (/ x 100.1)) (/ x 100.1))"
    );
    let all = context.defined_symbols();
    let nz = z.gsubst(&all, &mut context);
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
    let napp = app.gsubst(["append"], &mut context);
    assert_eq!(
        napp.to_string(),
        "(match (as nil (List Real)) ((nil (as nil (List Real))) ((cons a l1) (cons a (append l1 (as nil (List Real)))))))"
    );
}

#[test]
fn test_gsubst_define_fun() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (define-fun double ((x Int)) Int (+ x x))
        (declare-const y Int)
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let y = ctx.typed_symbol("y").unwrap();
    let double_y = ctx.typed_simp_app("double", [y]).unwrap();

    let expanded_inplace = double_y.gsubst(["double"], &mut ctx);
    assert_eq!(expanded_inplace.to_string(), "(+ y y)");
}

#[test]
fn test_gsubst_multiple_definitions() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (define-fun inc ((x Int)) Int (+ x 1))
        (define-fun dec ((x Int)) Int (- x 1))
        (declare-const z Int)
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let z = ctx.typed_symbol("z").unwrap();
    let dec_z = ctx.typed_simp_app("dec", [z.clone()]).unwrap();
    let inc_dec_z = ctx.typed_simp_app("inc", [dec_z]).unwrap();

    let expanded_inplace = inc_dec_z.gsubst(["inc", "dec"], &mut ctx);
    assert_eq!(expanded_inplace.to_string(), "(+ (- z 1) 1)");
}

#[test]
fn test_gsubst_nested_definitions() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (define-fun square ((x Int)) Int (* x x))
        (define-fun quad ((x Int)) Int (square (square x)))
        (declare-const a Int)
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let a = ctx.typed_symbol("a").unwrap();
    let quad_a = ctx.typed_simp_app("quad", [a]).unwrap();

    let expanded_inplace = quad_a.gsubst(["quad", "square"], &mut ctx);
    assert_eq!(expanded_inplace.to_string(), "(* (* a a) (* a a))");
}

#[test]
fn test_gsubst_with_quantifier() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (define-fun double ((x Int)) Int (+ x x))
        (declare-const y Int)
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let int = ctx.int_sort();
    let mut q_ctx = ctx.build_quantifier_with_domain([("z", int)]).unwrap();
    let z = q_ctx.typed_symbol("z").unwrap();
    let y = q_ctx.typed_symbol("y").unwrap();
    let double_z = q_ctx.typed_simp_app("double", [z]).unwrap();
    let eq = q_ctx.typed_eq(double_z, y).unwrap();
    let forall = q_ctx.typed_forall(eq).unwrap();

    assert_eq!(forall.to_string(), "(forall ((z Int)) (= (double z) y))");

    let expanded_inplace = forall.gsubst(["double"], &mut ctx);
    assert_eq!(
        expanded_inplace.to_string(),
        "(forall ((z Int)) (= (+ z z) y))"
    );
}

#[test]
fn test_gsubst_with_let() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (define-fun inc ((x Int)) Int (+ x 1))
        (declare-const a Int)
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let a = ctx.typed_symbol("a").unwrap();
    let inc_a = ctx.typed_simp_app("inc", [a]).unwrap();
    let mut l_ctx = ctx.build_let([("b", inc_a)]).unwrap();
    let b = l_ctx.typed_symbol("b").unwrap();
    let inc_b = l_ctx.typed_simp_app("inc", [b]).unwrap();
    let let_term = l_ctx.typed_let(inc_b);

    assert_eq!(let_term.to_string(), "(let ((b (inc a))) (inc b))");

    let expanded_inplace = let_term.gsubst(["inc"], &mut ctx);
    assert_eq!(expanded_inplace.to_string(), "(let ((b (+ a 1))) (+ b 1))");
}

#[test]
fn test_gsubst_nested_binders() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (define-fun square ((x Int)) Int (* x x))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let int = ctx.int_sort();
    let mut q_ctx = ctx.build_quantifier_with_domain([("x", int)]).unwrap();
    let x = q_ctx.typed_symbol("x").unwrap();
    let square_x = q_ctx.typed_simp_app("square", [x.clone()]).unwrap();
    let mut l_ctx = q_ctx.build_let([("y", square_x)]).unwrap();
    let y = l_ctx.typed_symbol("y").unwrap();
    let square_y = l_ctx.typed_simp_app("square", [y]).unwrap();
    let eq = l_ctx.typed_eq(square_y, x).unwrap();
    let let_term = l_ctx.typed_let(eq);
    let exists = q_ctx.typed_exists(let_term).unwrap();

    assert_eq!(
        exists.to_string(),
        "(exists ((x Int)) (let ((y (square x))) (= (square y) x)))"
    );

    let expanded_inplace = exists.gsubst(["square"], &mut ctx);
    assert_eq!(
        expanded_inplace.to_string(),
        "(exists ((x Int)) (let ((y (* x x))) (= (* y y) x)))"
    );
}

#[test]
fn test_gsubst_shadowing_in_quantifier() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (define-fun f ((x Int)) Int (+ x 1))
        (declare-const y Int)
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let int = ctx.int_sort();
    let mut q_ctx = ctx.build_quantifier_with_domain([("x", int)]).unwrap();
    let x = q_ctx.typed_symbol("x").unwrap();
    let y = q_ctx.typed_symbol("y").unwrap();
    let f_x = q_ctx.typed_simp_app("f", [x]).unwrap();
    let eq = q_ctx.typed_eq(f_x, y).unwrap();
    let forall = q_ctx.typed_forall(eq).unwrap();

    assert_eq!(forall.to_string(), "(forall ((x Int)) (= (f x) y))");
    let expanded = forall.gsubst(["f"], &mut ctx);
    assert_eq!(expanded.to_string(), "(forall ((x Int)) (= (+ x 1) y))");
}

#[test]
fn test_gsubst_shadowing_in_let() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (define-fun g ((y Int)) Int (* y 2))
        (declare-const y Int)
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let y = ctx.typed_symbol("y").unwrap();
    let g_y = ctx.typed_simp_app("g", [y.clone()]).unwrap();
    let mut l_ctx = ctx.build_let([("y", g_y)]).unwrap();
    let y_local = l_ctx.typed_symbol("y").unwrap();
    let g_y_local = l_ctx.typed_simp_app("g", [y_local]).unwrap();
    let let_term = l_ctx.typed_let(g_y_local);

    assert_eq!(let_term.to_string(), "(let ((y (g y))) (g y))");
    let expanded = let_term.gsubst(["g"], &mut ctx);
    assert_eq!(expanded.to_string(), "(let ((y (* y 2))) (* y 2))");

    assert_eq!(
        let_term.let_elim(&mut ctx).gsubst(["g"], &mut ctx),
        expanded.let_elim(&mut ctx)
    );
}

#[test]
fn test_gsubst_nested_shadowing() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (define-fun h ((z Int)) Int (- z 1))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let int = ctx.int_sort();
    let mut outer_q = ctx
        .build_quantifier_with_domain([("z", int.clone())])
        .unwrap();
    let z_outer = outer_q.typed_symbol("z").unwrap();
    let mut inner_q = outer_q.build_quantifier_with_domain([("z", int)]).unwrap();
    let z_inner = inner_q.typed_symbol("z").unwrap();
    let h_z = inner_q.typed_simp_app("h", [z_inner]).unwrap();
    let eq = inner_q.typed_eq(h_z, z_outer).unwrap();
    let exists = inner_q.typed_exists(eq).unwrap();
    let forall = outer_q.typed_forall(exists).unwrap();

    assert_eq!(
        forall.to_string(),
        "(forall ((z Int)) (exists ((z Int)) (= (h z) z)))"
    );
    let expanded = forall.gsubst(["h"], &mut ctx);
    assert_eq!(
        expanded.to_string(),
        "(forall ((z Int)) (exists ((z Int)) (= (- z 1) z)))"
    );
}

#[test]
fn test_gsubst_datatype_tester() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-datatype List (par (X) ((nil) (cons (car X) (cdr (List X))))))
        (declare-const l (List Int))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let l = ctx.typed_symbol("l").unwrap();
    let is_nil = ctx.typed_simp_app("is-nil", [l.clone()]).unwrap();

    let expanded_inplace = is_nil.gsubst(["is-nil"], &mut ctx);
    assert_eq!(expanded_inplace.to_string(), "((_ is nil) l)");
    expanded_inplace.type_check(&mut ctx).unwrap();
}

#[test]
fn test_gsubst_datatype_tester_in_formula() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-datatype List (par (X) ((nil) (cons (car X) (cdr (List X))))))
        (declare-const l (List Real))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let l = ctx.typed_symbol("l").unwrap();
    let is_nil = ctx.typed_simp_app("is-nil", [l.clone()]).unwrap();
    let is_cons = ctx.typed_simp_app("is-cons", [l.clone()]).unwrap();
    let formula = ctx.typed_or([is_nil, is_cons]).unwrap();

    let expanded_inplace = formula.gsubst(["is-nil", "is-cons"], &mut ctx);
    assert_eq!(
        expanded_inplace.to_string(),
        "(or ((_ is nil) l) ((_ is cons) l))"
    );
    expanded_inplace.type_check(&mut ctx).unwrap();
}

#[test]
fn test_gsubst_datatype_tester_with_quantifier() {
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

    let list_int = UntypedAst
        .parse_sort_str("(List Int)")
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let mut q_ctx = ctx.build_quantifier_with_domain([("x", list_int)]).unwrap();
    let x = q_ctx.typed_symbol("x").unwrap();
    let is_nil = q_ctx.typed_simp_app("is-nil", [x]).unwrap();
    let forall = q_ctx.typed_forall(is_nil).unwrap();

    assert_eq!(forall.to_string(), "(forall ((x (List Int))) (is-nil x))");
    let expanded_inplace = forall.gsubst(["is-nil"], &mut ctx);
    assert_eq!(
        expanded_inplace.to_string(),
        "(forall ((x (List Int))) ((_ is nil) x))"
    );
    expanded_inplace.type_check(&mut ctx).unwrap();
}

#[test]
fn test_gsubst_multiple_datatype_testers() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-datatype Option (par (T) ((none) (some (value T)))))
        (declare-const opt (Option Bool))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let opt = ctx.typed_symbol("opt").unwrap();
    let is_none = ctx.typed_simp_app("is-none", [opt.clone()]).unwrap();
    let is_some = ctx.typed_simp_app("is-some", [opt.clone()]).unwrap();
    let xor = ctx.typed_xor([is_none, is_some]).unwrap();

    let expanded_inplace = xor.gsubst(["is-none", "is-some"], &mut ctx);
    assert_eq!(
        expanded_inplace.to_string(),
        "(xor ((_ is none) opt) ((_ is some) opt))"
    );
    expanded_inplace.type_check(&mut ctx).unwrap();
}
