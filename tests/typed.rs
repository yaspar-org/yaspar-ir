// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use dashu::integer::{IBig, UBig};
use yaspar_ir::ast::alg::QualifiedIdentifier;
use yaspar_ir::ast::{
    Context, FetchSort, ObjectAllocatorExt, ScopedSortApi, SortAllocator, StrAllocator, Typecheck,
    TypedApi,
};
use yaspar_ir::untyped::UntypedAst;

#[test]
fn test_typed_apis() {
    let mut context = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-const foo (Array Int Real))
    "#,
        )
        .unwrap()
        .type_check(&mut context)
        .unwrap();

    let select = context.allocate_symbol("select");
    let int_sort = context.int_sort();
    let real_sort = context.real_sort();
    let array_sort = context.array_sort(int_sort, real_sort.clone());
    let foo_var = context.typed_symbol("foo").unwrap();
    assert_eq!(foo_var.get_sort(&mut context), array_sort);
    let one = context.integer(IBig::from(1)).unwrap();
    // typed_app properly maintains and returns type information.
    let select_foo = context
        .typed_app(
            QualifiedIdentifier::simple(select.clone()),
            vec![foo_var.clone(), one.clone()],
        )
        .unwrap();
    assert_eq!(select_foo.get_sort(&mut context), real_sort);

    // error because "bar" is not a declared symbol
    assert!(context.typed_symbol("bar").is_err());
    // select is a function symbol, so it cannot be used as a variable
    assert!(context.typed_symbol("select").is_err());
    // also fail for monomorphic str.len
    assert!(context.typed_symbol("str.len").is_err());
    // same for overloaded symbols
    assert!(context.typed_symbol("-").is_err());

    // now we insert `nil` as a polymorphic symbol
    UntypedAst
        .parse_command_str(
            "(declare-datatype List (par (X) ( (nil) (cons (car X) (cdr (List X))) ) ))",
        )
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    // won't work; `nil` itself cannot concretize `X`
    assert!(context.typed_symbol("nil").is_err());
    let int_sort = context.int_sort();
    let list = context.allocate_symbol("List");
    let int_list = context.sort_n(list, vec![int_sort]);
    // however, if we specify the sort of nil, then we are good.
    let nil = context
        .typed_symbol_with_sort("nil", int_list.clone())
        .unwrap();
    assert_eq!(nil.get_sort(&mut context), int_list.clone());

    // works for datatype constructors as well
    let singleton_one = context
        .typed_simp_app("cons", vec![one.clone(), nil])
        .unwrap();
    assert_eq!(singleton_one.get_sort(&mut context), int_list);

    // context.app would have trusted developers and passed the following:
    let select_foo_bad = context.typed_app(QualifiedIdentifier::simple(select), vec![foo_var]);
    assert!(select_foo_bad.is_err());
}

#[test]
fn test_more_typed_apis() {
    let mut context = Context::new();
    context.ensure_logic();

    //from test_comparison
    let int = context.int_sort();
    let mut q_context = context
        .build_quantifier_with_domain([("m", int.clone()), ("n", int.clone())])
        .unwrap();
    let t1 = UntypedAst
        .parse_term_str("(<= 0 m n)")
        .unwrap()
        .type_check(&mut q_context)
        .unwrap();
    let t2 = UntypedAst
        .parse_term_str("(< 0 m n)")
        .unwrap()
        .type_check(&mut q_context)
        .unwrap();
    let t3 = UntypedAst
        .parse_term_str("(>= 0 m n)")
        .unwrap()
        .type_check(&mut q_context)
        .unwrap();
    let t4 = UntypedAst
        .parse_term_str("(> 0 m n)")
        .unwrap()
        .type_check(&mut q_context)
        .unwrap();
    let t_and = q_context.typed_and([t1.clone(), t2.clone()]).unwrap();
    assert_eq!(t_and.to_string(), "(and (<= 0 m n) (< 0 m n))");
    let t_or = q_context.typed_or([t3.clone(), t4.clone()]).unwrap();
    assert_eq!(t_or.to_string(), "(or (>= 0 m n) (> 0 m n))");
    let t_xor = q_context.typed_xor([t2, t4]).unwrap();
    assert_eq!(t_xor.to_string(), "(xor (< 0 m n) (> 0 m n))");

    // negative tests
    assert!(q_context.typed_and([]).is_err());
    let one = q_context.numeral(UBig::from(1u8)).unwrap();
    assert!(q_context.typed_and([t1, one.clone()]).is_err());
    assert!(q_context.typed_or([]).is_err());
    assert!(q_context.typed_or([t3, one.clone()]).is_err());
    assert!(q_context.typed_xor([]).is_err());
    assert!(q_context.typed_xor([one.clone()]).is_err());

    let t = q_context
        .typed_distinct([t_and.clone(), t_or.clone()])
        .unwrap();
    assert_eq!(
        t.to_string(),
        "(distinct (and (<= 0 m n) (< 0 m n)) (or (>= 0 m n) (> 0 m n)))"
    );

    // negative tests
    assert!(q_context.typed_distinct([]).is_err());
    assert!(q_context.typed_distinct([one.clone()]).is_err());

    let tr = q_context.bool(true);
    let ite = q_context
        .typed_ite(tr.clone(), t_and.clone(), t_or)
        .unwrap();
    assert_eq!(
        ite.to_string(),
        "(ite true (and (<= 0 m n) (< 0 m n)) (or (>= 0 m n) (> 0 m n)))"
    );

    // negative tests
    assert!(q_context.typed_ite(tr.clone(), one, t_and).is_err());
}

#[test]
fn test_typed_quantifiers() {
    let mut context = Context::new();
    context.ensure_logic();

    let mut q_context = context.build_quantifier().unwrap();
    let int_sort = q_context.int_sort();

    // insert x: Int and y: Int to the local context
    q_context
        .extend("x", int_sort.clone())
        .unwrap()
        .extend("y", int_sort.clone())
        .unwrap();

    // t can be built either in the hard way or using the parser and then type-checking in the local context
    let t = UntypedAst
        .parse_term_str("(=> (>    x y) (>   (+ x 1) (+   1 y)))")
        .unwrap()
        .type_check(&mut q_context)
        .unwrap();
    // wrap up the construction to obtain a quantified term
    let t1 = q_context.typed_forall(t).unwrap();
    assert_eq!(
        t1.to_string(),
        "(forall ((x Int) (y Int)) (=> (> x y) (> (+ x 1) (+ 1 y))))"
    );

    // start a new one
    let mut q_context = context.build_quantifier().unwrap();
    let int_sort = q_context.int_sort();
    q_context
        .extend("x", int_sort.clone())
        .unwrap()
        .extend("y", int_sort.clone())
        .unwrap();
    let t = UntypedAst
        .parse_term_str("(=     (* 10 x)     y)")
        .unwrap()
        .type_check(&mut q_context)
        .unwrap();
    // wrap up an existential term this time
    let t2 = q_context.typed_exists(t).unwrap();
    assert_eq!(t2.to_string(), "(exists ((x Int) (y Int)) (= (* 10 x) y))");

    // boolean terms can be compared
    let t = context.typed_eq(t2, t1).unwrap();
    assert_eq!(
        t.to_string(),
        "(= (exists ((x Int) (y Int)) (= (* 10 x) y)) (forall ((x Int) (y Int)) (=> (> x y) (> (+ x 1) (+ 1 y)))))"
    );

    let mut q_context = context.build_quantifier().unwrap();
    let bool_sort = q_context.bool_sort();
    q_context.extend("p", bool_sort.clone()).unwrap();
    q_context.extend("q", bool_sort).unwrap();
    let p = q_context.typed_symbol("p").unwrap();
    let q = q_context.typed_symbol("q").unwrap();
    let xor = q_context.typed_xor([p, q]).unwrap();
    let forall_xor = q_context.typed_forall(xor).unwrap();
    assert_eq!(
        forall_xor.to_string(),
        "(forall ((p Bool) (q Bool)) (xor p q))"
    );
}

#[test]
fn test_typed_quantifiers_bad() {
    let mut context = Context::new();
    context.ensure_logic();

    let mut q_context = context.build_quantifier().unwrap();
    let int_sort = q_context.int_sort();

    // insert x: Int and y: Int to the local context
    q_context
        .extend("x", int_sort.clone())
        .unwrap()
        .extend("y", int_sort.clone())
        .unwrap();
    // reject duplicated names
    assert!(q_context.extend("x", int_sort.clone()).is_err());
    // z is an unbound symbol
    assert!(
        UntypedAst
            .parse_term_str("z")
            .unwrap()
            .type_check(&mut q_context)
            .is_err()
    );
}

/// example taken from mlkem
#[test]
fn test_typed_let_bindings() {
    let mut context = Context::new();
    context.ensure_logic();
    UntypedAst
        .parse_script_str(
            r#"(declare-sort t 0)

        ;; "in_range"
        (define-fun in_range ((x (_ BitVec 16))) Bool
          (and (bvule #x0000 x) (bvule x #x0D00)))

        ;; "to_rep"
        (declare-fun to_rep (t) (_ BitVec 16))

        ;; "of_rep"
        (declare-fun of_rep ((_ BitVec 16)) t)"#,
        )
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    let mut q_context = context.build_quantifier().unwrap();
    let bv16 = q_context.bv_sort(UBig::from(16u8));
    q_context.extend("x", bv16).unwrap();
    let y_t = UntypedAst
        .parse_term_str("(bvurem x #x0D01)")
        .unwrap()
        .type_check(&mut q_context)
        .unwrap();
    // reject duplicated names
    assert!(
        q_context
            .build_let(vec![("y", y_t.clone()), ("y", y_t.clone())])
            .is_err()
    );
    let mut l_context = q_context.build_let(vec![("y", y_t)]).unwrap();
    let body = UntypedAst
        .parse_term_str("(=> (in_range y) (= (to_rep (of_rep x)) y))")
        .unwrap()
        .type_check(&mut l_context)
        .unwrap();
    let let_exp = l_context.typed_let(body);
    let t = q_context.typed_forall(let_exp).unwrap();
    assert_eq!(
        t.to_string(),
        "(forall ((x (_ BitVec 16))) (let ((y (bvurem x #x0d01))) (=> (in_range y) (= (to_rep (of_rep x)) y))))"
    );
}

#[test]
fn test_typed_match() {
    let mut context = Context::new();
    context.ensure_logic();
    UntypedAst
        .parse_script_str(
            r#"
    (declare-datatype List (par (X) ( (nil) (cons (car X) (cdr (List X))) ) ))
    (declare-fun append ((List Int) (List Int)) (List Int))
    "#,
        )
        .unwrap()
        .type_check(&mut context)
        .unwrap();

    // build the following:
    //
    // ( forall (( l1 ( List Int )) ( l2 ( List Int )))
    //     (= (append l1 l2)
    //     (match l1 (
    //         ( nil l2 )
    //         (( cons h t ) ( cons h ( append t l2 )))))))

    let l_int = UntypedAst
        .parse_sort_str("(List Int)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();

    let mut q_context = context.build_quantifier().unwrap();
    q_context
        .extend("l1", l_int.clone())
        .unwrap()
        .extend("l2", l_int.clone())
        .unwrap();
    let l1 = q_context.typed_symbol("l1").unwrap();
    let l2 = q_context.typed_symbol("l2").unwrap();
    let app = q_context
        .typed_simp_app("append", [l1.clone(), l2.clone()])
        .unwrap();

    let mut m_context = q_context.build_matching(l1).unwrap();
    let nil_context = m_context.build_arm_nullary("nil").unwrap();
    nil_context.typed_arm(l2.clone()).unwrap();

    // not enough arguments
    assert!(m_context.build_arm("cons", [None]).is_err());
    // too many arguments
    assert!(m_context.build_arm("cons", [None, None, None]).is_err());

    let mut cons_context = m_context.build_arm("cons", [Some("h"), Some("t")]).unwrap();
    let t_var = cons_context.typed_symbol("t").unwrap();
    let app2 = cons_context.typed_simp_app("append", [t_var, l2]).unwrap();
    let h_var = cons_context.typed_symbol("h").unwrap();
    let body = cons_context.typed_simp_app("cons", [h_var, app2]).unwrap();
    cons_context.typed_arm(body).unwrap();
    let m = m_context.typed_matching().unwrap();

    let eq = q_context.typed_eq(app, m).unwrap();
    let overall = q_context.typed_forall(eq).unwrap();
    assert_eq!(
        overall.to_string(),
        "(forall ((l1 (List Int)) (l2 (List Int))) (= (append l1 l2) (match l1 ((nil l2) ((cons h t) (cons h (append t l2)))))))"
    );
}

#[test]
fn test_wf_sort() {
    let mut context = Context::new();
    context.ensure_logic();

    UntypedAst
        .parse_script_str(
            r#"
        (define-sort Foo () Int)
        (define-sort Bar () Real)
        (declare-datatype List (par (X) ( (nil) (cons (car X) (cdr (List X))) ) ))
        (define-sort List2 (Y) (List Y))
    "#,
        )
        .unwrap()
        .type_check(&mut context)
        .unwrap();

    // it's the same to get Int in either way
    let int = context.int_sort();
    let int2 = context.wf_sort("Int").unwrap();
    assert_eq!(int, int2);

    // Foo is an alias of Int, so asking for Foo gives Int
    let foo = context.wf_sort("Foo").unwrap();
    assert_eq!(foo, int);

    let real_list = UntypedAst
        .parse_sort_str("(List Real)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    // untyped api; call it only when we are sure Real is in scope
    let real = context.real_sort();
    let real_list2 = context.wf_sort_n("List", [real]).unwrap();
    // the same goes for polymorphic type
    assert_eq!(real_list, real_list2);

    let bar = context.wf_sort("Bar").unwrap();
    let real_list3 = context.wf_sort_n("List2", [bar]).unwrap();
    // alias is also expanded for polymorphic sorts
    assert_eq!(real_list, real_list3);

    UntypedAst
        .parse_script_str("(declare-sort Baz 0)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();

    let baz_sym = context.allocate_symbol("Baz");
    // untyped api
    let baz = context.sort0(baz_sym);
    // typed api
    let baz2 = context.wf_sort_n("Baz", []).unwrap();
    assert_eq!(baz, baz2);

    // untyped api; call it only when we are sure bv theory is enabled and 10 is small enough
    let bv10 = context.bv_sort(UBig::from(10u8));
    let bv10_again = context.wf_bv_sort(UBig::from(10u8)).unwrap();
    // typed api returns the same thing
    assert_eq!(bv10, bv10_again);

    // negative checks

    // won't work; List needs a sort argument
    assert!(context.wf_sort("List").is_err());
    // won't work; too many arguments
    assert!(context.wf_sort_n("Baz", [int]).is_err());
    let large_len = UBig::from(usize::MAX);
    let large_len = large_len + 1usize;
    // blow up length for bv
    assert!(context.wf_bv_sort(large_len).is_err());
    // 0 is an invalid length
    assert!(context.wf_bv_sort(UBig::from(0u8)).is_err());
}

#[test]
fn test_wf_sort_more_negatives() {
    let mut context = Context::new();
    context.set_ctx_logic("QF_LIA").unwrap();
    // untyped api would not check the existence of this sort
    assert!(context.wf_sort("Real").is_err());
    // bv doesn't exist!
    assert!(context.wf_bv_sort(UBig::from(10u8)).is_err());
}

#[test]
fn test_typed_commands() {
    let mut context = Context::new();
    context.ensure_logic();

    let int = context.int_sort();
    let real = context.real_sort();
    let s_ctx = context.build_sort_alias("Foo", []).unwrap();
    let cmd = s_ctx.typed_define_sort(int.clone()).unwrap();
    assert_eq!(cmd.to_string(), "(define-sort Foo () Int)");

    let s_ctx = context.build_sort_alias("Bar", []).unwrap();
    let cmd = s_ctx.typed_define_sort(real).unwrap();
    assert_eq!(cmd.to_string(), "(define-sort Bar () Real)");

    let mut d_ctx = context.build_datatypes([("List", ["X"])]).unwrap();
    let mut c_ctx = d_ctx.build_datatype("List").unwrap();
    c_ctx.build_datatype_constructor_nullary("nil").unwrap();
    let xvar = c_ctx.wf_sort("X").unwrap();
    let list_x = UntypedAst
        .parse_sort_str("(List X)")
        .unwrap()
        .type_check(&mut c_ctx)
        .unwrap();
    c_ctx
        .build_datatype_constructor("cons", [("car", xvar), ("cdr", list_x)])
        .unwrap();
    c_ctx.typed_datatype().unwrap();
    let cmd = d_ctx.typed_declare_datatypes().unwrap();
    // at this point, we have declared List
    assert_eq!(
        cmd.to_string(),
        "(declare-datatype List (par (X) ((nil) (cons (car X) (cdr (List X))))))"
    );

    let list_int = context.wf_sort_n("List", [int]).unwrap();
    let mut f_ctx = context
        .build_fun_out_sort("tail", [("l", list_int.clone())], list_int)
        .unwrap();
    let t = UntypedAst
        .parse_term_str("(match l ((nil l) ((cons h t) t)))")
        .unwrap()
        .type_check(&mut f_ctx)
        .unwrap();
    let cmd = f_ctx.typed_define_fun(t).unwrap();
    assert_eq!(
        cmd.to_string(),
        "(define-fun tail ((l (List Int))) (List Int) (match l ((nil l) ((cons h t) t))))"
    );

    let real_list = UntypedAst
        .parse_sort_str("(List Real)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    let nil_list = context.typed_symbol_with_sort("nil", real_list).unwrap();
    let cmd = context
        .typed_define_const("empty-real-list", nil_list)
        .unwrap();
    assert_eq!(
        cmd.to_string(),
        "(define-const empty-real-list (List Real) (as nil (List Real)))"
    );
}

#[test]
fn test_typed_datatypes() {
    let mut context = Context::new();
    context.ensure_logic();

    let num_defs = context.symbol_count();
    let num_sorts = context.sort_count();

    // test_datatype2
    let mut d_ctx = context.build_datatypes([("Foo", [])]).unwrap();
    let mut c_ctx = d_ctx.build_datatype("Foo").unwrap();
    c_ctx.build_datatype_constructor_nullary("Baz").unwrap();
    c_ctx.typed_datatype().unwrap();
    let cmd = d_ctx.typed_declare_datatypes().unwrap();
    assert_eq!(cmd.to_string(), "(declare-datatype Foo ((Baz)))");
    let sort = context.wf_sort("Foo").unwrap();
    assert_eq!(sort.to_string(), "Foo");

    let num_defs2 = context.symbol_count();
    let num_sorts2 = context.sort_count();
    assert_eq!(num_defs + 3, num_defs2);
    assert_eq!(num_sorts + 1, num_sorts2);

    // test_datatype3
    let mut d_ctx = context.build_datatypes([("Foo3", [])]).unwrap();
    // cannot create a datatype that is not declared!
    assert!(d_ctx.build_datatype("Foo").is_err());
    let mut c_ctx = d_ctx.build_datatype("Foo3").unwrap();
    c_ctx.build_datatype_constructor_nullary("Baz3").unwrap();
    let foo3 = c_ctx.wf_sort("Foo3").unwrap();
    c_ctx
        .build_datatype_constructor("Bar3", [("x", foo3)])
        .unwrap();
    c_ctx.typed_datatype().unwrap();
    let cmd = d_ctx.typed_declare_datatypes().unwrap();
    assert_eq!(
        cmd.to_string(),
        "(declare-datatype Foo3 ((Baz3) (Bar3 (x Foo3))))"
    );
    let num_defs3 = context.symbol_count();
    let num_sorts3 = context.sort_count();
    assert_eq!(num_defs2 + 7, num_defs3);
    assert_eq!(num_sorts2 + 1, num_sorts3);

    // test_datatype7
    let mut d_ctx = context.build_datatypes([("Color", [])]).unwrap();
    let mut c_ctx = d_ctx.build_datatype("Color").unwrap();
    c_ctx.build_datatype_constructor_nullary("red").unwrap();
    c_ctx.build_datatype_constructor_nullary("green").unwrap();
    c_ctx.build_datatype_constructor_nullary("blue").unwrap();
    c_ctx.typed_datatype().unwrap();
    let cmd = d_ctx.typed_declare_datatypes().unwrap();
    assert_eq!(
        cmd.to_string(),
        "(declare-datatype Color ((red) (green) (blue)))"
    );
    let num_defs4 = context.symbol_count();
    let num_sorts4 = context.sort_count();
    assert_eq!(num_defs3 + 9, num_defs4);
    assert_eq!(num_sorts3 + 1, num_sorts4);

    // test_datatype8
    // (declare-datatypes ((Tree 1) (TreeList 1)) (
    //                     ; Tree
    //                     ( par ( X ) ( ( node ( value X ) ( children ( TreeList X )) )))
    //                     ; TreeList
    //                     ( par ( Y ) ( ( empty )
    //                                   ( insert ( head ( Tree Y )) ( tail ( TreeList Y ))) ))))
    let mut d_ctx = context
        .build_datatypes([("Tree", ["X"]), ("TreeList", ["Y"])])
        .unwrap();
    let mut c_ctx = d_ctx.build_datatype("Tree").unwrap();
    let xvar = c_ctx.wf_sort("X").unwrap();
    let xtree = UntypedAst
        .parse_sort_str("(TreeList X)")
        .unwrap()
        .type_check(&mut c_ctx)
        .unwrap();
    // Y is for TreeList
    assert!(c_ctx.wf_sort("Y").is_err());
    c_ctx
        .build_datatype_constructor("node", [("value", xvar), ("children", xtree)])
        .unwrap();
    // at this point, Tree is empty, but it's fine, as we are going to build TreeList
    c_ctx.typed_datatype().unwrap();
    // cannot re-define a datatype that has been defined!
    assert!(d_ctx.build_datatype("Tree").is_err());

    let mut c_ctx = d_ctx.build_datatype("TreeList").unwrap();
    let yvar = c_ctx.wf_sort("Y").unwrap();
    let ytree = c_ctx.wf_sort_n("Tree", [yvar.clone()]).unwrap();
    let ylist = c_ctx.wf_sort_n("TreeList", [yvar.clone()]).unwrap();
    c_ctx.build_datatype_constructor_nullary("empty").unwrap();
    // node is defined
    assert!(
        c_ctx
            .build_datatype_constructor("insert", [("node", ytree.clone())])
            .is_err()
    );
    // non-top symbol
    let ytreelist = UntypedAst
        .parse_sort_str("(TreeList (Tree Y))")
        .unwrap()
        .type_check(&mut c_ctx)
        .unwrap();
    assert!(
        c_ctx
            .build_datatype_constructor("insert", [("tail", ytreelist)])
            .is_err()
    );
    c_ctx
        .build_datatype_constructor("insert", [("head", ytree.clone()), ("tail", ylist.clone())])
        .unwrap();
    c_ctx.typed_datatype().unwrap();
    let cmd = d_ctx.typed_declare_datatypes().unwrap();
    assert_eq!(
        cmd.to_string(),
        "(declare-datatypes ((Tree 1) (TreeList 1)) ((par (X) ((node (value X) (children (TreeList X))))) (par (Y) ((empty) (insert (head (Tree Y)) (tail (TreeList Y)))))))"
    );

    let num_defs5 = context.symbol_count();
    let num_sorts5 = context.sort_count();
    assert_eq!(num_defs4 + 13, num_defs5);
    assert_eq!(num_sorts4 + 2, num_sorts5);

    let cmd2 = context
        .typed_enum("Color2", ["red2", "green2", "blue2"])
        .unwrap();
    assert_eq!(
        cmd2.to_string(),
        "(declare-datatype Color2 ((red2) (green2) (blue2)))"
    );
}

#[test]
fn test_typed_datatypes_negatives() {
    // this test focuses on negative tests for building datatypes
    let mut context = Context::new();
    context.ensure_logic();

    // let's get the number of symbols at this moment
    let old_num_defs = context.symbol_count();
    let old_num_sorts = context.sort_count();

    assert!(context.build_datatypes::<[_; 0], [_; 0], &str>([]).is_err(),);

    // test_datatype1
    // no constructor
    let mut d_ctx = context.build_datatypes([("Foo", [])]).unwrap();
    let c_ctx = d_ctx.build_datatype("Foo").unwrap();
    assert!(c_ctx.typed_datatype().is_err());
    assert!(d_ctx.typed_declare_datatypes().is_err());
    let num_defs = context.symbol_count();
    let num_sorts = context.sort_count();
    assert_eq!(old_num_defs, num_defs);
    assert_eq!(old_num_sorts, num_sorts);

    // test_datatype4
    // non-top symbols
    let mut d_ctx = context.build_datatypes([("Foo4", [])]).unwrap();
    let mut c_ctx = d_ctx.build_datatype("Foo4").unwrap();
    c_ctx.build_datatype_constructor_nullary("Baz4").unwrap();
    let foo4 = c_ctx.wf_sort("Foo4").unwrap();
    c_ctx
        .build_datatype_constructor("Bar4", [("x", foo4.clone())])
        .unwrap();
    // x has been used
    assert!(
        c_ctx
            .build_datatype_constructor("Barr4", [("x", foo4.clone())])
            .is_err()
    );
    // Bar has been used
    assert!(
        c_ctx
            .build_datatype_constructor("Bar4", [("y", foo4.clone())])
            .is_err()
    );
    let array = UntypedAst
        .parse_sort_str("(Array Int Foo4)")
        .unwrap()
        .type_check(&mut c_ctx)
        .unwrap();
    // Foo4 is not a top symbol in (Array Int Foo4)!
    assert!(
        c_ctx
            .build_datatype_constructor("Barr4", [("y", array)])
            .is_err()
    );
    let array2 = UntypedAst
        .parse_sort_str("(Array Foo4 Int)")
        .unwrap()
        .type_check(&mut c_ctx)
        .unwrap();
    // test_datatype5
    // same; Foo4 is not a top symbol in (Array Foo4 Int)!
    assert!(
        c_ctx
            .build_datatype_constructor("Barr4", [("y", array2)])
            .is_err()
    );
    // this is good
    c_ctx
        .build_datatype_constructor("Barr4", [("y", foo4.clone())])
        .unwrap();
    c_ctx.typed_datatype().unwrap();
    // now we give up on d_ctx; all previous building actions shouldn't change the context at all
    drop(d_ctx);
    let num_defs = context.symbol_count();
    let num_sorts = context.sort_count();
    assert_eq!(old_num_defs, num_defs);
    assert_eq!(old_num_sorts, num_sorts);

    // test_datatype6
    // empty datatype
    let mut d_ctx = context.build_datatypes([("Foo6", [])]).unwrap();
    let mut c_ctx = d_ctx.build_datatype("Foo6").unwrap();
    let foo6 = c_ctx.wf_sort("Foo6").unwrap();
    c_ctx
        .build_datatype_constructor("Bar6", [("x", foo6)])
        .unwrap();
    c_ctx.typed_datatype().unwrap();
    assert!(d_ctx.typed_declare_datatypes().is_err());
    let num_defs = context.symbol_count();
    let num_sorts = context.sort_count();
    assert_eq!(old_num_defs, num_defs);
    assert_eq!(old_num_sorts, num_sorts);
}

#[test]
fn test_typed_match_negatives() {
    // c.f. test_datatype12
    let mut context = Context::new();
    context.ensure_logic();

    let cmds = UntypedAst
        .parse_script_str(
            "(declare-datatype List (par (X) ( (nil) (cons (car X) (cdr (List X))) ) ))
                (declare-const foo (List Int))
                (declare-const bar Int)",
        )
        .unwrap();
    cmds.type_check(&mut context).unwrap();

    let foo = context.typed_symbol("foo").unwrap();
    let mut m_ctx = context.build_matching(foo).unwrap();
    // not enough arguments
    assert!(m_ctx.build_arm("cons", [Some("h")]).is_err());
    // too many arguments
    assert!(
        m_ctx
            .build_arm("cons", [Some("h"), Some("t"), Some("x")])
            .is_err()
    );
    assert!(m_ctx.build_arm("nil", [None]).is_err());
    // undefined constructor
    assert!(m_ctx.build_arm("baz", []).is_err());
    let mut a_ctx = m_ctx.build_arm("cons", [Some("h"), Some("t")]).unwrap();
    let tru = a_ctx.get_true();
    a_ctx.typed_arm(tru).unwrap();
    // non-covering
    assert!(m_ctx.typed_matching().is_err());
    let bar = context.typed_symbol("bar").unwrap();
    assert!(context.build_matching(bar).is_err());
}
