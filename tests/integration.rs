// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use dashu::integer::UBig;
use yaspar_ir::ast::*;
use yaspar_ir::untyped::UntypedAst;

#[test]
fn test_parse() {
    let script = r#"(forall (($generated@@18 Int)) (! (= ($generated ($generated@@8 $generated@@18)) $generated@@18) :pattern (($generated@@8 $generated@@18))))"#;
    let mut context = Context::new();
    context.ensure_logic();
    let int_sort = context.int_sort();
    let name = context.allocate_symbol("$generated@@8");
    context
        .add_symbol(name, Sig::func(vec![int_sort.clone()], int_sort.clone()))
        .unwrap();
    let name = context.allocate_symbol("$generated");
    context
        .add_symbol(name, Sig::func(vec![int_sort.clone()], int_sort))
        .unwrap();
    let term = UntypedAst.parse_term_str(script).unwrap();
    term.type_check(&mut context).unwrap();
}

#[test]
fn test_real_int_comparison() {
    let script = r"
(set-logic QF_LIRA)
(declare-const x Real)
(assert (< x (/ 1 3)))
(check-sat)
";
    let mut ctx = Context::new();
    let cs = UntypedAst.parse_script_str(script).unwrap();
    assert!(cs.type_check(&mut ctx).is_ok());

    let script = r"
(set-logic QF_LIRA)
(declare-const x Real)
(assert (< x (/ 1.0 3.0)))
(check-sat)
";
    let mut ctx = Context::new();
    let cs = UntypedAst.parse_script_str(script).unwrap();
    assert!(cs.type_check(&mut ctx).is_ok());
}

#[test]
fn test_true() {
    let mut context = Context::new();
    context.ensure_logic();
    let cmd = UntypedAst
        .parse_command_str("(assert true)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    let t = match cmd.repr() {
        ACommand::Assert(t) => t.clone(),
        _ => panic!(),
    };
    assert_eq!(t, context.get_true());
    assert_eq!(t.to_string(), "true");
}

#[test]
fn test_false() {
    let mut context = Context::new();
    context.ensure_logic();
    let cmd = UntypedAst
        .parse_command_str("(assert false)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    let t = match cmd.repr() {
        ACommand::Assert(t) => t.clone(),
        _ => panic!(),
    };
    assert_eq!(t, context.get_false());
    assert_eq!(t.to_string(), "false");
}

#[test]
fn test_xor_parsing() {
    let mut context = Context::new();
    context.ensure_logic();
    let xor = UntypedAst
        .parse_term_str("(xor true false)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    assert_eq!(xor.to_string(), "(xor true false)");
}

#[test]
fn test_xor() {
    let script = r"
(set-logic ALL)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(assert (xor p q))
(assert (xor p q r))
(assert (xor (and p q) (or p q)))
(assert (= (xor p q) (not (= p q))))
";
    let mut ctx = Context::new();
    let cs = UntypedAst.parse_script_str(script).unwrap();
    assert!(cs.type_check(&mut ctx).is_ok());

    let script = r"
(set-logic QF_LIA)
(declare-const x Int)
(assert (xor x true))
";
    let mut ctx = Context::new();
    let cs = UntypedAst.parse_script_str(script).unwrap();
    assert!(cs.type_check(&mut ctx).is_err());

    let script = "(assert (xor true))";
    let mut ctx = Context::new();
    ctx.ensure_logic();
    assert!(UntypedAst.parse_script_str(script).is_err());
}

#[test]
fn test_int_div() {
    // int division operator is `div`
    let script: String = r"
(set-logic QF_LIA)
(declare-const a Int)
(declare-const b Int)
(assert (= a (div b 2)))    ; a = b/2
(assert (= a (div b 2 a)))  ; a = (b/2)/a"
        .into();
    let mut ctx = Context::new();
    let cs = UntypedAst.parse_script_str(&script).unwrap();
    // type checking succeeds on all commands
    assert!(cs.type_check(&mut ctx).is_ok());

    // / is not defined for Ints
    let script: String = r"
(set-logic QF_LIA)
(declare-const a Int)
(declare-const b Int)
(assert (= a (/ b 2)))  ; undefined symbol"
        .into();
    let mut ctx = Context::new();
    let cs = UntypedAst.parse_script_str(&script).unwrap();
    assert!(cs.type_check(&mut ctx).is_err());
}

#[test]
fn test_real_division() {
    // Real division operator is /
    let script: String = r"
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (= x (/ y (/ 1 2))))  ; / applied to pairs of NUMERALS and pairs of Real variables
(assert (< 0.0 (/ y 3)))      ; / applied to a Real and a NUMERAL
(assert (= 1.0 (/ x y x)))    ; / can be applied to two or more arguments (left-assoc)"
        .into();
    let mut ctx = Context::new();
    let cs = UntypedAst.parse_script_str(&script).unwrap();
    // type checking succeeds on all commands
    assert!(cs.type_check(&mut ctx).is_ok());

    // div is not defined on Reals
    let script: String = r"
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (= x (div y 2)))  ; undefined symbol"
        .into();
    let mut ctx = Context::new();
    let cs = UntypedAst.parse_script_str(&script).unwrap();
    assert!(cs.type_check(&mut ctx).is_err());
}

#[test]
fn test_real_int_division() {
    // Real division operator is `/`, Int division is `div`, and NUMERALS type as Ints
    let script: String = r"
(set-logic QF_LIRA)
(declare-const a Int)
(declare-const b Int)
(declare-const x Real)
(declare-const y Real)
(assert (= x (/ y (/ (to_real 1) (to_real 2)))))  ; / applied to pairs of NUMERALS and pairs of Real variables
(assert (< 0.0 (/ y (to_real 3))))                ; / applied to a Real and a NUMERAL
(assert (< 0.0 (/ (- (to_real 4)) (to_real 3))))  ; / applied to a negative NUMERAL and a non-zero NUMERAL
(assert (= 1.0 (/ x y x)))                        ; / can be applied to two or more arguments (left-assoc)
(assert (= 42 (div a b a)))                       ; div can be applied to two or more arguments (left-assoc)
"
    .into();
    let mut ctx = Context::new();
    let cs = UntypedAst.parse_script_str(&script).unwrap();
    // type checking succeeds on all commands; leaving as a loop to aid in test debugging
    for c in &cs {
        assert!(
            c.type_check(&mut ctx).is_ok(),
            "unexpected type error {}",
            c
        );
    }

    // Negative type checking tests
    //
    // Note: basically all solvers allow `(/ NUMERAL NUMERAL)` directly, overloading for
    // Ints. We test here that this is not allowed.
    let script: String = r"
(set-logic QF_LIRA)
(declare-const a Int)
(declare-const b Int)
(declare-const x Real)
(declare-const y Real)
(assert (= x (div y 2)))  ; div is not overloaded for Reals
"
    .into();
    let mut ctx = Context::new();
    let cs = UntypedAst.parse_script_str(&script).unwrap();
    // there is a type error in the assertion
    let ts: Vec<_> = cs.iter().map(|c| c.type_check(&mut ctx)).collect();
    assert_eq!(ts.len(), 6);
    for (i, t) in ts.iter().take(5).enumerate() {
        assert!(t.is_ok(), "is_ok assertion {i} failed");
    }
    assert!(ts[5].is_err(), "is_err assertion 5 failed");
}

#[test]
fn test_real_int_implicit_conversion() {
    let mut ctx = Context::new();
    ctx.ensure_logic();
    let t1 = UntypedAst
        .parse_term_str("(/ 1 2)")
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let t2 = UntypedAst
        .parse_term_str("(/ (to_real 1) (to_real 2))")
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    // `to_real` is implicitly inserted.
    assert_eq!(t1, t2);
}

#[test]
fn test_minus() {
    // Int minus operator takes one or more arguments (left-associative)
    let script: String = r"
(set-logic QF_LIA)
(declare-const a Int)
(assert (= 0 (- a)))
(assert (= 0 (- a a)))
(assert (= 0 (- a a a)))
"
    .into();
    let mut ctx = Context::new();
    let cs = UntypedAst.parse_script_str(&script).unwrap();
    assert!(cs.type_check(&mut ctx).is_ok());

    // same with Real minus
    let script: String = r"
(set-logic QF_LRA)
(declare-const a Real)
(assert (= 0.0 (- a)))
(assert (= 0.0 (- a a)))
(assert (= 0.0 (- a a a)))
"
    .into();
    let mut ctx = Context::new();
    let cs = UntypedAst.parse_script_str(&script).unwrap();
    assert!(cs.type_check(&mut ctx).is_ok());
}

#[test]
fn test_is_int() {
    // signature of is_int : Real -> Bool
    let script: String = r"
(set-logic QF_LIRA)
(declare-const a Real)
(assert (= (* (to_real 6) a) (to_real 12)))
(assert (is_int a))
(check-sat)
"
    .into();
    let mut ctx = Context::new();
    let cs = UntypedAst.parse_script_str(&script).unwrap();
    assert!(cs.type_check(&mut ctx).is_ok());
}

#[test]
fn test_comparison() {
    let term = "(forall ((m Int) (n Int))
      (and (<= 0 m n) (< 0 m n) (>= 0 m n) (> 0 m n)))";
    let t = UntypedAst.parse_term_str(term).unwrap();

    let mut ctx = Context::new();
    ctx.set_ctx_logic("ALL").unwrap();
    assert!(t.type_check(&mut ctx).is_ok());
    assert!(
        UntypedAst
            .parse_term_str("(< 0)")
            .unwrap()
            .type_check(&mut ctx)
            .is_err()
    );

    let mut ctx = Context::new();
    ctx.set_ctx_logic("LIA").unwrap();
    assert!(t.type_check(&mut ctx).is_ok());
    assert!(
        UntypedAst
            .parse_term_str("(< 0)")
            .unwrap()
            .type_check(&mut ctx)
            .is_err()
    );
}

#[test]
fn test_string1() {
    let term = UntypedAst.parse_term_str("((_ re.^ 10) re.none)").unwrap();
    let mut context = Context::new();
    context.set_ctx_logic("QF_S").unwrap();
    let term = term.type_check(&mut context).unwrap();
    let s = term.get_sort(&mut context);
    assert_eq!(s, context.reglan_sort())
}

#[test]
fn test_string2() {
    let term = UntypedAst
        .parse_term_str("((_ re.loop 2 10) re.none)")
        .unwrap();
    let mut context = Context::new();
    context.set_ctx_logic("QF_S").unwrap();
    let term = term.type_check(&mut context).unwrap();
    let s = term.get_sort(&mut context);
    assert_eq!(s, context.reglan_sort())
}

#[test]
fn test_string3() {
    let term = UntypedAst.parse_term_str("(re.^ re.none)").unwrap();
    let mut context = Context::new();
    context.set_ctx_logic("QF_S").unwrap();
    let r = term.type_check(&mut context);
    assert!(r.is_err());
}

#[test]
fn test_string4() {
    let term = UntypedAst
        .parse_term_str("((_ re.loop 2) re.none)")
        .unwrap();
    let mut context = Context::new();
    context.set_ctx_logic("QF_S").unwrap();
    let r = term.type_check(&mut context);
    assert!(r.is_err());
}

#[test]
fn test_string5() {
    let term = UntypedAst
        .parse_term_str(r#"(str.< "a" "aardvark" "aardwolf" "zygomorphic" "zygotic")"#)
        .unwrap();
    let mut context = Context::new();
    context.set_ctx_logic("QF_S").unwrap();
    assert!(term.type_check(&mut context).is_ok());
    assert!(
        UntypedAst
            .parse_term_str(r#"(str.< "")"#)
            .unwrap()
            .type_check(&mut context)
            .is_err()
    );

    let term = UntypedAst
        .parse_term_str(r#"(str.<= "a" "aardvark" "aardwolf" "zygomorphic" "zygotic")"#)
        .unwrap();
    let mut context = Context::new();
    context.set_ctx_logic("QF_S").unwrap();
    assert!(term.type_check(&mut context).is_ok());
    assert!(
        UntypedAst
            .parse_term_str(r#"(str.<= "")"#)
            .unwrap()
            .type_check(&mut context)
            .is_err()
    );
}

#[test]
fn test_array1() {
    let script = "(declare-fun a1 () (Array Int Int))";
    let cmds = UntypedAst.parse_script_str(script).unwrap();
    let mut context = Context::new();
    context.set_ctx_logic("AUFLIA").unwrap();
    cmds.type_check(&mut context).unwrap();
    let term = UntypedAst.parse_term_str("(select a1 3)").unwrap();
    let term = term.type_check(&mut context).unwrap();
    let s = term.get_sort(&mut context);
    assert_eq!(s, context.int_sort())
}

#[test]
fn test_array2() {
    let script = "(declare-fun a1 () (Array Bool Int))";
    let cmds = UntypedAst.parse_script_str(script).unwrap();
    let mut context = Context::new();
    context.set_ctx_logic("AUFLIA").unwrap();
    cmds.type_check(&mut context).unwrap();
    let term = UntypedAst.parse_term_str("(select a1 3)").unwrap();
    let r = term.type_check(&mut context);
    assert!(r.is_err());
}

#[test]
fn test_array3() {
    let mut context = Context::new();
    context.ensure_logic();
    let term = UntypedAst
        .parse_term_str("(forall ((a1 (Array Int Bool))) (and (select a1 3) false))")
        .unwrap();
    let term = term.type_check(&mut context).unwrap();
    let s = term.get_sort(&mut context);
    assert_eq!(s, context.bool_sort())
}

#[test]
fn test_array4() {
    let mut context = Context::new();
    context.ensure_logic();
    let term = UntypedAst
        .parse_term_str("(forall ((a1 (Array Bool))) (and (select a1 3) false))")
        .unwrap();
    let r = term.type_check(&mut context);
    assert!(r.is_err());
}

#[test]
fn test_datatype1() {
    let mut context = Context::new();
    context.ensure_logic();
    let cmd = UntypedAst.parse_command_str("(declare-datatype Foo () )");
    assert!(cmd.is_err());
}

#[test]
fn test_datatype2() {
    let mut context = Context::new();
    context.ensure_logic();
    let begin = context.symbol_count();
    let cmd = UntypedAst
        .parse_command_str("(declare-datatype Foo ( (Baz) ) )")
        .unwrap();
    cmd.type_check(&mut context).unwrap();
    assert_eq!(begin + 3, context.symbol_count());
}

#[test]
fn test_datatype3() {
    let mut context = Context::new();
    context.ensure_logic();
    let begin = context.symbol_count();
    let cmd = UntypedAst
        .parse_command_str("(declare-datatype Foo ( (Baz) (Bar (x Foo) ) ))")
        .unwrap();
    cmd.type_check(&mut context).unwrap();
    assert_eq!(begin + 7, context.symbol_count());
}

#[test]
fn test_datatype4() {
    let mut context = Context::new();
    context.ensure_logic();
    let cmd = UntypedAst
        .parse_command_str(
            "(declare-datatype Foo ( (Baz) (Bar (x Foo) ) (Barr (y (Array Int Foo))) ) )",
        )
        .unwrap();
    assert!(cmd.type_check(&mut context).is_err());
}
#[test]
fn test_datatype5() {
    let mut context = Context::new();
    context.ensure_logic();
    let cmd = UntypedAst
        .parse_command_str(
            "(declare-datatype Foo ( (Baz) (Bar (x Foo) ) (Barr (y (Array Foo Int))) ) )",
        )
        .unwrap();
    assert!(cmd.type_check(&mut context).is_err());
}

#[test]
fn test_datatype6() {
    let mut context = Context::new();
    context.ensure_logic();
    let cmd = UntypedAst
        .parse_command_str("(declare-datatype Foo ( (Bar (x Foo) ) ) )")
        .unwrap();
    assert!(cmd.type_check(&mut context).is_err());
}

#[test]
fn test_datatype7() {
    let mut context = Context::new();
    context.ensure_logic();
    let begin = context.symbol_count();
    let cmd = UntypedAst
        .parse_command_str(
            "(declare-datatypes ( (Color 0) ) (
                    ( ( red ) ( green ) ( blue ) ))
                )",
        )
        .unwrap();
    cmd.type_check(&mut context).unwrap();
    assert_eq!(begin + 9, context.symbol_count());
    UntypedAst
        .parse_term_str(
            "(forall ((x Color)) (exists ((y Int)) \
    (= y (match x ((red 1) (green 2) (blue 3) )))\
    ))",
        )
        .unwrap()
        .type_check(&mut context)
        .unwrap();
}

#[test]
fn test_datatype8() {
    let mut context = Context::new();
    context.ensure_logic();
    let begin = context.symbol_count();
    let cmd = UntypedAst
        .parse_command_str(
            "(declare-datatypes ((Tree 1) (TreeList 1)) (
                    ; Tree
                    ( par ( X ) ( ( node ( value X ) ( children ( TreeList X )) )))
                    ; TreeList
                    ( par ( Y ) ( ( empty )
                    ( insert ( head ( Tree Y )) ( tail ( TreeList Y ))) ))))",
        )
        .unwrap();
    cmd.type_check(&mut context).unwrap();
    assert_eq!(begin + 13, context.symbol_count());
}

#[test]
fn test_datatype9() {
    let mut context = Context::new();
    context.ensure_logic();
    let cmds = UntypedAst
        .parse_script_str(
            "
  		          (declare-datatype Color ((Blue) (Red)))
  		          (declare-const X Color)
  		          (assert (= X Blue))
  		          ",
        )
        .unwrap();
    cmds.type_check(&mut context).unwrap();
}

#[test]
fn test_datatype10() {
    let mut context = Context::new();
    context.ensure_logic();
    let cmds = UntypedAst
        .parse_script_str(
            "
  		          (declare-datatype List (par (X) ( (nil) (cons (car X) (cdr (List X))) ) ))
  		          (declare-const foo (List Int))
  		          (assert (= foo (as nil (List Int))))
  		          ",
        )
        .unwrap();
    cmds.type_check(&mut context).unwrap();
}

#[test]
fn test_datatype11() {
    let mut context = Context::new();
    context.ensure_logic();
    let cmds = UntypedAst
        .parse_script_str(
            "(declare-datatype List (par (X) ( (nil) (cons (car X) (cdr (List X))) ) ))
                (declare-fun append ((List Int) (List Int)) (List Int))
            ",
        )
        .unwrap();
    cmds.type_check(&mut context).unwrap();

    // tests from the spec, p29
    let t = UntypedAst
        .parse_term_str(
            "
    ( forall (( l1 ( List Int )) ( l2 ( List Int )))
        (= (append l1 l2)
           (match l1 (
             ( nil l2 )
             (( cons h t ) ( cons h ( append t l2 )))))))",
        )
        .unwrap();
    t.type_check(&mut context).unwrap();

    let t = UntypedAst
        .parse_term_str(
            "
    ( forall (( l1 ( List Int )) ( l2 ( List Int )))
        (= (append l1 l2)
           (match l1 (
             (( cons h t ) ( cons h ( append t l2 )))
              ( x l2 )))))",
        )
        .unwrap();
    t.type_check(&mut context).unwrap();

    UntypedAst
        .parse_script_str(
            "(declare-fun head ( (List Int) ) Int)

        (declare-fun tail ( (List Int) ) (List Int))",
        )
        .unwrap()
        .type_check(&mut context)
        .unwrap();

    UntypedAst
        .parse_term_str(
            "
    ( forall (( l ( List Int )))
        (= (head l)
           (match l (
             (( cons h _ ) h)
              ( _ 0 )))))",
        )
        .unwrap()
        .type_check(&mut context)
        .unwrap();

    UntypedAst
        .parse_term_str(
            "
    ( forall (( l ( List Int )))
        (= (tail l)
           (match l (
             (( cons _ t ) t)
              ( _ (as nil (List Int)) )))))",
        )
        .unwrap()
        .type_check(&mut context)
        .unwrap();
}

#[test]
fn test_datatype12() {
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

    // negative tests
    // 1. nested patterns don't parse
    assert!(
        UntypedAst
            .parse_term_str("(match foo ( ((cons h1 (cons h2 t)) true) (x false) ))")
            .is_err()
    );

    // 2. not enough arguments
    let t = UntypedAst
        .parse_term_str("(match foo ( ((cons h) true) (nil false) ))")
        .unwrap();
    assert!(t.type_check(&mut context).is_err());

    // 3. too many arguments
    let t = UntypedAst
        .parse_term_str("(match foo ( ((cons h t x) true) (nil false) ))")
        .unwrap();
    assert!(t.type_check(&mut context).is_err());

    // 4. undefined constructor
    let t = UntypedAst
        .parse_term_str("(match foo ( ((cons h t) true) ((foo x) false) ))")
        .unwrap();
    assert!(t.type_check(&mut context).is_err());

    // 5. uncovered branches
    let t = UntypedAst
        .parse_term_str("(match foo ( ((cons h t) true) ))")
        .unwrap();
    assert!(t.type_check(&mut context).is_err());

    // 6. bad match on non-datatype
    let t = UntypedAst
        .parse_term_str("(match bar ( (x true) ))")
        .unwrap();
    assert!(t.type_check(&mut context).is_err());
}

#[test]
fn test_bv1() {
    let mut context = Context::new();
    context.set_ctx_logic("QF_BV").unwrap();
    let cmd = UntypedAst
        .parse_command_str("(define-fun foo () (_ BitVec 2) (_ bv3 2))")
        .unwrap();
    cmd.type_check(&mut context).unwrap();
}

#[test]
fn test_bv2() {
    let mut context = Context::new();
    context.set_ctx_logic("QF_BV").unwrap();
    let cmd = UntypedAst
        .parse_command_str("(define-fun foo () (_ BitVec 10) (_ bv3 10))")
        .unwrap();
    cmd.type_check(&mut context).unwrap();
}

#[test]
fn test_bv3() {
    let mut context = Context::new();
    context.set_ctx_logic("QF_BV").unwrap();
    let cmd = UntypedAst
        .parse_command_str("(define-fun foo () (_ BitVec 2) (_ bv4 2))")
        .unwrap();
    // 4 cannot be fit into 2 bits
    assert!(cmd.type_check(&mut context).is_err());
}

#[test]
fn test_bv5() {
    let mut context = Context::new();
    context.set_ctx_logic("QF_BV").unwrap();
    let cmd = UntypedAst
        .parse_command_str("(declare-const foo (_ BitVec 0))")
        .unwrap();
    // bit vector cannot be 0 bit
    assert!(cmd.type_check(&mut context).is_err());
}

#[test]
fn test_bv6() {
    let mut context = Context::new();
    context.set_ctx_logic("QF_BV").unwrap();
    let cmd = UntypedAst
        .parse_command_str("(define-fun foo () (_ BitVec 2) (_ bv4 0))")
        .unwrap();
    // bit length mismatch
    assert!(cmd.type_check(&mut context).is_err());
}

#[test]
fn test_bv7() {
    let mut context = Context::new();
    context.set_ctx_logic("QF_BV").unwrap();
    let cmd = UntypedAst
        .parse_command_str("(define-fun foo () (_ BitVec 2) (_ bv4 3))")
        .unwrap();
    // bit length mismatch
    assert!(cmd.type_check(&mut context).is_err());
}

#[test]
fn test_bv8() {
    let mut context = Context::new();
    context.ensure_logic();
    UntypedAst
        .parse_script_str(
            "
    (declare-const foo (_ BitVec 20))
    (declare-const bar (_ BitVec 2))
    (declare-const baz (_ BitVec 20))
    ",
        )
        .unwrap()
        .type_check(&mut context)
        .unwrap();

    let bv22 = context.bv_sort(UBig::from(22u8));
    let foo = context.typed_symbol("foo").unwrap();
    let bar = context.typed_symbol("bar").unwrap();
    let bv20 = foo.get_sort(&mut context);
    let bv2 = bar.get_sort(&mut context);
    let bv1 = context.bv_sort(UBig::from(1u8));
    let bool = context.bool_sort();
    let int = context.int_sort();

    // concat is special
    let t = UntypedAst
        .parse_term_str("(concat foo)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    assert_eq!(t.get_sort(&mut context), bv20);

    let t = UntypedAst
        .parse_term_str("(concat foo bar)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    assert_eq!(t.get_sort(&mut context), bv22);

    let t = UntypedAst
        .parse_term_str("(concat foo bar baz)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    let bv42 = context.bv_sort(UBig::from(42u8));
    assert_eq!(t.get_sort(&mut context), bv42);

    assert!(
        UntypedAst
            .parse_term_str("(concat foo bar 1 baz)")
            .unwrap()
            .type_check(&mut context)
            .is_err()
    );

    let t = UntypedAst
        .parse_term_str("((_ extract 10 2) foo)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    let bv9 = context.bv_sort(UBig::from(9u8));
    assert_eq!(t.get_sort(&mut context), bv9);

    assert!(
        UntypedAst
            .parse_term_str("((_ extract 10 2) bar)")
            .unwrap()
            .type_check(&mut context)
            .is_err()
    );

    // unsigned integer underflow during TC!
    assert!(
        UntypedAst
            .parse_term_str("((_ extract 2 10) foo)")
            .unwrap()
            .type_check(&mut context)
            .is_err()
    );

    // marginally safe
    let t = UntypedAst
        .parse_term_str("((_ extract 10 10) foo)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    assert_eq!(t.get_sort(&mut context), bv1);

    // create bit vector size 0!
    assert!(
        UntypedAst
            .parse_term_str("((_ extract 10 11) foo)")
            .unwrap()
            .type_check(&mut context)
            .is_err()
    );

    let t = UntypedAst
        .parse_term_str("(bvnot foo)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    assert_eq!(t.get_sort(&mut context), bv20);

    // wrong number of arguments
    assert!(
        UntypedAst
            .parse_term_str("(bvnot foo bar)")
            .unwrap()
            .type_check(&mut context)
            .is_err()
    );

    // bvand is chainable
    let t = UntypedAst
        .parse_term_str("(bvand bar bar bar bar)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    assert_eq!(t.get_sort(&mut context), bv2);
    assert!(
        UntypedAst
            .parse_term_str("(bvadd foo bar)")
            .unwrap()
            .type_check(&mut context)
            .is_err()
    );

    // bv length mismatch
    assert!(
        UntypedAst
            .parse_term_str("(bvshl foo bar)")
            .unwrap()
            .type_check(&mut context)
            .is_err()
    );

    let t = UntypedAst
        .parse_term_str("(bvshl foo baz)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    assert_eq!(t.get_sort(&mut context), bv20);

    // wrong number of arguments
    assert!(
        UntypedAst
            .parse_term_str("(bvshl foo)")
            .unwrap()
            .type_check(&mut context)
            .is_err()
    );

    assert!(
        UntypedAst
            .parse_term_str("(bvshl foo baz baz)")
            .unwrap()
            .type_check(&mut context)
            .is_err()
    );

    let t = UntypedAst
        .parse_term_str("(bvnego foo)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    assert_eq!(t.get_sort(&mut context), bool);

    let t = UntypedAst
        .parse_term_str("(bvsaddo foo baz)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    assert_eq!(t.get_sort(&mut context), bool);

    let t = UntypedAst
        .parse_term_str("(ubv_to_int foo)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    assert_eq!(t.get_sort(&mut context), int);
    let t = UntypedAst
        .parse_term_str("(bv2int foo)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    assert_eq!(t.get_sort(&mut context), int);

    let t = UntypedAst
        .parse_term_str("((_ int_to_bv 20) 1000)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    assert_eq!(t.get_sort(&mut context), bv20);

    let t = UntypedAst
        .parse_term_str("(bvcomp foo baz)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    assert_eq!(t.get_sort(&mut context), bv1);

    let t = UntypedAst
        .parse_term_str("((_ repeat 10) bar)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    assert_eq!(t.get_sort(&mut context), bv20);

    let t = UntypedAst
        .parse_term_str("((_ zero_extend 18) bar)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    assert_eq!(t.get_sort(&mut context), bv20);

    let t = UntypedAst
        .parse_term_str("((_ zero_extend 19) bar)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    assert_ne!(t.get_sort(&mut context), bv20);

    let t = UntypedAst
        .parse_term_str("((_ rotate_left 10) bar)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    assert_eq!(t.get_sort(&mut context), bv2);

    let t = UntypedAst
        .parse_term_str("((_ rotate_left 100) baz)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    assert_eq!(t.get_sort(&mut context), bv20);
}

#[test]
fn test_rejected_2_7_features() {
    assert!(
        UntypedAst
            .parse_term_str("(lambda ((x Int)) (and (<= 0 x) (<= x 9)))")
            .is_err()
    );
    assert!(
        UntypedAst
            .parse_command_str("(declare-sort-parameter foobar)")
            .is_err()
    );
}

#[test]
fn test_fresh_vars() {
    let mut context = Context::new();
    context.ensure_logic();

    let x = context.fresh_x();
    assert_eq!(x.inner(), "x-0");
    // counter should be 0; not incremented

    UntypedAst
        .parse_script_str("(declare-const y-0 Int)")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    let y = context.fresh_var("y");
    assert_eq!(y.inner(), "y-1");
    // y0 has been declared, so y-1 is returned, counter is 1

    let y = context.fresh_var("y");
    assert_eq!(y.inner(), "y-2");
    // now the counter is 2.

    UntypedAst
        .parse_term_str("(forall ((z-2 Int)) (exists ((z-3 Real)) (= (to_real z-2) z-3)))")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
    // now z2 and z3 are used, so the next is z4
    let z = context.fresh_var("z");
    assert_eq!(z.inner(), "z-4");
}

#[test]
fn test_check_sat_assuming() {
    let mut context = Context::new();
    context.ensure_logic();

    // negative; 1 is not a boolean
    assert!(
        UntypedAst
            .parse_command_str("(check-sat-assuming ( 1 ))")
            .unwrap()
            .type_check(&mut context)
            .is_err()
    );

    // positive cases; two booleans
    UntypedAst
        .parse_command_str("(check-sat-assuming ( true ))")
        .unwrap()
        .type_check(&mut context)
        .unwrap();

    UntypedAst
        .parse_command_str("(check-sat-assuming ( false ))")
        .unwrap()
        .type_check(&mut context)
        .unwrap();

    UntypedAst
        .parse_script_str(
            "
        (declare-const x Real)
        (declare-const y Real)",
        )
        .unwrap()
        .type_check(&mut context)
        .unwrap();

    // (+ x 1) is not boolean
    assert!(
        UntypedAst
            .parse_command_str("(check-sat-assuming ( (+ x 1) ))")
            .unwrap()
            .type_check(&mut context)
            .is_err()
    );

    // all terms must be boolean
    assert!(
        UntypedAst
            .parse_command_str("(check-sat-assuming ( false (+ x 1) ))")
            .unwrap()
            .type_check(&mut context)
            .is_err()
    );

    // all boolean; good
    UntypedAst
        .parse_command_str("(check-sat-assuming ( (= (+ x 1) y) ))")
        .unwrap()
        .type_check(&mut context)
        .unwrap();

    UntypedAst
        .parse_command_str("(check-sat-assuming ( (= (+ x 1) y) (< y x) ))")
        .unwrap()
        .type_check(&mut context)
        .unwrap();
}

#[test]
fn test_named_annotations() {
    let mut context = Context::new();
    context.ensure_logic();

    UntypedAst
        .parse_script_str(
            "
        (declare-const x Real)
        (declare-const y Real)",
        )
        .unwrap()
        .type_check(&mut context)
        .unwrap();

    UntypedAst
        .parse_script_str(
            "
        (assert (! (> x y) :named foo))",
        )
        .unwrap()
        .type_check(&mut context)
        .unwrap();

    let t = context.typed_symbol("foo").unwrap();
    assert!(t.get_sort(&mut context).is_bool());

    // foo is used
    assert!(
        UntypedAst
            .parse_script_str(
                "
        (assert (! (>= x y) :named foo))",
            )
            .unwrap()
            .type_check(&mut context)
            .is_err()
    );

    // two named also works
    UntypedAst
        .parse_script_str(
            "
        (assert (! (< x y) :named bar :named baz))",
        )
        .unwrap()
        .type_check(&mut context)
        .unwrap();

    let t = context.typed_symbol("bar").unwrap();
    assert!(t.get_sort(&mut context).is_bool());
    let t = context.typed_symbol("baz").unwrap();
    assert!(t.get_sort(&mut context).is_bool());

    // nested also works
    UntypedAst
        .parse_script_str(
            "
        (assert (! (! (= x y) :named bar1) :named baz1))",
        )
        .unwrap()
        .type_check(&mut context)
        .unwrap();

    let t = context.typed_symbol("bar1").unwrap();
    assert!(t.get_sort(&mut context).is_bool());
    let t = context.typed_symbol("baz1").unwrap();
    assert!(t.get_sort(&mut context).is_bool());

    // not top level :named has no effect
    UntypedAst
        .parse_script_str(
            "
        (assert (distinct (! x :named xxx) y))",
        )
        .unwrap()
        .type_check(&mut context)
        .unwrap();

    assert!(context.typed_symbol("xxx").is_err());
}

fn test_main() -> TC<()> {
    let mut context = Context::new();
    context.set_ctx_logic("ALL").unwrap();

    UntypedAst
        .parse_script_str("(declare-const foo Int) (declare-const bar Int)")
        .unwrap()
        .type_check(&mut context)?;

    let var = context.typed_symbol("foo")?;
    let int_sort = context.wf_sort("Int")?;
    assert_eq!(var.to_string(), "foo");
    assert_eq!(var.get_sort(&mut context), int_sort);

    let mut q_ctx = context.build_quantifier()?;
    q_ctx
        .extend("x", int_sort.clone())?
        .extend("y", int_sort.clone())?;
    // commutativity of addition
    let xy = UntypedAst
        .parse_term_str("(+ x y)")
        .unwrap()
        .type_check(&mut q_ctx)?;
    assert_eq!(xy.to_string(), "(+ x y)");
    let x = q_ctx.typed_symbol("x")?;
    let y = q_ctx.typed_symbol("y")?;
    let yx = q_ctx.typed_simp_app("+", [y, x])?;
    assert_eq!(yx.to_string(), "(+ y x)");
    let eq = q_ctx.typed_eq(xy, yx)?;
    let comm = q_ctx.typed_forall(eq)?;
    assert_eq!(
        comm.to_string(),
        "(forall ((x Int) (y Int)) (= (+ x y) (+ y x)))"
    );
    Ok(())
}

#[test]
fn do_test() {
    test_main().unwrap()
}

fn cannot_add_symbol(context: &mut Context, sym: &str) {
    let sym = context.allocate_symbol(sym);
    assert!(context.can_add_symbol(&sym).is_err());
}

#[test]
fn test_special_symbols() {
    let mut context = Context::new();
    for sym in yaspar::tokens::SPECIAL_SYMBOLS.keys() {
        cannot_add_symbol(&mut context, sym);
    }
    cannot_add_symbol(&mut context, "and");
    cannot_add_symbol(&mut context, "or");
    cannot_add_symbol(&mut context, "not");
    cannot_add_symbol(&mut context, "=>");
    cannot_add_symbol(&mut context, "=");
    cannot_add_symbol(&mut context, "ite");
    cannot_add_symbol(&mut context, "distinct");
}

#[test]
fn test_build_fun_context() {
    let mut ctx = Context::new();
    ctx.ensure_logic();

    let int = ctx.int_sort();
    let mut f_ctx = ctx
        .build_fun_out_sort("add", [("x", int.clone()), ("y", int.clone())], int)
        .unwrap();
    let x = f_ctx.typed_symbol("x").unwrap();
    let y = f_ctx.typed_symbol("y").unwrap();
    let body = f_ctx.typed_simp_app("+", [x, y]).unwrap();
    let cmd = f_ctx.typed_define_fun(body).unwrap();

    assert_eq!(
        cmd.to_string(),
        "(define-fun add ((x Int) (y Int)) Int (+ x y))"
    );
}

#[test]
fn test_build_fun_with_quantifier() {
    let mut ctx = Context::new();
    ctx.ensure_logic();

    let int = ctx.int_sort();
    let bool = ctx.bool_sort();
    let mut f_ctx = ctx
        .build_fun_out_sort("is_positive", [("x", int)], bool)
        .unwrap();
    let body = UntypedAst
        .parse_term_str("(> x 0)")
        .unwrap()
        .type_check(&mut f_ctx)
        .unwrap();
    let cmd = f_ctx.typed_define_fun(body).unwrap();

    assert_eq!(
        cmd.to_string(),
        "(define-fun is_positive ((x Int)) Bool (> x 0))"
    );
}

#[test]
fn test_build_matching_context() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-datatype Option ((none) (some (value Int))))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let option = ctx.wf_sort("Option").unwrap();
    let mut q_ctx = ctx.build_quantifier_with_domain([("o", option)]).unwrap();
    let o = q_ctx.typed_symbol("o").unwrap();
    let zero = q_ctx.numeral(UBig::from(0u8)).unwrap();
    let mut m_ctx = q_ctx.build_matching(o).unwrap();

    let none_ctx = m_ctx.build_arm_nullary("none").unwrap();
    none_ctx.typed_arm(zero.clone()).unwrap();

    let mut some_ctx = m_ctx.build_arm("some", [Some("v")]).unwrap();
    let v = some_ctx.typed_symbol("v").unwrap();
    some_ctx.typed_arm(v).unwrap();

    let match_term = m_ctx.typed_matching().unwrap();
    let eq = q_ctx.typed_eq(match_term, zero).unwrap();
    let forall = q_ctx.typed_forall(eq).unwrap();

    assert_eq!(
        forall.to_string(),
        "(forall ((o Option)) (= (match o ((none 0) ((some v) v))) 0))"
    );
}

#[test]
fn test_matching_get_constructors() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-datatype Color ((red) (green) (blue)))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let color = ctx.wf_sort("Color").unwrap();
    let mut q_ctx = ctx.build_quantifier_with_domain([("c", color)]).unwrap();
    let c = q_ctx.typed_symbol("c").unwrap();
    let mut m_ctx = q_ctx.build_matching(c).unwrap();

    let ctors = m_ctx.get_constructors();
    assert_eq!(ctors.len(), 3);

    assert!(m_ctx.is_constructor(&"red"));
    assert!(m_ctx.is_constructor(&"green"));
    assert!(m_ctx.is_constructor(&"blue"));
    assert!(!m_ctx.is_constructor(&"yellow"));
}

#[test]
fn test_fun_context_with_let() {
    let mut ctx = Context::new();
    ctx.ensure_logic();

    let int = ctx.int_sort();
    let mut f_ctx = ctx
        .build_fun_out_sort("compute", [("x", int.clone()), ("y", int.clone())], int)
        .unwrap();
    let x = f_ctx.typed_symbol("x").unwrap();
    let y = f_ctx.typed_symbol("y").unwrap();
    let sum = f_ctx.typed_simp_app("+", [x.clone(), y.clone()]).unwrap();
    let mut let_ctx = f_ctx.build_let([("z", sum)]).unwrap();
    let z = let_ctx.typed_symbol("z").unwrap();
    let body = let_ctx.typed_simp_app("*", [z, x]).unwrap();
    let let_term = let_ctx.typed_let(body);
    let cmd = f_ctx.typed_define_fun(let_term).unwrap();

    assert_eq!(
        cmd.to_string(),
        "(define-fun compute ((x Int) (y Int)) Int (let ((z (+ x y))) (* z x)))"
    );
}

#[test]
fn test_fun_context_with_quantifier() {
    let mut ctx = Context::new();
    ctx.ensure_logic();

    let int = ctx.int_sort();
    let bool = ctx.bool_sort();
    let mut f_ctx = ctx
        .build_fun_out_sort("all_positive", [("x", int)], bool)
        .unwrap();
    let mut q_ctx = f_ctx.build_quantifier().unwrap();
    let cmp = UntypedAst
        .parse_term_str("(> x 0)")
        .unwrap()
        .type_check(&mut q_ctx)
        .unwrap();
    let forall = q_ctx.typed_forall(cmp).unwrap();
    let cmd = f_ctx.typed_define_fun(forall).unwrap();

    assert_eq!(
        cmd.to_string(),
        "(define-fun all_positive ((x Int)) Bool (forall () (> x 0)))"
    );
}

#[test]
fn test_fun_context_with_matching() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-datatype Bool2 ((true2) (false2)))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let bool2 = ctx.wf_sort("Bool2").unwrap();
    let int = ctx.int_sort();
    let mut f_ctx = ctx
        .build_fun_out_sort("bool2_to_int", [("b", bool2)], int)
        .unwrap();
    let b = f_ctx.typed_symbol("b").unwrap();
    let one = f_ctx.numeral(UBig::from(1u8)).unwrap();
    let zero = f_ctx.numeral(UBig::from(0u8)).unwrap();
    let mut m_ctx = f_ctx.build_matching(b).unwrap();

    let true_ctx = m_ctx.build_arm_nullary("true2").unwrap();
    true_ctx.typed_arm(one).unwrap();

    let false_ctx = m_ctx.build_arm_nullary("false2").unwrap();
    false_ctx.typed_arm(zero).unwrap();

    let match_term = m_ctx.typed_matching().unwrap();
    let cmd = f_ctx.typed_define_fun(match_term).unwrap();

    assert_eq!(
        cmd.to_string(),
        "(define-fun bool2_to_int ((b Bool2)) Int (match b ((true2 1) (false2 0))))"
    );
}

#[test]
fn test_matching_scrutinee_sort() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-datatype Color ((red) (green)))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let color = ctx.wf_sort("Color").unwrap();
    let mut q_ctx = ctx
        .build_quantifier_with_domain([("c", color.clone())])
        .unwrap();
    let c = q_ctx.typed_symbol("c").unwrap();
    let mut m_ctx = q_ctx.build_matching(c).unwrap();

    let sort = m_ctx.scrutinee_sort();
    assert_eq!(sort.to_string(), "Color");
}

#[test]
fn test_matching_is_covered() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-datatype Bit ((zero) (one)))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let bit = ctx.wf_sort("Bit").unwrap();
    let mut q_ctx = ctx.build_quantifier_with_domain([("b", bit)]).unwrap();
    let b = q_ctx.typed_symbol("b").unwrap();
    let val = q_ctx.numeral(UBig::from(0u8)).unwrap();
    let mut m_ctx = q_ctx.build_matching(b).unwrap();

    assert!(!m_ctx.is_covered());

    let zero_ctx = m_ctx.build_arm_nullary("zero").unwrap();
    zero_ctx.typed_arm(val.clone()).unwrap();

    assert!(!m_ctx.is_covered());

    let one_ctx = m_ctx.build_arm_nullary("one").unwrap();
    one_ctx.typed_arm(val).unwrap();

    assert!(m_ctx.is_covered());
}

#[test]
fn test_matching_get_unseen_constructors() {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-datatype Tri ((a) (b) (c)))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let tri = ctx.wf_sort("Tri").unwrap();
    let a_sym = ctx.allocate_symbol("a");
    let mut q_ctx = ctx.build_quantifier_with_domain([("t", tri)]).unwrap();
    let t = q_ctx.typed_symbol("t").unwrap();
    let val = q_ctx.numeral(UBig::from(0u8)).unwrap();
    let mut m_ctx = q_ctx.build_matching(t).unwrap();

    assert_eq!(m_ctx.get_unseen_constructors().len(), 3);

    let a_ctx = m_ctx.build_arm_nullary("a").unwrap();
    a_ctx.typed_arm(val).unwrap();

    let unseen = m_ctx.get_unseen_constructors();
    assert_eq!(unseen.len(), 2);
    assert!(!unseen.contains(&a_sym));
}
