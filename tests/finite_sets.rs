// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#![cfg(feature = "finite-set")]

use yaspar_ir::ast::*;
use yaspar_ir::untyped::UntypedAst;

fn check(script: &str) {
    let mut ctx = Context::new();
    let cs = UntypedAst.parse_script_str(script).unwrap();
    cs.type_check(&mut ctx).unwrap();
}

fn check_err(script: &str) {
    let mut ctx = Context::new();
    let cs = UntypedAst.parse_script_str(script).unwrap();
    assert!(cs.type_check(&mut ctx).is_err());
}

#[test]
fn test_set_union() {
    check(
        r"
(set-logic QF_LIAFS)
(declare-const a (Set Int))
(declare-const b (Set Int))
(assert (= (set.union a b) a))
(check-sat)
",
    );
}

#[test]
fn test_set_inter() {
    check(
        r"
(set-logic QF_LIAFS)
(declare-const a (Set Int))
(declare-const b (Set Int))
(assert (= (set.inter a b) b))
(check-sat)
",
    );
}

#[test]
fn test_set_minus() {
    check(
        r"
(set-logic QF_LIAFS)
(declare-const a (Set Int))
(declare-const b (Set Int))
(assert (= (set.minus a b) a))
(check-sat)
",
    );
}

#[test]
fn test_set_complement() {
    check(
        r"
(set-logic QF_LIAFS)
(declare-const a (Set Int))
(assert (= (set.complement a) a))
(check-sat)
",
    );
}

#[test]
fn test_set_member() {
    check(
        r"
(set-logic QF_LIAFS)
(declare-const x Int)
(declare-const a (Set Int))
(assert (set.member x a))
(check-sat)
",
    );
}

#[test]
fn test_set_subset() {
    check(
        r"
(set-logic QF_LIAFS)
(declare-const a (Set Int))
(declare-const b (Set Int))
(assert (set.subset a b))
(check-sat)
",
    );
}

#[test]
fn test_set_empty() {
    check(
        r"
(set-logic QF_LIAFS)
(declare-const a (Set Int))
(assert (= a (as set.empty (Set Int))))
(check-sat)
",
    );
}

#[test]
fn test_set_universe() {
    check(
        r"
(set-logic QF_LIAFS)
(declare-const a (Set Int))
(assert (= a (as set.universe (Set Int))))
(check-sat)
",
    );
}

#[test]
fn test_set_singleton() {
    check(
        r"
(set-logic QF_LIAFS)
(declare-const a (Set Int))
(assert (= a (set.singleton 1)))
(check-sat)
",
    );
}

#[test]
fn test_set_card() {
    check(
        r"
(set-logic QF_LIAFS)
(declare-const a (Set Int))
(assert (= (set.card a) 3))
(check-sat)
",
    );
}

#[test]
fn test_set_member_wrong_sort() {
    check_err(
        r"
(set-logic QF_LIAFS)
(declare-const a (Set Int))
(declare-const x Bool)
(assert (set.member x a))
(check-sat)
",
    );
}

#[test]
fn test_set_union_wrong_sort() {
    check_err(
        r"
(set-logic QF_LIAFS)
(declare-const a (Set Int))
(declare-const x Int)
(assert (= (set.union a x) a))
(check-sat)
",
    );
}

#[test]
fn test_set_combined() {
    check(
        r"
(set-logic QF_LIAFS)
(declare-const a (Set Int))
(declare-const b (Set Int))
(declare-const x Int)
(assert (set.member x (set.union a b)))
(assert (set.subset (set.inter a b) a))
(assert (= (set.card (set.minus a b)) 2))
(assert (= (set.complement (as set.empty (Set Int))) (as set.universe (Set Int))))
(check-sat)
",
    );
}

/// ATSLIB's finite sets, in `ALL`, have six operations (#182). The other four are left out: they
/// are not declared, so a script may declare them itself.
#[test]
fn test_atslib_finite_set_operations() {
    let run = |script: &str| {
        let cs = UntypedAst.parse_script_str(script).unwrap();
        cs.type_check(&mut Context::<AtsLib>::new_dialect())
            .map(|_| ())
    };
    let decls = "(set-logic ALL)(declare-const a (Set Int))(declare-const b (Set Int))\
        (declare-const x Int)";
    for t in [
        "(= (set.union a b) a)",
        "(= (set.inter a b) a)",
        "(set.member x a)",
        "(set.subset a b)",
        "(= (as set.empty (Set Int)) a)",
        "(= (set.singleton x) a)",
    ] {
        let script = format!("{decls}(assert {t})");
        assert_eq!(run(&script), Ok(()), "{t}");
    }
    for t in [
        "(= (set.minus a b) a)",
        "(= (set.complement a) a)",
        "(= (as set.universe (Set Int)) a)",
        "(= (set.card a) 0)",
    ] {
        let script = format!("{decls}(assert {t})");
        let err = run(&script).unwrap_err();
        assert!(
            err.contains("not declared") || err.contains("does not exist"),
            "{t}: {err}"
        );
    }
    let declared =
        format!("{decls}(declare-fun set.card ((Set Int)) Int)(assert (= (set.card a) 0))");
    assert_eq!(run(&declared), Ok(()));
}

/// SMT-LIB keeps all ten operations.
#[test]
fn test_smtlib_finite_set_operations() {
    let script = "(set-logic ALL)(declare-const a (Set Int))(declare-const b (Set Int))\
        (assert (= (set.minus a b) (set.complement a)))\
        (assert (= (set.card a) 0))(assert (= (as set.universe (Set Int)) a))";
    let cs = UntypedAst.parse_script_str(script).unwrap();
    assert!(cs.type_check(&mut Context::<SmtLib>::new_dialect()).is_ok());
}
