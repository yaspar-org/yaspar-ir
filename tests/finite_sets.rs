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
