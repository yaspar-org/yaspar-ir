// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use yaspar::ast::Keyword;
use yaspar_ir::ast::alg::{
    Attribute, Constant, Local, PatternArm, QualifiedIdentifier, VarBinding,
};
use yaspar_ir::ast::{Bottom, CheckedApi, Context, Typecheck};
use yaspar_ir::ast::{
    ObjectAllocatorExt, Sort, Str, StrAllocator, Term, TermAllocator, TermRecursor,
    TypedTermRecursor,
};
use yaspar_ir::untyped::UntypedAst;

struct TermSize;

impl TermRecursor<Str, Sort, Term> for TermSize {
    type Out = usize;
    type Attr = usize;
    type Binding = usize;
    type Pattern = ();
    type Arm = usize;
    type Err = Bottom;

    fn on_constant(
        &mut self,
        _current: &Term,
        _constant: &Constant<Str>,
        _sort: &Option<Sort>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1)
    }

    fn on_global(
        &mut self,
        _current: &Term,
        _id: &QualifiedIdentifier<Str, Sort>,
        _sort: &Option<Sort>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1)
    }

    fn on_local(
        &mut self,
        _current: &Term,
        _id: &Local<Str, Sort>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1)
    }

    fn on_app(
        &mut self,
        _current: &Term,
        _id: &QualifiedIdentifier<Str, Sort>,
        _ts: &[Term],
        _s: &Option<Sort>,
        recs: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + recs.into_iter().sum::<usize>())
    }

    fn on_let_binding(
        &mut self,
        _current: &Term,
        _vs: &[VarBinding<Str, Term>],
        _body: &Term,
        _binding_idx: usize,
        binding_rec: Self::Out,
    ) -> Result<Self::Binding, Self::Err> {
        Ok(binding_rec)
    }

    fn setup_let_scope(
        &mut self,
        _current: &Term,
        _vs: &[VarBinding<Str, Term>],
        _body: &Term,
        _vs_rec: &[Self::Out],
    ) -> Result<(), Self::Err> {
        Ok(())
    }

    fn on_let(
        &mut self,
        _current: &Term,
        _vs: &[VarBinding<Str, Term>],
        _body: &Term,
        vs_rec: Vec<Self::Out>,
        body_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + vs_rec.into_iter().sum::<usize>() + body_rec)
    }

    fn setup_quantifier_scope(
        &mut self,
        _current: &Term,
        _vs: &[VarBinding<Str, Sort>],
        _t: &Term,
        _is_forall: bool,
    ) -> Result<(), Self::Err> {
        Ok(())
    }

    fn on_exists(
        &mut self,
        _current: &Term,
        _vs: &[VarBinding<Str, Sort>],
        _t: &Term,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + t_rec)
    }

    fn on_forall(
        &mut self,
        _current: &Term,
        _vs: &[VarBinding<Str, Sort>],
        _t: &Term,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + t_rec)
    }

    fn setup_match_case_scope(
        &mut self,
        _current: &Term,
        _scrutinee: &Term,
        _cases: &[PatternArm<Str, Term>],
        _scrutinee_rec: &Self::Out,
        _case_idx: usize,
    ) -> Result<(), Self::Err> {
        Ok(())
    }

    fn on_match_arm(
        &mut self,
        _current: &Term,
        _scrutinee: &Term,
        _cases: &[PatternArm<Str, Term>],
        _scrutinee_rec: &Self::Out,
        _case_idx: usize,
        _current_pattern: Self::Pattern,
        arm: Self::Out,
    ) -> Result<Self::Arm, Self::Err> {
        Ok(arm)
    }

    fn on_match(
        &mut self,
        _current: &Term,
        _scrutinee: &Term,
        _cases: &[PatternArm<Str, Term>],
        scrutinee_rec: Self::Out,
        cases_rec: Vec<Self::Arm>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + scrutinee_rec + cases_rec.into_iter().sum::<usize>())
    }

    fn on_annotated(
        &mut self,
        _current: &Term,
        _t: &Term,
        _anns: &[Attribute<Str, Term>],
        t_rec: Self::Out,
        anns_rec: Vec<Self::Attr>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + t_rec + anns_rec.into_iter().sum::<usize>())
    }

    fn on_attribute_keyword(&mut self, _keyword: &Keyword) -> Result<Self::Attr, Self::Err> {
        Ok(1)
    }

    fn on_attribute_constant(
        &mut self,
        _keyword: &Keyword,
        _constant: &Constant<Str>,
    ) -> Result<Self::Attr, Self::Err> {
        Ok(1)
    }

    fn on_attribute_symbol(
        &mut self,
        _keyword: &Keyword,
        _symbol: &Str,
    ) -> Result<Self::Attr, Self::Err> {
        Ok(1)
    }

    fn on_attribute_named(&mut self, _name: &Str) -> Result<Self::Attr, Self::Err> {
        Ok(1)
    }

    fn on_attribute_pattern(
        &mut self,
        _patterns: &[Term],
        patterns_rec: Vec<Self::Out>,
    ) -> Result<Self::Attr, Self::Err> {
        Ok(patterns_rec.into_iter().sum::<usize>())
    }

    fn on_eq(
        &mut self,
        _current: &Term,
        _a: &Term,
        _b: &Term,
        a_rec: Self::Out,
        b_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + a_rec + b_rec)
    }

    fn on_distinct(
        &mut self,
        _current: &Term,
        _ts: &[Term],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + ts_rec.into_iter().sum::<usize>())
    }

    fn on_and(
        &mut self,
        _current: &Term,
        _ts: &[Term],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + ts_rec.into_iter().sum::<usize>())
    }

    fn on_or(
        &mut self,
        _current: &Term,
        _ts: &[Term],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + ts_rec.into_iter().sum::<usize>())
    }

    fn on_xor(
        &mut self,
        _current: &Term,
        _ts: &[Term],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + ts_rec.into_iter().sum::<usize>())
    }

    fn on_not(
        &mut self,
        _current: &Term,
        _t: &Term,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + t_rec)
    }

    fn on_implies(
        &mut self,
        _current: &Term,
        _ts: &[Term],
        _t: &Term,
        ts_rec: Vec<Self::Out>,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + ts_rec.into_iter().sum::<usize>() + t_rec)
    }

    fn on_ite(
        &mut self,
        _current: &Term,
        _b: &Term,
        _t: &Term,
        _e: &Term,
        b_rec: Self::Out,
        t_rec: Self::Out,
        e_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + b_rec + t_rec + e_rec)
    }
}

impl TypedTermRecursor for TermSize {}

fn size(ctx: &mut Context, s: &str) -> usize {
    let t = UntypedAst
        .parse_term_str(s)
        .unwrap()
        .type_check(ctx)
        .unwrap();
    match TermSize.recurse_on_term(&t) {
        Ok(n) => n,
        Err(b) => match b {},
    }
}

fn setup(script: &str) -> Context {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(script)
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    ctx
}

#[test]
fn test_constant() {
    let mut ctx = setup("(set-logic ALL)");
    assert_eq!(size(&mut ctx, "42"), 1);
    assert_eq!(size(&mut ctx, "true"), 1);
}

#[test]
fn test_global() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)");
    assert_eq!(size(&mut ctx, "x"), 1);
}

#[test]
fn test_app() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)(declare-const y Int)");
    // (+ x y) = 1 (app) + 1 (x) + 1 (y) = 3
    assert_eq!(size(&mut ctx, "(+ x y)"), 3);
    // (+ x y 1) = 1 + 1 + 1 + 1 = 4
    assert_eq!(size(&mut ctx, "(+ x y 1)"), 4);
}

#[test]
fn test_not() {
    let mut ctx = setup("(set-logic ALL)(declare-const p Bool)");
    // (not p) = 1 (not) + 1 (p) = 2
    assert_eq!(size(&mut ctx, "(not p)"), 2);
}

#[test]
fn test_and_or() {
    let mut ctx = setup("(set-logic ALL)(declare-const p Bool)(declare-const q Bool)");
    // (and p q) = 1 + 1 + 1 = 3
    assert_eq!(size(&mut ctx, "(and p q)"), 3);
    assert_eq!(size(&mut ctx, "(or p q)"), 3);
}

#[test]
fn test_xor() {
    let mut ctx = setup("(set-logic ALL)(declare-const p Bool)(declare-const q Bool)");
    assert_eq!(size(&mut ctx, "(xor p q)"), 3);
}

#[test]
fn test_implies() {
    let mut ctx = setup("(set-logic ALL)(declare-const p Bool)(declare-const q Bool)");
    // (=> p q) = 1 + 1 + 1 = 3
    assert_eq!(size(&mut ctx, "(=> p q)"), 3);
}

#[test]
fn test_eq() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)(declare-const y Int)");
    // (= x y) = 1 + 1 + 1 = 3
    assert_eq!(size(&mut ctx, "(= x y)"), 3);
}

#[test]
fn test_distinct() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)(declare-const y Int)");
    assert_eq!(size(&mut ctx, "(distinct x y)"), 3);
}

#[test]
fn test_ite() {
    let mut ctx =
        setup("(set-logic ALL)(declare-const p Bool)(declare-const x Int)(declare-const y Int)");
    // (ite p x y) = 1 + 1 + 1 + 1 = 4
    assert_eq!(size(&mut ctx, "(ite p x y)"), 4);
}

#[test]
fn test_let() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)");
    // (let ((y (+ x 1))) (+ y y)) = 1 (let) + 3 (+ x 1) + 3 (+ y y) = 7
    assert_eq!(size(&mut ctx, "(let ((y (+ x 1))) (+ y y))"), 7);
}

#[test]
fn test_forall() {
    let mut ctx = setup("(set-logic ALL)");
    // (forall ((x Int)) (= x 0)) = 1 (forall) + 3 (= x 0) = 4
    assert_eq!(size(&mut ctx, "(forall ((x Int)) (= x 0))"), 4);
}

#[test]
fn test_exists() {
    let mut ctx = setup("(set-logic ALL)");
    assert_eq!(size(&mut ctx, "(exists ((x Int)) (= x 0))"), 4);
}

#[test]
fn test_nested() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)(declare-const y Int)");
    // (+ (+ x y) 1) = 1 + (1 + 1 + 1) + 1 = 5
    assert_eq!(size(&mut ctx, "(+ (+ x y) 1)"), 5);
    // (not (= (+ x 1) y)) = 1 + (1 + (1 + 1 + 1) + 1) = 6
    assert_eq!(size(&mut ctx, "(not (= (+ x 1) y))"), 6);
}

#[test]
fn test_match() {
    let mut ctx = setup(
        "(set-logic ALL)
             (declare-datatype List (par (X) ((nil) (cons (car X) (cdr (List X))))))
             (declare-const l (List Int))",
    );
    // (match l ((nil 0) ((cons h t) h)))
    // = 1 (match) + 1 (scrutinee l) + 1 (nil arm: 0) + 1 (cons arm: h) = 4
    assert_eq!(size(&mut ctx, "(match l ((nil 0) ((cons h t) h)))"), 4,);
}

#[test]
fn test_annotated() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)");
    // (! x :named foo) = 1 (annotated) + 1 (x) + 1 (:named) = 3
    assert_eq!(size(&mut ctx, "(! x :named foo)"), 3);
}

fn term_size(t: &Term) -> usize {
    match TermSize.recurse_on_term(t) {
        Ok(n) => n,
        Err(b) => match b {},
    }
}

#[test]
fn test_empty_and() {
    let mut ctx = setup("(set-logic ALL)");
    let t = ctx.and(vec![]);
    assert_eq!(term_size(&t), 1);
}

#[test]
fn test_empty_or() {
    let mut ctx = setup("(set-logic ALL)");
    let t = ctx.or(vec![]);
    assert_eq!(term_size(&t), 1);
}

#[test]
fn test_empty_distinct() {
    let mut ctx = setup("(set-logic ALL)");
    let t = ctx.distinct(vec![]);
    assert_eq!(term_size(&t), 1);
}

#[test]
fn test_empty_xor() {
    let mut ctx = setup("(set-logic ALL)");
    let t = ctx.xor(vec![]);
    assert_eq!(term_size(&t), 1);
}

#[test]
fn test_empty_implies() {
    let mut ctx = setup("(set-logic ALL)(declare-const p Bool)");
    let p = UntypedAst
        .parse_term_str("p")
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let t = ctx.implies(vec![], p);
    assert_eq!(term_size(&t), 2);
}

#[test]
fn test_empty_app() {
    let mut ctx = setup("(set-logic ALL)");
    let bool_sort = ctx.bool_sort();
    let f = ctx.allocate_symbol("f");
    let t = ctx.app(QualifiedIdentifier::simple(f), vec![], Some(bool_sort));
    assert_eq!(term_size(&t), 1);
}

#[test]
fn test_empty_let() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)");
    let x = UntypedAst
        .parse_term_str("x")
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    let t = ctx.let_term(vec![], x);
    assert_eq!(term_size(&t), 2);
}

#[test]
fn test_empty_match() {
    let mut ctx = setup(
        "(set-logic ALL)
         (declare-datatype List (par (X) ((nil) (cons (car X) (cdr (List X))))))
         (declare-const l (List Int))",
    );
    let l = ctx.typed_symbol("l").unwrap();
    let t = ctx.matching(l, vec![]);
    assert_eq!(term_size(&t), 2);
}
