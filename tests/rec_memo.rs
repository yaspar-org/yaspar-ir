// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use yaspar::ast::Keyword;
use yaspar_ir::ast::Typecheck;
use yaspar_ir::ast::alg::{
    Attribute, Constant, Local, PatternArm, QualifiedIdentifier, VarBinding,
};
use yaspar_ir::ast::{Bottom, Context, Memoize, Sort, Str, Term, TermRecursor, TypedTermRecursor};
use yaspar_ir::untyped::UntypedAst;

struct TouchedTermSize {
    /// count the touched subterms; side effect to poke whether cache is hit
    counter: u128,
}

impl TermRecursor<Str, Sort, Term> for TouchedTermSize {
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
        self.counter += 1;
        Ok(1)
    }

    fn on_global(
        &mut self,
        _current: &Term,
        _id: &QualifiedIdentifier<Str, Sort>,
        _sort: &Option<Sort>,
    ) -> Result<Self::Out, Self::Err> {
        self.counter += 1;
        Ok(1)
    }

    fn on_local(
        &mut self,
        _current: &Term,
        _id: &Local<Str, Sort>,
    ) -> Result<Self::Out, Self::Err> {
        self.counter += 1;
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
        self.counter += 1;
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
        self.counter += 1;
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
        self.counter += 1;
        Ok(1 + t_rec)
    }

    fn on_forall(
        &mut self,
        _current: &Term,
        _vs: &[VarBinding<Str, Sort>],
        _t: &Term,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        self.counter += 1;
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
        current: &T,
        scrutinee: &T,
        cases: &[PatternArm<Str, T>],
        scrutinee_rec: &Self::Out,
        case_idx: usize,
        current_pattern: Self::Pattern,
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
        self.counter += 1;
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
        self.counter += 1;
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
        self.counter += 1;
        Ok(1 + a_rec + b_rec)
    }

    fn on_distinct(
        &mut self,
        _current: &Term,
        _ts: &[Term],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        self.counter += 1;
        Ok(1 + ts_rec.into_iter().sum::<usize>())
    }

    fn on_and(
        &mut self,
        _current: &Term,
        _ts: &[Term],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        self.counter += 1;
        Ok(1 + ts_rec.into_iter().sum::<usize>())
    }

    fn on_or(
        &mut self,
        _current: &Term,
        _ts: &[Term],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        self.counter += 1;
        Ok(1 + ts_rec.into_iter().sum::<usize>())
    }

    fn on_xor(
        &mut self,
        _current: &Term,
        _ts: &[Term],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        self.counter += 1;
        Ok(1 + ts_rec.into_iter().sum::<usize>())
    }

    fn on_not(
        &mut self,
        _current: &Term,
        _t: &Term,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        self.counter += 1;
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
        self.counter += 1;
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
        self.counter += 1;
        Ok(1 + b_rec + t_rec + e_rec)
    }
}

impl TypedTermRecursor for TouchedTermSize {}

fn test_term_size(t: &Term, expected: usize, expected_cache_size: usize) {
    let other_recursor = TouchedTermSize { counter: 0 };
    // memoization happens just by wrapping on top of another recursor!
    let mut recursor = Memoize::new(other_recursor);
    // memoization is automagic during recursion
    let sz = recursor.recurse_on_term(t).unwrap();
    assert_eq!(sz, expected);
    assert_eq!(recursor.cache.len(), expected_cache_size);
    // cache can be inherited
    // see how we can just pass in a reference to the previous cache, instead of a new cache
    let mut recursor = Memoize::with_cache(TouchedTermSize { counter: 0 }, &mut recursor.cache);
    let sz = recursor.recurse_on_term(t).unwrap();
    assert_eq!(sz, expected);
    // cache should hit, so no subterm is touched
    assert_eq!(recursor.inner.counter, 0);
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

fn parse_term(ctx: &mut Context, s: &str) -> Term {
    UntypedAst
        .parse_term_str(s)
        .unwrap()
        .type_check(ctx)
        .unwrap()
}

#[test]
fn test_memo_constant() {
    let mut ctx = setup("(set-logic ALL)");
    test_term_size(&parse_term(&mut ctx, "42"), 1, 1);
    test_term_size(&parse_term(&mut ctx, "true"), 1, 1);
}

#[test]
fn test_memo_global() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)");
    test_term_size(&parse_term(&mut ctx, "x"), 1, 1);
}

#[test]
fn test_memo_app() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)(declare-const y Int)");
    test_term_size(&parse_term(&mut ctx, "(+ x y)"), 3, 3);
    test_term_size(&parse_term(&mut ctx, "(+ x y 1)"), 4, 4);
}

#[test]
fn test_memo_not() {
    let mut ctx = setup("(set-logic ALL)(declare-const p Bool)");
    test_term_size(&parse_term(&mut ctx, "(not p)"), 2, 2);
}

#[test]
fn test_memo_and_or() {
    let mut ctx = setup("(set-logic ALL)(declare-const p Bool)(declare-const q Bool)");
    test_term_size(&parse_term(&mut ctx, "(and p q)"), 3, 3);
    test_term_size(&parse_term(&mut ctx, "(or p q)"), 3, 3);
}

#[test]
fn test_memo_eq() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)(declare-const y Int)");
    test_term_size(&parse_term(&mut ctx, "(= x y)"), 3, 3);
}

#[test]
fn test_memo_ite() {
    let mut ctx =
        setup("(set-logic ALL)(declare-const p Bool)(declare-const x Int)(declare-const y Int)");
    test_term_size(&parse_term(&mut ctx, "(ite p x y)"), 4, 4);
}

#[test]
fn test_memo_let() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)");
    test_term_size(&parse_term(&mut ctx, "(let ((y (+ x 1))) (+ y y))"), 7, 6);
}

#[test]
fn test_memo_forall() {
    let mut ctx = setup("(set-logic ALL)");
    test_term_size(&parse_term(&mut ctx, "(forall ((x Int)) (= x 0))"), 4, 4);
}

#[test]
fn test_memo_exists() {
    let mut ctx = setup("(set-logic ALL)");
    test_term_size(&parse_term(&mut ctx, "(exists ((x Int)) (= x 0))"), 4, 4);
}

#[test]
fn test_memo_nested() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)(declare-const y Int)");
    test_term_size(&parse_term(&mut ctx, "(+ (+ x y) 1)"), 5, 5);
    test_term_size(&parse_term(&mut ctx, "(not (= (+ x 1) y))"), 6, 6);
}

#[test]
fn test_memo_match() {
    let mut ctx = setup(
        "(set-logic ALL)
             (declare-datatype List (par (X) ((nil) (cons (car X) (cdr (List X))))))
             (declare-const l (List Int))",
    );
    test_term_size(
        &parse_term(&mut ctx, "(match l ((nil 0) ((cons h t) h)))"),
        4,
        4,
    );
}

#[test]
fn test_memo_annotated() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)");
    test_term_size(&parse_term(&mut ctx, "(! x :named foo)"), 3, 2);
}

#[test]
fn test_memo_deep_not() {
    let mut ctx = setup("(set-logic ALL)(declare-const p Bool)");
    // (not (not (not ... (not p) ...))) — 10 layers of not + 1 leaf = 11
    let term = "(not (not (not (not (not (not (not (not (not (not p))))))))))";
    test_term_size(&parse_term(&mut ctx, term), 11, 11);
}

#[test]
fn test_memo_deep_add() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)");
    // (+ (+ (+ ... (+ x 1) ... 1) 1) 1) — 10 apps, each with a numeral + nested child = 10*2 + 1 = 21
    let term = "(+ (+ (+ (+ (+ (+ (+ (+ (+ (+ x 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)";
    test_term_size(&parse_term(&mut ctx, term), 21, 12);
}

#[test]
fn test_memo_deep_ite() {
    let mut ctx =
        setup("(set-logic ALL)(declare-const p Bool)(declare-const x Int)(declare-const y Int)");
    // 10 nested ites: each ite node + condition p + else y = 3 overhead, plus the nested then-branch
    // size = 10 * 3 + 1 (innermost x) = 31
    let term = "(ite p (ite p (ite p (ite p (ite p (ite p (ite p (ite p (ite p (ite p x y) y) y) y) y) y) y) y) y) y)";
    test_term_size(&parse_term(&mut ctx, term), 31, 13);
}

#[test]
fn test_memo_deep_and() {
    let mut ctx = setup("(set-logic ALL)(declare-const p Bool)(declare-const q Bool)");
    // (and (and (and ... (and p q) ... q) q) q) — 10 ands, each with q + nested child = 10*2 + 1 = 21
    let term = "(and (and (and (and (and (and (and (and (and (and p q) q) q) q) q) q) q) q) q) q)";
    test_term_size(&parse_term(&mut ctx, term), 21, 12);
}

#[test]
fn test_memo_deep_let() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)");
    // 10 nested lets, each binding a fresh variable to 0, innermost body is (+ x 0)
    // each let = 1 (let) + 1 (binding rhs 0) = 2 overhead, plus nested body
    // size = 10 * 2 + 3 (+ x 0) = 23
    let term = "\
        (let ((a 0)) \
        (let ((b 0)) \
        (let ((c 0)) \
        (let ((d 0)) \
        (let ((e 0)) \
        (let ((f 0)) \
        (let ((g 0)) \
        (let ((h 0)) \
        (let ((i 0)) \
        (let ((j 0)) \
        (+ x 0)\
        ))))))))))";
    test_term_size(&parse_term(&mut ctx, term), 23, 13);
}

/// Like `test_term_size`, but also asserts the number of touched nodes on the first
/// traversal. When sub-terms are shared via hashconsing, the cache is hit during the
/// first pass, so `expected_touched` can be less than `expected_size`.
fn test_term_size_with_hits(
    t: &Term,
    expected_size: usize,
    expected_cache_size: usize,
    expected_touched: usize,
) {
    let mut recursor = Memoize::new(TouchedTermSize { counter: 0 });
    let sz = recursor.recurse_on_term(t).unwrap();
    assert_eq!(sz, expected_size);
    assert_eq!(recursor.cache.len(), expected_cache_size);
    assert_eq!(recursor.inner.counter as usize, expected_touched);
}

#[test]
fn test_memo_shared_and() {
    // (and (> x 0) (> x 0)) — the two arguments are identical hashconsed terms.
    // term size = 1 (and) + 3 (> x 0) + 3 (> x 0) = 7
    // but the second (> x 0) is a cache hit, so only 4 unique nodes are touched.
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)");
    let t = parse_term(&mut ctx, "(and (> x 0) (> x 0))");
    test_term_size_with_hits(&t, 7, 4, 4);
}

#[test]
fn test_memo_shared_eq() {
    // (= (+ x y) (+ x y)) — both sides are the same hashconsed term.
    // term size = 1 (=) + 3 (+ x y) + 3 (+ x y) = 7
    // cache hits on the second (+ x y), so 4 unique nodes touched.
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)(declare-const y Int)");
    let t = parse_term(&mut ctx, "(= (+ x y) (+ x y))");
    test_term_size_with_hits(&t, 7, 4, 4);
}

#[test]
fn test_memo_shared_ite_branches() {
    // (ite p (+ x 1) (+ x 1)) — both branches are the same hashconsed term.
    // term size = 1 (ite) + 1 (p) + 3 (+ x 1) + 3 (+ x 1) = 8
    // cache hits on the second (+ x 1), so 5 unique nodes touched.
    let mut ctx = setup("(set-logic ALL)(declare-const p Bool)(declare-const x Int)");
    let t = parse_term(&mut ctx, "(ite p (+ x 1) (+ x 1))");
    test_term_size_with_hits(&t, 8, 5, 5);
}

#[test]
fn test_memo_shared_nested() {
    // (and (or p q) (or p q) (or p q)) — three identical sub-terms.
    // term size = 1 (and) + 3 * 3 (or p q) = 10
    // only the first (or p q) is traversed; the other two are cache hits.
    // unique nodes touched = 1 (and) + 3 (or p q) = 4
    let mut ctx = setup("(set-logic ALL)(declare-const p Bool)(declare-const q Bool)");
    let t = parse_term(&mut ctx, "(and (or p q) (or p q) (or p q))");
    test_term_size_with_hits(&t, 10, 4, 4);
}

#[test]
fn test_memo_shared_deep() {
    // (and (not (not (not p))) (not (not (not p)))) — two identical deep sub-terms.
    // term size = 1 (and) + 4 (not (not (not p))) + 4 = 9
    // second branch is a full cache hit, so 5 unique nodes touched.
    let mut ctx = setup("(set-logic ALL)(declare-const p Bool)");
    let t = parse_term(&mut ctx, "(and (not (not (not p))) (not (not (not p))))");
    test_term_size_with_hits(&t, 9, 5, 5);
}
