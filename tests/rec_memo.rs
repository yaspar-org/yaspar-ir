use yaspar::ast::Keyword;
use yaspar_ir::ast::Typecheck;
use yaspar_ir::ast::alg::{
    Attribute, Constant, Local, PatternArm, QualifiedIdentifier, VarBinding,
};
use yaspar_ir::ast::{Bottom, Context, Memoize, Sort, Str, Term, TermRecursor, TypedTermRecursor};
use yaspar_ir::untyped::UntypedAst;

struct TouchedTermSize {
    /// count the touched subterms; side effect to poke wheather cache is hit
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
        _current: &Term,
        _scrutinee: &Term,
        _cases: &[PatternArm<Str, Term>],
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

fn test_term_size(t: &Term, expected: usize) {
    let other_recursor = TouchedTermSize { counter: 0 };
    // memoization happens just by wrapping on top of another recursor!
    let mut recursor = Memoize::new(other_recursor);
    // memoization is automagic during recursion
    let sz = recursor.recurse_on_term(t).unwrap();
    assert_eq!(sz, expected);
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
    test_term_size(&parse_term(&mut ctx, "42"), 1);
    test_term_size(&parse_term(&mut ctx, "true"), 1);
}

#[test]
fn test_memo_global() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)");
    test_term_size(&parse_term(&mut ctx, "x"), 1);
}

#[test]
fn test_memo_app() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)(declare-const y Int)");
    test_term_size(&parse_term(&mut ctx, "(+ x y)"), 3);
    test_term_size(&parse_term(&mut ctx, "(+ x y 1)"), 4);
}

#[test]
fn test_memo_not() {
    let mut ctx = setup("(set-logic ALL)(declare-const p Bool)");
    test_term_size(&parse_term(&mut ctx, "(not p)"), 2);
}

#[test]
fn test_memo_and_or() {
    let mut ctx = setup("(set-logic ALL)(declare-const p Bool)(declare-const q Bool)");
    test_term_size(&parse_term(&mut ctx, "(and p q)"), 3);
    test_term_size(&parse_term(&mut ctx, "(or p q)"), 3);
}

#[test]
fn test_memo_eq() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)(declare-const y Int)");
    test_term_size(&parse_term(&mut ctx, "(= x y)"), 3);
}

#[test]
fn test_memo_ite() {
    let mut ctx =
        setup("(set-logic ALL)(declare-const p Bool)(declare-const x Int)(declare-const y Int)");
    test_term_size(&parse_term(&mut ctx, "(ite p x y)"), 4);
}

#[test]
fn test_memo_let() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)");
    test_term_size(&parse_term(&mut ctx, "(let ((y (+ x 1))) (+ y y))"), 7);
}

#[test]
fn test_memo_forall() {
    let mut ctx = setup("(set-logic ALL)");
    test_term_size(&parse_term(&mut ctx, "(forall ((x Int)) (= x 0))"), 4);
}

#[test]
fn test_memo_exists() {
    let mut ctx = setup("(set-logic ALL)");
    test_term_size(&parse_term(&mut ctx, "(exists ((x Int)) (= x 0))"), 4);
}

#[test]
fn test_memo_nested() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)(declare-const y Int)");
    test_term_size(&parse_term(&mut ctx, "(+ (+ x y) 1)"), 5);
    test_term_size(&parse_term(&mut ctx, "(not (= (+ x 1) y))"), 6);
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
    );
}

#[test]
fn test_memo_annotated() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)");
    test_term_size(&parse_term(&mut ctx, "(! x :named foo)"), 3);
}

#[test]
fn test_memo_deep_not() {
    let mut ctx = setup("(set-logic ALL)(declare-const p Bool)");
    // (not (not (not ... (not p) ...))) — 10 layers of not + 1 leaf = 11
    let term = "(not (not (not (not (not (not (not (not (not (not p))))))))))";
    test_term_size(&parse_term(&mut ctx, term), 11);
}

#[test]
fn test_memo_deep_add() {
    let mut ctx = setup("(set-logic ALL)(declare-const x Int)");
    // (+ (+ (+ ... (+ x 1) ... 1) 1) 1) — 10 apps, each with a numeral + nested child = 10*2 + 1 = 21
    let term = "(+ (+ (+ (+ (+ (+ (+ (+ (+ (+ x 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)";
    test_term_size(&parse_term(&mut ctx, term), 21);
}

#[test]
fn test_memo_deep_ite() {
    let mut ctx =
        setup("(set-logic ALL)(declare-const p Bool)(declare-const x Int)(declare-const y Int)");
    // 10 nested ites: each ite node + condition p + else y = 3 overhead, plus the nested then-branch
    // size = 10 * 3 + 1 (innermost x) = 31
    let term = "(ite p (ite p (ite p (ite p (ite p (ite p (ite p (ite p (ite p (ite p x y) y) y) y) y) y) y) y) y) y)";
    test_term_size(&parse_term(&mut ctx, term), 31);
}

#[test]
fn test_memo_deep_and() {
    let mut ctx = setup("(set-logic ALL)(declare-const p Bool)(declare-const q Bool)");
    // (and (and (and ... (and p q) ... q) q) q) — 10 ands, each with q + nested child = 10*2 + 1 = 21
    let term = "(and (and (and (and (and (and (and (and (and (and p q) q) q) q) q) q) q) q) q) q)";
    test_term_size(&parse_term(&mut ctx, term), 21);
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
    test_term_size(&parse_term(&mut ctx, term), 23);
}
