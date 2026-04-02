use yaspar_ir::ast::alg::{
    Attribute, Constant, Local, PatternArm, QualifiedIdentifier, VarBinding,
};
use yaspar_ir::ast::{Context, Typecheck};
use yaspar_ir::ast::{Sort, Str, Term, TermRecursor, TypedTermRecursor};
use yaspar_ir::untyped::UntypedAst;
enum Bottom {}
struct TermSize;

impl TermRecursor<Str, Sort, Term> for TermSize {
    type Out = usize;
    type Err = Bottom;

    fn on_constant(
        &mut self,
        constant: &Constant<Str>,
        sort: &Option<Sort>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1)
    }

    fn on_global(
        &mut self,
        id: &QualifiedIdentifier<Str, Sort>,
        sort: &Option<Sort>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1)
    }

    fn on_local(&mut self, id: &Local<Str, Sort>) -> Result<Self::Out, Self::Err> {
        Ok(1)
    }

    fn on_app(
        &mut self,
        id: &QualifiedIdentifier<Str, Sort>,
        ts: &[Term],
        s: &Option<Sort>,
        recs: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + recs.into_iter().sum::<usize>())
    }

    fn setup_let_scope(
        &mut self,
        vs: &[VarBinding<Str, Term>],
        body: &Term,
        vs_rec: &[VarBinding<Str, Self::Out>],
    ) -> Result<(), Self::Err> {
        Ok(())
    }

    fn on_let(
        &mut self,
        vs: &[VarBinding<Str, Term>],
        body: &Term,
        vs_rec: Vec<VarBinding<Str, Self::Out>>,
        body_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + vs_rec.into_iter().map(|v| v.2).sum::<usize>() + body_rec)
    }

    fn setup_quantifier_scope(
        &mut self,
        vs: &[VarBinding<Str, Sort>],
        t: &Term,
    ) -> Result<(), Self::Err> {
        Ok(())
    }

    fn on_exists(
        &mut self,
        vs: &[VarBinding<Str, Sort>],
        t: &Term,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + t_rec)
    }

    fn on_forall(
        &mut self,
        vs: &[VarBinding<Str, Sort>],
        t: &Term,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + t_rec)
    }

    fn setup_match_case_scope(
        &mut self,
        scrutinee: &Term,
        cases: &[PatternArm<Str, Term>],
        scrutinee_rec: &Self::Out,
        case_idx: usize,
    ) -> Result<(), Self::Err> {
        Ok(())
    }

    fn on_match_arm(
        &mut self,
        scrutinee: &Term,
        cases: &[PatternArm<Str, Term>],
        case_idx: usize,
        arm: Self::Out,
    ) -> Result<PatternArm<Str, Self::Out>, Self::Err> {
        Ok(PatternArm {
            pattern: cases[case_idx].pattern.clone(),
            body: arm,
        })
    }

    fn on_match(
        &mut self,
        scrutinee: &Term,
        cases: &[PatternArm<Str, Term>],
        scrutinee_rec: Self::Out,
        cases_rec: Vec<PatternArm<Str, Self::Out>>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + scrutinee_rec + cases_rec.into_iter().map(|c| c.body).sum::<usize>())
    }

    fn on_annotated(
        &mut self,
        t: &Term,
        anns: &[Attribute<Str, Term>],
        t_rec: Self::Out,
        anns_rec: Vec<Attribute<Str, Self::Out>>,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + t_rec
            + anns_rec
                .into_iter()
                .map(|a| match a {
                    Attribute::Keyword(_) => 1,
                    Attribute::Constant(_, _) => 1,
                    Attribute::Symbol(_, _) => 1,
                    Attribute::Named(_) => 1,
                    Attribute::Pattern(ns) => ns.into_iter().sum::<usize>(),
                })
                .sum::<usize>())
    }

    fn on_eq(
        &mut self,
        a: &Term,
        b: &Term,
        a_rec: Self::Out,
        b_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + a_rec + b_rec)
    }

    fn on_distinct(&mut self, ts: &[Term], ts_rec: Vec<Self::Out>) -> Result<Self::Out, Self::Err> {
        Ok(1 + ts_rec.into_iter().sum::<usize>())
    }

    fn on_and(&mut self, ts: &[Term], ts_rec: Vec<Self::Out>) -> Result<Self::Out, Self::Err> {
        Ok(1 + ts_rec.into_iter().sum::<usize>())
    }

    fn on_or(&mut self, ts: &[Term], ts_rec: Vec<Self::Out>) -> Result<Self::Out, Self::Err> {
        Ok(1 + ts_rec.into_iter().sum::<usize>())
    }

    fn on_xor(&mut self, ts: &[Term], ts_rec: Vec<Self::Out>) -> Result<Self::Out, Self::Err> {
        Ok(1 + ts_rec.into_iter().sum::<usize>())
    }

    fn on_not(&mut self, t: &Term, t_rec: Self::Out) -> Result<Self::Out, Self::Err> {
        Ok(1 + t_rec)
    }

    fn on_implies(
        &mut self,
        ts: &[Term],
        t: &Term,
        ts_rec: &[Self::Out],
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err> {
        Ok(1 + ts_rec.into_iter().sum::<usize>() + t_rec)
    }

    fn on_ite(
        &mut self,
        b: &Term,
        t: &Term,
        e: &Term,
        b_rec: Self::Out,
        t_rec: Self::Out,
        e_rec: &Self::Out,
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
