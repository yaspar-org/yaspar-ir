// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Tests that [`LetElim::let_elim`] and the [`GlobalSubst`] operations work in environments
//! other than `&mut Context`.
//!
//! The two operations have different bounds, because they need different capabilities:
//!
//! - `let_elim` only allocates terms, so it takes any `E: HasArena`.
//! - `gsubst` must read global definitions and the definition cache off a [`Context`], so it
//!   takes any `Ctx: HasMutRef<Context>`.
//!
//! Every builder context satisfies both, so [`check_ops`] exercises the two together across
//! `Context`, `&mut Context`, `Rc<RefCell<Context>>`, `Arc<Mutex<Context>>`, and each of
//! `QuantifierContext`, `LetContext`, `MatchContext`, `ArmContext`, `FunctionContext`,
//! `RecFunsContext`, `EachRecFunContext`, `DefSortContext`, `DatatypeContext`, and
//! `DtDeclContext`. [`check_let_elim`] additionally covers `TypedBuilder`, which is
//! `HasArena` but not `HasMutRef<Context>`.

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use yaspar_ir::ast::{
    CheckedApi, Context, GlobalSubst, HasArena, LetElim, ObjectAllocatorExt, RecFunc, Term,
    Typecheck, TypedBuilder,
};
use yaspar_ir::traits::HasMutRef;
use yaspar_ir::untyped::UntypedAst;

/// The term under test: it has both a `let` binding to eliminate and a global definition
/// (`double`) to expand, so a single term exercises both operations.
const TERM: &str = "(let ((x n)) (= (double x) 2))";

/// Expected result of `let_elim` on [`TERM`].
const LET_ELIMINATED: &str = "(= (double n) 2)";

/// Expected result of `gsubst(["double"])` on [`TERM`].
const GLOBAL_EXPANDED: &str = "(let ((x n)) (= (+ x x) 2))";

/// Expected result of applying both operations to [`TERM`], in either order.
const BOTH: &str = "(= (+ n n) 2)";

fn setup() -> (Context, Term) {
    let mut ctx = Context::new();
    UntypedAst
        .parse_script_str(
            r#"
        (set-logic ALL)
        (declare-const n Int)
        (declare-datatype Color ((red) (green)))
        (declare-const c Color)
        (define-fun double ((x Int)) Int (+ x x))
    "#,
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let term = UntypedAst
        .parse_term_str(TERM)
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();
    assert_eq!(term.to_string(), TERM);
    (ctx, term)
}

/// Run `let_elim` in `env` and assert it matches the `&mut Context` result.
///
/// Generic over `E: HasArena`, so this compiles only if `E` really is a valid `let_elim`
/// environment.
fn check_let_elim<E>(term: &Term, env: &mut E) -> Term
where
    E: HasArena,
{
    let elim = term.let_elim(env);
    assert_eq!(elim.to_string(), LET_ELIMINATED);
    // idempotent: no lets remain to eliminate
    assert_eq!(elim.let_elim(env).to_string(), LET_ELIMINATED);
    elim
}

/// Run every [`GlobalSubst`] entry point in `env` and assert they match the `&mut Context`
/// results.
///
/// Generic over `Ctx: HasMutRef<Context>`, so this compiles only if `Ctx` really is a valid
/// `gsubst` environment.
fn check_gsubst<Ctx>(term: &Term, env: &mut Ctx) -> Term
where
    Ctx: HasMutRef<Context>,
{
    let expanded = term.gsubst(["double"], env);
    assert_eq!(expanded.to_string(), GLOBAL_EXPANDED);

    // expanding a name that is not in the term leaves it untouched
    assert_eq!(term.gsubst(["red"], env).to_string(), TERM);

    // gsubst_all and gsubst_with_names agree with the explicit name list here, since
    // `double` is the only definition reachable from the term
    assert_eq!(term.gsubst_all(env).to_string(), GLOBAL_EXPANDED);
    let names = env.ref_mut().defined_symbols();
    assert_eq!(
        term.gsubst_with_names(&names, env).to_string(),
        GLOBAL_EXPANDED
    );

    // the slice impl is available in the same environment
    let slice = std::slice::from_ref(term).gsubst(["double"], env);
    assert_eq!(slice.len(), 1);
    assert_eq!(slice[0].to_string(), GLOBAL_EXPANDED);

    expanded
}

/// Run both operations in `env` and assert they compose in either order.
fn check_ops<Env>(term: &Term, env: &mut Env)
where
    Env: HasArena + HasMutRef<Context>,
{
    let elim = check_let_elim(term, env);
    let expanded = check_gsubst(term, env);
    assert_eq!(elim.gsubst(["double"], env).to_string(), BOTH);
    assert_eq!(expanded.let_elim(env).to_string(), BOTH);
}

#[test]
fn test_ops_in_context() {
    let (mut ctx, term) = setup();
    // Context itself, via the blanket `impl<X> HasMutRef<X> for X`
    check_ops(&term, &mut ctx);
}

#[test]
fn test_gsubst_in_context_mut_ref() {
    let (mut ctx, term) = setup();
    // `&mut Context` is HasMutRef<Context> (via `impl<X> HasMutRef<X> for &mut X`) but not
    // HasArena, so only gsubst applies
    let mut env: &mut Context = &mut ctx;
    check_gsubst(&term, &mut env);
}

#[test]
fn test_gsubst_in_rc_refcell() {
    let (ctx, term) = setup();
    let mut ctx = Rc::new(RefCell::new(ctx));
    check_gsubst(&term, &mut ctx);
}

#[test]
fn test_gsubst_in_arc_mutex() {
    let (ctx, term) = setup();
    let mut ctx = Arc::new(Mutex::new(ctx));
    check_gsubst(&term, &mut ctx);
}

#[test]
fn test_let_elim_in_typed_builder() {
    let (mut ctx, term) = setup();
    // TypedBuilder is HasArena but not HasMutRef<Context>, so only let_elim applies
    let mut builder = TypedBuilder::new(&mut ctx);
    check_let_elim(&term, &mut builder);
}

#[test]
fn test_ops_in_quantifier_context() {
    let (mut ctx, term) = setup();
    let int = ctx.int_sort();
    let mut q_ctx = ctx
        .build_quantifier_with_domain([("q", int.clone()), ("r", int)])
        .unwrap();
    check_ops(&term, &mut q_ctx);

    // the context is still usable afterwards
    let q = q_ctx.typed_symbol("q").unwrap();
    let r = q_ctx.typed_symbol("r").unwrap();
    let body = q_ctx.typed_simp_app(">", [q, r]).unwrap();
    let forall = q_ctx.typed_forall(body).unwrap();
    assert_eq!(forall.to_string(), "(forall ((q Int) (r Int)) (> q r))");
}

#[test]
fn test_ops_in_let_context() {
    let (mut ctx, term) = setup();
    let one = ctx.numeral(1u8.into()).unwrap();
    let mut l_ctx = ctx.build_let([("b", one)]).unwrap();
    check_ops(&term, &mut l_ctx);

    let b = l_ctx.typed_symbol("b").unwrap();
    let body = l_ctx.typed_eq(b.clone(), b).unwrap();
    assert_eq!(l_ctx.typed_let(body).to_string(), "(let ((b 1)) (= b b))");
}

#[test]
fn test_ops_in_match_and_arm_context() {
    let (mut ctx, term) = setup();
    let c = ctx.typed_symbol("c").unwrap();
    let mut m_ctx = ctx.build_matching(c).unwrap();
    check_ops(&term, &mut m_ctx);

    let mut arm = m_ctx.build_arm_nullary("red").unwrap();
    check_ops(&term, &mut arm);

    // the arm is still usable afterwards
    let t = arm.get_true();
    arm.typed_arm(t).unwrap();
    let mut arm = m_ctx.build_arm_nullary("green").unwrap();
    let f = arm.get_false();
    arm.typed_arm(f).unwrap();
    assert_eq!(
        m_ctx.typed_matching().unwrap().to_string(),
        "(match c ((red true) (green false)))"
    );
}

#[test]
fn test_ops_in_function_context() {
    let (mut ctx, term) = setup();
    let int = ctx.int_sort();
    let mut f_ctx = ctx
        .build_fun_out_sort("triple", [("x", int.clone())], int)
        .unwrap();
    check_ops(&term, &mut f_ctx);

    let x = f_ctx.typed_symbol("x").unwrap();
    let body = f_ctx
        .typed_simp_app("+", [x.clone(), x.clone(), x])
        .unwrap();
    assert_eq!(
        f_ctx.typed_define_fun(body).unwrap().to_string(),
        "(define-fun triple ((x Int)) Int (+ x x x))"
    );
}

#[test]
fn test_ops_in_rec_funs_and_each_rec_fun_context() {
    let (mut ctx, term) = setup();
    let int = ctx.int_sort();
    let mut r_ctx = ctx
        .build_rec_funs([RecFunc::new("countdown", [("x", int.clone())], int)])
        .unwrap();
    check_ops(&term, &mut r_ctx);

    let mut f_ctx = r_ctx.build_function("countdown").unwrap();
    check_ops(&term, &mut f_ctx);

    // the recursive function body can still be built afterwards
    let x = f_ctx.typed_symbol("x").unwrap();
    let zero = f_ctx.numeral(0u8.into()).unwrap();
    let one = f_ctx.numeral(1u8.into()).unwrap();
    let is_zero = f_ctx.typed_eq(x.clone(), zero.clone()).unwrap();
    let dec = f_ctx.typed_simp_app("-", [x, one]).unwrap();
    let rec = f_ctx.typed_simp_app("countdown", [dec]).unwrap();
    let body = f_ctx.typed_ite(is_zero, zero, rec).unwrap();
    f_ctx.typed_function(body).unwrap();
    assert_eq!(
        r_ctx.typed_define_funs_rec().unwrap().to_string(),
        "(define-fun-rec countdown ((x Int)) Int (ite (= x 0) 0 (countdown (- x 1))))"
    );
}

#[test]
fn test_ops_in_def_sort_context() {
    let (mut ctx, term) = setup();
    let int = ctx.int_sort();
    let mut s_ctx = ctx.build_sort_alias("MyInt", []).unwrap();
    check_ops(&term, &mut s_ctx);

    assert_eq!(
        s_ctx.typed_define_sort(int).unwrap().to_string(),
        "(define-sort MyInt () Int)"
    );
}

#[test]
fn test_ops_in_datatype_and_dt_decl_context() {
    let (mut ctx, term) = setup();
    let int = ctx.int_sort();
    let mut d_ctx = ctx.build_datatypes([("Pair", [])]).unwrap();
    check_ops(&term, &mut d_ctx);

    let mut dt_ctx = d_ctx.build_datatype("Pair").unwrap();
    check_ops(&term, &mut dt_ctx);

    // the datatype declaration can still be completed afterwards
    dt_ctx
        .build_datatype_constructor("mk-pair", [("fst", int.clone()), ("snd", int)])
        .unwrap();
    dt_ctx.typed_datatype().unwrap();
    assert_eq!(
        d_ctx.typed_declare_datatypes().unwrap().to_string(),
        "(declare-datatype Pair ((mk-pair (fst Int) (snd Int))))"
    );
}

#[test]
fn test_ops_in_nested_contexts() {
    let (mut ctx, term) = setup();
    let int = ctx.int_sort();
    let mut q_ctx = ctx
        .build_quantifier_with_domain([("q", int.clone())])
        .unwrap();
    let q = q_ctx.typed_symbol("q").unwrap();
    let mut l_ctx = q_ctx.build_let([("b", q)]).unwrap();
    let mut inner = l_ctx.build_quantifier_with_domain([("z", int)]).unwrap();
    // reaching through three nested builder contexts still resolves to the same Context
    check_ops(&term, &mut inner);
}

/// A definition local to a builder context's scope is still expanded correctly: the local
/// bindings of the environment must not interfere with global expansion.
#[test]
fn test_gsubst_in_context_with_shadowing_local() {
    let (mut ctx, _) = setup();
    let int = ctx.int_sort();
    // bind a local named `x`, the same name as `double`'s parameter
    let mut q_ctx = ctx.build_quantifier_with_domain([("x", int)]).unwrap();
    let x = q_ctx.typed_symbol("x").unwrap();
    let double_x = q_ctx.typed_simp_app("double", [x]).unwrap();
    assert_eq!(double_x.to_string(), "(double x)");

    let expanded = double_x.gsubst(["double"], &mut q_ctx);
    assert_eq!(expanded.to_string(), "(+ x x)");

    // and the quantifier still binds the local it expanded into
    let body = q_ctx.typed_eq(expanded, double_x).unwrap();
    let forall = q_ctx.typed_forall(body).unwrap();
    assert_eq!(
        forall.to_string(),
        "(forall ((x Int)) (= (+ x x) (double x)))"
    );
}
