// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Alpha equivalence of terms.
//!
//! Two terms are alpha equivalent when they are structurally identical up to a renaming of the
//! variables bound by `let`, `forall`, `exists`, and `match` patterns. This is the equivalence
//! that plain `==` on a [`Term`] deliberately does *not* provide: local variables carry a unique
//! id, so two separately built copies of `(forall ((x Int)) (p x))` compare unequal even though
//! they denote the same formula.
//!
//! Two flavors are provided:
//!
//! - [`AlphaEquiv::aeq`] — strict: free local variables are *not* renamed. They must be
//!   literally the same variable on both sides, since a free local's meaning comes from its
//!   ambient context.
//! - [`AlphaEquiv::aeq_permissive`] — additionally allows free local variables to correspond,
//!   provided the correspondence is consistent: it must be a bijection (each free local on the
//!   left corresponds to exactly one on the right, and vice versa), sorts must agree, and a free
//!   local never matches a bound one. This is useful for comparing terms that were built in
//!   different scopes, e.g. bodies extracted from two separately constructed quantifiers.

use crate::ast::alg::PatternArm;
use crate::ast::alg::{LocalId, VarBinding};
use crate::ast::{ATerm, Attribute, Pattern, Sort, Str, Term};
use crate::traits::Repr;
use bimap::BiHashMap;
use yaspar_macros::stack_safe;

/// Compare `Self` up to renaming of bound variables.
pub trait AlphaEquiv {
    /// Strict alpha equivalence: bound variables may be renamed, but free local variables must
    /// be literally the same variable on both sides.
    fn aeq(&self, other: &Self) -> bool;
    /// Permissive alpha equivalence: like [`aeq`](AlphaEquiv::aeq), but free local variables may
    /// also correspond under a consistent (bijective, sort-preserving) renaming.
    fn aeq_permissive(&self, other: &Self) -> bool;
}

impl AlphaEquiv for Term {
    fn aeq(&self, other: &Self) -> bool {
        aeq::aeq_impl(&mut AEqCtx::new(), self, other, false)
    }

    fn aeq_permissive(&self, other: &Self) -> bool {
        aeq::aeq_impl(&mut AEqCtx::new(), self, other, true)
    }
}

struct AEqCtx {
    /// Correspondence between local variables
    ///
    /// A bijection: each bound variable on the left corresponds to exactly one on the right.
    local_map: BiHashMap<LocalId, LocalId>,
}

impl AEqCtx {
    fn new() -> Self {
        Self {
            local_map: BiHashMap::new(),
        }
    }

    fn assoc_local(&mut self, id1: LocalId, id2: LocalId) {
        self.local_map.insert(id1, id2);
    }

    /// Enter a scope in which each `(id1, id2)` pair of bound variables corresponds.
    fn enter(&mut self, pairs: Vec<(LocalId, LocalId)>) -> Option<Vec<LocalId>> {
        let mut inserted = vec![];
        for (id1, id2) in pairs {
            let overwritten = self.local_map.insert(id1, id2);
            if overwritten.did_overwrite() {
                // in this case, scope management has failed for some reason because local ids are
                // unbalanced, so comparison should also return false
                return None;
            }
            inserted.push(id1);
        }
        Some(inserted)
    }

    /// Leave a scope, restoring the correspondences it shadowed.
    fn exit(&mut self, inserted: Vec<LocalId>) {
        for id1 in inserted {
            self.local_map.remove_by_left(&id1);
        }
    }
}

/// Match two patterns up to renaming of the variables they bind.
///
/// Returns the corresponding pattern-variable id pairs when the patterns have the same shape,
/// or [`None`] when they cannot match at all.
fn aeq_pattern(p1: &Pattern, p2: &Pattern) -> Option<Vec<(LocalId, LocalId)>> {
    match (p1, p2) {
        (Pattern::Wildcard(None), Pattern::Wildcard(None)) => Some(vec![]),
        // a named wildcard binds one variable, whose name is irrelevant
        (Pattern::Wildcard(Some((_, id1))), Pattern::Wildcard(Some((_, id2)))) => {
            Some(vec![(*id1, *id2)])
        }
        (Pattern::Ctor(c1), Pattern::Ctor(c2)) if c1 == c2 => Some(vec![]),
        (
            Pattern::Applied {
                ctor: c1,
                arguments: args1,
            },
            Pattern::Applied {
                ctor: c2,
                arguments: args2,
            },
        ) if *c1 == *c2 && args1.len() == args2.len() => {
            let mut id_map = vec![];
            for (a1, a2) in args1.iter().zip(args2.iter()) {
                match (a1, a2) {
                    (None, None) => {}
                    (Some((_, id1)), Some((_, id2))) => id_map.push((*id1, *id2)),
                    _ => return None,
                }
            }
            Some(id_map)
        }
        _ => None,
    }
}

#[stack_safe]
mod aeq {
    use super::*;

    /// Decide alpha equivalence of `t1` and `t2` under the variable correspondence in `ctx`.
    pub(super) fn aeq_impl(ctx: &mut AEqCtx, t1: &Term, t2: &Term, permissive: bool) -> bool {
        match (t1.repr(), t2.repr()) {
            // --- Leaves ---
            (ATerm::Constant(_, _), ATerm::Constant(_, _))
            | (ATerm::Global(_, _), ATerm::Global(_, _)) => *t1 == *t2,

            // A bound variable matches only its counterpart; a free variable only itself.
            (ATerm::Local(l1), ATerm::Local(l2)) => {
                if l1.sort != l2.sort {
                    return false;
                }
                match (
                    ctx.local_map.get_by_left(&l1.id).copied(),
                    ctx.local_map.get_by_right(&l2.id).copied(),
                ) {
                    (Some(id1), Some(_)) => id1 == l2.id,
                    (None, None) => {
                        if permissive {
                            // in the permissive case, two free local variables in retrospect compare equal
                            ctx.local_map.remove_by_left(&l1.id);
                            ctx.assoc_local(l1.id, l2.id);
                            true
                        } else {
                            l1.id == l2.id
                        }
                    }
                    // otherwise, a free variable never matches a bound one
                    _ => false,
                }
            }

            // --- Application ---
            (ATerm::App(f1, ts1, s1), ATerm::App(f2, ts2, s2)) => {
                f1 == f2 && s1 == s2 && aeq_terms(ctx, ts1, ts2, permissive)
            }

            // --- Binders ---

            // `let` is parallel: the bound terms live in the enclosing scope, only the body sees
            // the new bindings.
            (ATerm::Let(vs1, b1), ATerm::Let(vs2, b2)) => {
                if vs1.len() != vs2.len() {
                    return false;
                }
                let mut id_map = vec![];
                for (v1, v2) in vs1.iter().zip(vs2.iter()) {
                    if !aeq_impl(ctx, &v1.2, &v2.2, permissive) {
                        return false;
                    }
                    id_map.push((v1.1, v2.1));
                }
                aeq_in_scope(ctx, id_map, b1, b2, permissive)
            }

            (ATerm::Forall(vs1, b1), ATerm::Forall(vs2, b2))
            | (ATerm::Exists(vs1, b1), ATerm::Exists(vs2, b2)) => {
                aeq_quantifier(ctx, vs1, b1, vs2, b2, permissive)
            }

            // Arms must correspond positionally; each pattern binds its variables in its own body.
            (ATerm::Matching(s1, arms1), ATerm::Matching(s2, arms2)) => {
                let arm_lhs: &[PatternArm<Str, Term>] = arms1;
                let arm_rhs: &[PatternArm<Str, Term>] = arms2;
                if arm_lhs.len() != arm_rhs.len() || !aeq_impl(ctx, s1, s2, permissive) {
                    return false;
                }
                let mut i: usize = 0;
                while i < arm_lhs.len() {
                    let (a1, a2) = (&arm_lhs[i], &arm_rhs[i]);
                    match aeq_pattern(&a1.pattern, &a2.pattern) {
                        Some(pairs) => {
                            if !aeq_in_scope(ctx, pairs, &a1.body, &a2.body, permissive) {
                                return false;
                            }
                        }
                        None => return false,
                    }
                    i += 1;
                }
                true
            }

            // --- Annotation ---
            (ATerm::Annotated(x1, as1), ATerm::Annotated(x2, as2)) => {
                let attr_lhs: &[Attribute] = as1;
                let attr_rhs: &[Attribute] = as2;
                if attr_lhs.len() != attr_rhs.len() || !aeq_impl(ctx, x1, x2, permissive) {
                    return false;
                }
                let mut i: usize = 0;
                while i < attr_lhs.len() {
                    if !aeq_attribute(ctx, &attr_lhs[i], &attr_rhs[i], permissive) {
                        return false;
                    }
                    i += 1;
                }
                true
            }

            // --- Equality and logical connectives ---
            (ATerm::Eq(a1, b1), ATerm::Eq(a2, b2)) => {
                aeq_impl(ctx, a1, a2, permissive) && aeq_impl(ctx, b1, b2, permissive)
            }

            (ATerm::Distinct(ts1), ATerm::Distinct(ts2))
            | (ATerm::And(ts1), ATerm::And(ts2))
            | (ATerm::Or(ts1), ATerm::Or(ts2))
            | (ATerm::Xor(ts1), ATerm::Xor(ts2)) => aeq_terms(ctx, ts1, ts2, permissive),

            (ATerm::Implies(ts1, c1), ATerm::Implies(ts2, c2)) => {
                aeq_terms(ctx, ts1, ts2, permissive) && aeq_impl(ctx, c1, c2, permissive)
            }

            (ATerm::Not(x1), ATerm::Not(x2)) => aeq_impl(ctx, x1, x2, permissive),

            (ATerm::Ite(c1, t1, e1), ATerm::Ite(c2, t2, e2)) => {
                aeq_impl(ctx, c1, c2, permissive)
                    && aeq_impl(ctx, t1, t2, permissive)
                    && aeq_impl(ctx, e1, e2, permissive)
            }

            // different constructors are never alpha equivalent
            (_, _) => false,
        }
    }

    /// Pairwise alpha equivalence of two term lists, which must have the same length.
    pub(super) fn aeq_terms(
        ctx: &mut AEqCtx,
        ts1: &[Term],
        ts2: &[Term],
        permissive: bool,
    ) -> bool {
        if ts1.len() != ts2.len() {
            return false;
        }
        let mut i = 0;
        while i < ts1.len() {
            if !aeq_impl(ctx, &ts1[i], &ts2[i], permissive) {
                return false;
            }
            i += 1;
        }
        true
    }

    /// Compare `b1` and `b2` with `pairs` of bound variables corresponding, then restore the scope.
    pub(super) fn aeq_in_scope(
        ctx: &mut AEqCtx,
        pairs: Vec<(LocalId, LocalId)>,
        b1: &Term,
        b2: &Term,
        permissive: bool,
    ) -> bool {
        match ctx.enter(pairs) {
            None => false,
            Some(scope) => {
                let r = aeq_impl(ctx, b1, b2, permissive);
                ctx.exit(scope);
                r
            }
        }
    }

    /// Compare two quantified terms: the bound variables must agree in number and sort (but not in
    /// name), and the bodies must agree with those variables corresponding positionally.
    pub(super) fn aeq_quantifier(
        ctx: &mut AEqCtx,
        vs1: &[VarBinding<Str, Sort>],
        b1: &Term,
        vs2: &[VarBinding<Str, Sort>],
        b2: &Term,
        permissive: bool,
    ) -> bool {
        if vs1.len() != vs2.len() {
            return false;
        }
        let mut id_map = vec![];
        for (v1, v2) in vs1.iter().zip(vs2.iter()) {
            if v1.2 != v2.2 {
                return false;
            }
            id_map.push((v1.1, v2.1));
        }
        aeq_in_scope(ctx, id_map, b1, b2, permissive)
    }

    /// Compare two attributes, recursing into `:pattern` and `:no-pattern` since they carry terms.
    pub(super) fn aeq_attribute(
        ctx: &mut AEqCtx,
        a1: &Attribute,
        a2: &Attribute,
        permissive: bool,
    ) -> bool {
        match (a1, a2) {
            (Attribute::Pattern(ts1), Attribute::Pattern(ts2)) => {
                aeq_terms(ctx, ts1, ts2, permissive)
            }
            #[cfg(feature = "no-pattern")]
            (Attribute::NoPattern(t1), Attribute::NoPattern(t2)) => {
                aeq_impl(ctx, t1, t2, permissive)
            }
            // the remaining attributes hold no terms, so syntactic equality is exact
            _ => a1 == a2,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{CheckedApi, Context, ObjectAllocatorExt, Typecheck};
    use crate::untyped::UntypedAst;

    /// Parse and type-check `s` in a context pre-loaded with the declarations used by the tests.
    fn parse(ctx: &mut Context, s: &str) -> Term {
        UntypedAst
            .parse_term_str(s)
            .unwrap()
            .type_check(ctx)
            .unwrap()
    }

    fn setup() -> Context {
        let mut ctx = Context::new();
        UntypedAst
            .parse_script_str(
                r#"
            (set-logic ALL)
            (declare-const n Int)
            (declare-const m Int)
            (declare-fun p (Int) Bool)
            (declare-fun q (Int Int) Bool)
            (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
            (declare-datatype Color ((red) (green)))
            (declare-const c Color)
            (declare-const pr Pair)
        "#,
            )
            .unwrap()
            .type_check(&mut ctx)
            .unwrap();
        ctx
    }

    /// Assert that `s1` and `s2` are alpha equivalent, and that `aeq` is reflexive on both.
    fn assert_aeq(s1: &str, s2: &str) {
        let mut ctx = setup();
        let t1 = parse(&mut ctx, s1);
        let t2 = parse(&mut ctx, s2);
        assert!(t1.aeq(&t2), "expected {s1} ~ {s2}");
        assert!(t2.aeq(&t1), "expected aeq to be symmetric on {s1} / {s2}");
        assert!(t1.aeq(&t1));
        assert!(t2.aeq(&t2));
    }

    fn assert_not_aeq(s1: &str, s2: &str) {
        let mut ctx = setup();
        let t1 = parse(&mut ctx, s1);
        let t2 = parse(&mut ctx, s2);
        assert!(!t1.aeq(&t2), "expected {s1} !~ {s2}");
        assert!(!t2.aeq(&t1), "expected aeq to be symmetric on {s1} / {s2}");
    }

    #[test]
    fn test_aeq_leaves() {
        assert_aeq("1", "1");
        assert_not_aeq("1", "2");
        assert_aeq("n", "n");
        assert_not_aeq("n", "m");
        assert_aeq("(p n)", "(p n)");
        assert_not_aeq("(p n)", "(p m)");
    }

    /// The motivating case: two separately parsed copies of the same quantifier are `!=` because
    /// the bound variables get distinct ids, but they are alpha equivalent.
    #[test]
    fn test_aeq_quantifier_distinct_ids() {
        let mut ctx = setup();
        let t1 = parse(&mut ctx, "(forall ((x Int)) (p x))");
        let t2 = parse(&mut ctx, "(forall ((x Int)) (p x))");
        assert_ne!(t1, t2);
        assert!(t1.aeq(&t2));
    }

    #[test]
    fn test_aeq_quantifier_renaming() {
        assert_aeq("(forall ((x Int)) (p x))", "(forall ((y Int)) (p y))");
        assert_aeq("(exists ((x Int)) (p x))", "(exists ((y Int)) (p y))");
        // a quantifier is not equivalent to the other kind
        assert_not_aeq("(forall ((x Int)) (p x))", "(exists ((y Int)) (p y))");
        // sorts of bound variables must agree
        assert_not_aeq("(forall ((x Int)) (p 1))", "(forall ((x Bool)) (p 1))");
        // arity must agree
        assert_not_aeq(
            "(forall ((x Int)) (p x))",
            "(forall ((x Int) (y Int)) (p x))",
        );
    }

    /// Renaming must respect the *position* of each binder, not merely the set of names.
    #[test]
    fn test_aeq_quantifier_permuted_uses() {
        assert_aeq(
            "(forall ((x Int) (y Int)) (q x y))",
            "(forall ((a Int) (b Int)) (q a b))",
        );
        // swapping the uses is a genuinely different formula
        assert_not_aeq(
            "(forall ((x Int) (y Int)) (q x y))",
            "(forall ((a Int) (b Int)) (q b a))",
        );
    }

    /// A free local must be the same variable on both sides, and never matches a bound one.
    #[test]
    fn test_aeq_free_locals_not_renamed() {
        let mut ctx = setup();
        let int = ctx.int_sort();
        let mut q1 = ctx
            .build_quantifier_with_domain([("x", int.clone())])
            .unwrap();
        let x1 = q1.typed_symbol("x").unwrap();
        // `(p x)` with `x` free, from two different quantifier scopes
        let free1 = q1.typed_simp_app("p", [x1.clone()]).unwrap();
        assert!(free1.aeq(&free1));

        let mut q2 = ctx.build_quantifier_with_domain([("x", int)]).unwrap();
        let x2 = q2.typed_symbol("x").unwrap();
        let free2 = q2.typed_simp_app("p", [x2]).unwrap();
        // distinct free variables that merely print the same are not alpha equivalent
        assert!(!free1.aeq(&free2));

        // and a bound variable does not match a free one
        let bound = parse(&mut ctx, "(forall ((x Int)) (p x))");
        let ATerm::Forall(_, body) = bound.repr() else {
            panic!("expected a forall")
        };
        assert!(!body.aeq(&free1));
        assert!(!free1.aeq(body));
    }

    #[test]
    fn test_aeq_let() {
        assert_aeq("(let ((x n)) (p x))", "(let ((y n)) (p y))");
        // the bound term is compared in the enclosing scope
        assert_not_aeq("(let ((x n)) (p x))", "(let ((y m)) (p y))");
        assert_aeq("(let ((x n) (y m)) (q x y))", "(let ((a n) (b m)) (q a b))");
        assert_not_aeq("(let ((x n) (y m)) (q x y))", "(let ((a n) (b m)) (q b a))");
        // a let is not equivalent to its own expansion: the shapes differ
        assert_not_aeq("(let ((x n)) (p x))", "(p n)");
    }

    /// `let` bindings are parallel, so the right-hand sides do not see the new bindings.
    #[test]
    fn test_aeq_let_is_parallel() {
        assert_aeq(
            "(let ((x n)) (let ((x m) (y x)) (q x y)))",
            "(let ((a n)) (let ((b m) (c a)) (q b c)))",
        );
    }

    /// An inner binder shadowing an outer one must be undone when the inner scope ends.
    #[test]
    fn test_aeq_shadowing() {
        assert_aeq(
            "(forall ((x Int)) (and (forall ((x Int)) (p x)) (p x)))",
            "(forall ((a Int)) (and (forall ((b Int)) (p b)) (p a)))",
        );
        // the inner `x` shadows the outer one, so the two `(p x)` refer to different variables;
        // on the right both refer to the outer `a`
        assert_not_aeq(
            "(forall ((x Int)) (and (forall ((x Int)) (p x)) (p x)))",
            "(forall ((a Int)) (and (forall ((b Int)) (p a)) (p a)))",
        );
    }

    #[test]
    fn test_aeq_match() {
        assert_aeq(
            "(match pr (((mk-pair a b) (q a b))))",
            "(match pr (((mk-pair x y) (q x y))))",
        );
        assert_not_aeq(
            "(match pr (((mk-pair a b) (q a b))))",
            "(match pr (((mk-pair x y) (q y x))))",
        );
        // nullary constructor arms compare by constructor name
        assert_aeq(
            "(match c ((red true) (green false)))",
            "(match c ((red true) (green false)))",
        );
        assert_not_aeq(
            "(match c ((red true) (green false)))",
            "(match c ((red false) (green true)))",
        );
        // a named wildcard binds a variable, so it can be renamed
        assert_aeq(
            "(match c ((red true) (w (p 1))))",
            "(match c ((red true) (v (p 1))))",
        );
    }

    #[test]
    fn test_aeq_connectives() {
        assert_aeq("(and (p n) (p m))", "(and (p n) (p m))");
        // connectives are compared positionally, not as sets
        assert_not_aeq("(and (p n) (p m))", "(and (p m) (p n))");
        assert_not_aeq("(and (p n) (p m))", "(or (p n) (p m))");
        assert_not_aeq("(and (p n))", "(and (p n) (p n))");
        assert_aeq("(not (p n))", "(not (p n))");
        assert_aeq("(=> (p n) (p m))", "(=> (p n) (p m))");
        assert_aeq("(ite (p n) 1 2)", "(ite (p n) 1 2)");
        assert_not_aeq("(ite (p n) 1 2)", "(ite (p n) 2 1)");
        assert_aeq("(distinct n m)", "(distinct n m)");
        assert_aeq("(xor (p n) (p m))", "(xor (p n) (p m))");
        assert_aeq("(= n m)", "(= n m)");
        assert_not_aeq("(= n m)", "(= m n)");
    }

    /// Attributes are part of the term, and `:pattern` carries terms that need renaming.
    #[test]
    fn test_aeq_annotated() {
        assert_aeq(
            "(forall ((x Int)) (! (p x) :pattern ((p x))))",
            "(forall ((y Int)) (! (p y) :pattern ((p y))))",
        );
        assert_not_aeq(
            "(forall ((x Int)) (! (p x) :pattern ((p x))))",
            "(forall ((y Int)) (! (p y) :pattern ((p n))))",
        );
        assert_aeq("(! (p n) :named foo)", "(! (p n) :named foo)");
        assert_not_aeq("(! (p n) :named foo)", "(! (p n) :named bar)");
        // an annotation is not transparent
        assert_not_aeq("(! (p n) :named foo)", "(p n)");
    }

    /// `:no-pattern` carries a term as well, so its variables must correspond like any other.
    #[cfg(feature = "no-pattern")]
    #[test]
    fn test_aeq_no_pattern() {
        assert_aeq(
            "(forall ((x Int)) (! (p x) :no-pattern (p x)))",
            "(forall ((y Int)) (! (p y) :no-pattern (p y)))",
        );
        // the anti-trigger has to correspond too: here it is the global `n` on one side
        assert_not_aeq(
            "(forall ((x Int)) (! (p x) :no-pattern (p x)))",
            "(forall ((y Int)) (! (p y) :no-pattern (p n)))",
        );
        // `:pattern` and `:no-pattern` mean opposite things, so they never match
        assert_not_aeq(
            "(forall ((x Int)) (! (p x) :pattern ((p x))))",
            "(forall ((y Int)) (! (p y) :no-pattern (p y)))",
        );
        // both attributes together, as Dafny/Boogie emit them
        assert_aeq(
            "(forall ((x Int)) (! (p x) :pattern ((p x)) :no-pattern (p x)))",
            "(forall ((y Int)) (! (p y) :pattern ((p y)) :no-pattern (p y)))",
        );
    }

    /// Build `(p v)` and `v` itself, where `v` is a local variable of sort `Int` that is *free*
    /// in the returned terms.
    fn free_p_v(ctx: &mut Context, name: &str) -> (Term, Term) {
        let int = ctx.int_sort();
        let mut q = ctx.build_quantifier_with_domain([(name, int)]).unwrap();
        let v = q.typed_symbol(name).unwrap();
        let pv = q.typed_simp_app("p", [v.clone()]).unwrap();
        (pv, v)
    }

    /// On terms without free locals, `aeq_permissive` agrees with `aeq`.
    #[test]
    fn test_aeq_permissive_agrees_with_aeq_on_closed_terms() {
        let mut ctx = setup();
        let t1 = parse(&mut ctx, "(forall ((x Int)) (p x))");
        let t2 = parse(&mut ctx, "(forall ((y Int)) (p y))");
        assert!(t1.aeq_permissive(&t2));
        let t3 = parse(&mut ctx, "(exists ((y Int)) (p y))");
        assert!(!t1.aeq_permissive(&t3));
        // globals are still not renamed
        let t4 = parse(&mut ctx, "(p n)");
        let t5 = parse(&mut ctx, "(p m)");
        assert!(t4.aeq_permissive(&t4));
        assert!(!t4.aeq_permissive(&t5));
    }

    /// The motivating case for the permissive mode: two distinct free locals of the same sort
    /// may correspond, even though strict `aeq` rejects them.
    #[test]
    fn test_aeq_permissive_free_locals() {
        let mut ctx = setup();
        let (free1, _) = free_p_v(&mut ctx, "x");
        let (free2, _) = free_p_v(&mut ctx, "y");
        assert!(!free1.aeq(&free2));
        assert!(free1.aeq_permissive(&free2));
        assert!(free2.aeq_permissive(&free1));
        assert!(free1.aeq_permissive(&free1));
    }

    /// The free-local correspondence must be a bijection applied consistently across the term.
    #[test]
    fn test_aeq_permissive_bijective_renaming() {
        let mut ctx = setup();
        let int = ctx.int_sort();
        let mut q1 = ctx
            .build_quantifier_with_domain([("x", int.clone()), ("y", int.clone())])
            .unwrap();
        let x = q1.typed_symbol("x").unwrap();
        let y = q1.typed_symbol("y").unwrap();
        let q_x_y = q1.typed_simp_app("q", [x.clone(), y.clone()]).unwrap();
        let q_x_x = q1.typed_simp_app("q", [x.clone(), x]).unwrap();

        let mut q2 = ctx
            .build_quantifier_with_domain([("a", int.clone()), ("b", int)])
            .unwrap();
        let a = q2.typed_symbol("a").unwrap();
        let b = q2.typed_symbol("b").unwrap();
        let q_a_b = q2.typed_simp_app("q", [a.clone(), b.clone()]).unwrap();
        let q_b_a = q2.typed_simp_app("q", [b.clone(), a.clone()]).unwrap();
        let q_a_a = q2.typed_simp_app("q", [a.clone(), a]).unwrap();

        // any bijective renaming works, including a "swapped" one
        assert!(q_x_y.aeq_permissive(&q_a_b));
        assert!(q_x_y.aeq_permissive(&q_b_a));
        assert!(q_x_x.aeq_permissive(&q_a_a));
        // but one variable cannot correspond to two (and vice versa)
        assert!(!q_x_x.aeq_permissive(&q_a_b));
        assert!(!q_x_y.aeq_permissive(&q_a_a));
    }

    /// Corresponding free locals must have the same sort.
    #[test]
    fn test_aeq_permissive_sort_mismatch() {
        let mut ctx = setup();
        let int = ctx.int_sort();
        let bool_s = ctx.bool_sort();
        let mut q = ctx
            .build_quantifier_with_domain([("x", int), ("u", bool_s)])
            .unwrap();
        let x = q.typed_symbol("x").unwrap();
        let u = q.typed_symbol("u").unwrap();
        assert!(!x.aeq_permissive(&u));
        assert!(x.aeq_permissive(&x));
    }

    /// Freeness is judged from the perspective of the compared terms, not their origin: a body
    /// extracted from a quantifier has its variable *free*, so permissive mode may match it
    /// against another free local. Rejection of free-vs-bound applies only when the binder is
    /// part of the compared terms (see `test_aeq_permissive_under_binders`).
    #[test]
    fn test_aeq_permissive_extracted_body_is_free() {
        let mut ctx = setup();
        let (free, _) = free_p_v(&mut ctx, "x");
        let bound = parse(&mut ctx, "(forall ((x Int)) (p x))");
        let ATerm::Forall(_, body) = bound.repr() else {
            panic!("expected a forall")
        };
        // strict aeq rejects: the two locals have different ids
        assert!(!body.aeq(&free));
        // permissive accepts: both variables are free in the compared terms
        assert!(body.aeq_permissive(&free));
        assert!(free.aeq_permissive(body));
    }

    /// Bound variables (matched positionally) and free locals (matched permissively) coexist.
    #[test]
    fn test_aeq_permissive_under_binders() {
        let mut ctx = setup();
        let int = ctx.int_sort();

        // t1 = (forall ((z Int)) (q z x)), with x free
        let mut q1 = ctx
            .build_quantifier_with_domain([("x", int.clone())])
            .unwrap();
        let x = q1.typed_symbol("x").unwrap();
        let mut inner1 = q1
            .build_quantifier_with_domain([("z", int.clone())])
            .unwrap();
        let z = inner1.typed_symbol("z").unwrap();
        let body1 = inner1.typed_simp_app("q", [z, x]).unwrap();
        let t1 = inner1.typed_forall(body1).unwrap();

        // t2 = (forall ((w Int)) (q w y)), with y free
        let mut q2 = ctx
            .build_quantifier_with_domain([("y", int.clone())])
            .unwrap();
        let y = q2.typed_symbol("y").unwrap();
        let mut inner2 = q2
            .build_quantifier_with_domain([("w", int.clone())])
            .unwrap();
        let w = inner2.typed_symbol("w").unwrap();
        let body2 = inner2.typed_simp_app("q", [w.clone(), y.clone()]).unwrap();
        let t2 = inner2.typed_forall(body2).unwrap();

        // t3 = (forall ((w Int)) (q y w)): the bound/free positions are swapped
        let mut inner3 = q2.build_quantifier_with_domain([("w", int)]).unwrap();
        let w3 = inner3.typed_symbol("w").unwrap();
        let body3 = inner3.typed_simp_app("q", [y, w3]).unwrap();
        let t3 = inner3.typed_forall(body3).unwrap();

        assert!(!t1.aeq(&t2));
        assert!(t1.aeq_permissive(&t2));
        assert!(t2.aeq_permissive(&t1));
        // a bound variable cannot correspond to a free one, even permissively
        assert!(!t1.aeq_permissive(&t3));
    }
}

#[cfg(test)]
mod stack_safety {
    use super::*;
    use crate::ast::{CheckedApi, Context, Typecheck};
    use crate::untyped::UntypedAst;

    fn deep_not(ctx: &mut Context, depth: usize) -> Term {
        let mut t = UntypedAst
            .parse_term_str("true")
            .unwrap()
            .type_check(ctx)
            .unwrap();
        for _ in 0..depth {
            t = ctx.typed_not(t).unwrap();
        }
        t
    }

    #[test]
    fn aeq_is_flat() {
        let ok = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut ctx = Context::new();
                ctx.ensure_logic();
                let a = deep_not(&mut ctx, 100_000);
                let b = a.clone();
                let r = a.aeq(&b) && a.aeq_permissive(&b);
                std::mem::forget((a, b));
                r
            })
            .expect("spawn")
            .join();
        assert_eq!(ok.ok(), Some(true));
    }
}
