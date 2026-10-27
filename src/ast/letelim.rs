// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Let-elimination: inlining let-bound variables.
//!
//! Let-elimination expands all local variables introduced by `let`-bindings with their bound
//! terms. After let-elimination, the resulting term contains no `let`-bindings, which simplifies
//! subsequent analysis (e.g. substitution, free variable computation, CNF conversion).
//!
//! Use it via [`LetElim`]: `.let_elim(&mut context)`. It is a recursion made stack-safe by
//! `#[stack_safe]`, and caches the result for each shared sub-term.
//!
//! # Untouched sub-terms are shared, not rebuilt
//!
//! Most terms contain no `let` at all, and even in those that do, only the sub-terms mentioning
//! a let-bound variable actually change. So the recursion produces an `Option<Term>`, where
//! [`None`] means "this sub-term is unchanged" and `Some(t)` means "this sub-term became `t`".
//! A node whose children all report [`None`] reports [`None`] in turn, so it is never
//! re-allocated through the arena — the original is reused. Only the spine leading to an
//! inlined variable is rebuilt.
//!
//! Note: let-elimination may increase term size due to duplication of shared sub-terms. For the
//! inverse operation (re-introducing let-bindings to share common sub-terms), see
//! [`crate::ast::letintro`].

use crate::allocator::TermAllocator;
use crate::ast::{Attribute, Bottom, HasArena, PatternArm, Repr, Str, Term, alg};
use crate::containers::Mapping;
use crate::raw::alg::{LocalId, VarBinding};
use std::collections::HashMap;
use yaspar_macros::stack_safe;

/// Eliminates all let-bindings by applying substitutions properly
///
/// This trait assumes that the given object has been type-checked.
pub trait LetElim<Env> {
    fn let_elim(&self, env: &mut Env) -> Self;
}

impl<E> LetElim<E> for Term
where
    E: HasArena,
{
    fn let_elim(&self, env: &mut E) -> Self {
        let mut st = LetElimState::default();
        let_elim::let_elim_rec(self, &mut st, env).unwrap_or_else(|| self.clone())
    }
}

/// The let-eliminator that predates [`LetElim`], kept so that code written against it still
/// compiles. It caches its results across calls, so one eliminator reused on many terms shares
/// their common sub-terms.
#[deprecated(
    note = "use `LetElim::let_elim` instead; `LetEliminator` is no longer a `TermRecursor`"
)]
pub struct LetEliminator<'a, E> {
    arena: &'a mut E,
    state: LetElimState,
}

#[allow(deprecated)]
impl<'a, E> LetEliminator<'a, E>
where
    E: HasArena,
{
    /// Create a new let-eliminator backed by the given arena.
    #[deprecated(note = "use `LetElim::let_elim` instead")]
    pub fn create(arena: &'a mut E) -> Self {
        Self {
            arena,
            state: LetElimState::default(),
        }
    }

    /// Eliminate the `let`s in `t`, or return [`None`] when `t` has none and so is unchanged.
    #[deprecated(note = "use `LetElim::let_elim` instead")]
    pub fn recurse_on_term_no_err(&mut self, t: &Term) -> Option<Term> {
        let_elim::let_elim_rec(t, &mut self.state, self.arena)
    }

    /// [`Self::recurse_on_term_no_err`], which cannot fail.
    #[deprecated(note = "use `LetElim::let_elim` instead")]
    pub fn recurse_on_term(&mut self, t: &Term) -> Result<Option<Term>, Bottom> {
        Ok(let_elim::let_elim_rec(t, &mut self.state, self.arena))
    }
}

/// The uncached let-eliminator that predates [`LetElim`], kept so that code written against it
/// still compiles. Every call starts afresh.
#[deprecated(
    note = "use `LetElim::let_elim` instead; `LetEliminatorInner` is no longer a `TermRecursor`"
)]
pub struct LetEliminatorInner<'a, E> {
    arena: &'a mut E,
}

#[allow(deprecated)]
impl<'a, E> LetEliminatorInner<'a, E>
where
    E: HasArena,
{
    #[deprecated(note = "use `LetElim::let_elim` instead")]
    pub fn new(arena: &'a mut E) -> Self {
        Self { arena }
    }

    /// Eliminate the `let`s in `t`, or return [`None`] when `t` has none and so is unchanged.
    #[deprecated(note = "use `LetElim::let_elim` instead")]
    pub fn recurse_on_term_no_err(&mut self, t: &Term) -> Option<Term> {
        let_elim::let_elim_rec(t, &mut LetElimState::default(), self.arena)
    }

    /// [`Self::recurse_on_term_no_err`], which cannot fail.
    #[deprecated(note = "use `LetElim::let_elim` instead")]
    pub fn recurse_on_term(&mut self, t: &Term) -> Result<Option<Term>, Bottom> {
        Ok(self.recurse_on_term_no_err(t))
    }
}

/// The state of [`LetElim::let_elim`].
#[derive(Default)]
struct LetElimState {
    /// Environment stack: each frame maps a local variable id to the substituted term, or to
    /// [`None`] for a quantifier/match-bound variable, which is not substituted.
    env: Vec<HashMap<LocalId, Option<Term>>>,
    /// The result for each sub-term already eliminated.
    cache: HashMap<Term, Option<Term>>,
}

/// Record the result `rec` of the child `originals[idx]`, where [`None`] means unchanged.
///
/// Nothing is allocated unless a child really changed: the output vector is created on the first
/// change, seeded with the unchanged children already passed over.
fn push_if_changed<T: Clone>(
    out: &mut Option<Vec<T>>,
    originals: &[T],
    idx: usize,
    rec: Option<T>,
) {
    match rec {
        Some(rec) => out
            .get_or_insert_with(|| {
                let mut built = Vec::with_capacity(originals.len());
                built.extend_from_slice(&originals[..idx]);
                built
            })
            .push(rec),
        None => {
            if let Some(built) = out {
                built.push(originals[idx].clone())
            }
        }
    }
}

/// Rebuild the `distinct`, `and`, `or`, `xor` or application `t` over new arguments.
fn rebuild_nary<E: HasArena>(env: &mut E, t: &Term, ts: Vec<Term>) -> Term {
    match t.repr() {
        alg::Term::App(id, _, s) => env.arena().app(id.clone(), ts, s.clone()),
        alg::Term::Distinct(_) => env.arena().distinct(ts),
        alg::Term::And(_) => env.arena().and(ts),
        alg::Term::Or(_) => env.arena().or(ts),
        alg::Term::Xor(_) => env.arena().xor(ts),
        _ => unreachable!("rebuild_nary is only called on an n-ary node"),
    }
}

// The loops over match arms and attributes resume after a recursive call, where `#[stack_safe]`
// leaves the type of the loop variable to inference that has not seen it yet. These typed
// accessors give it one.

fn arm_body(arm: &PatternArm) -> &Term {
    &arm.body
}

fn push_arm_scope(st: &mut LetElimState, arm: &PatternArm) {
    st.env.push(
        arm.pattern
            .variables_and_ids()
            .into_iter()
            .map(|(_, id)| (id, None))
            .collect(),
    );
}

/// Let-elimination proper, which recurses over a term of unbounded nesting. Every function returns
/// [`None`] to mean "unchanged", and a node builds the vector of its new children only once one of
/// them has changed.
#[stack_safe]
mod let_elim {
    use super::*;

    pub(super) fn let_elim_rec<E: HasArena>(
        t: &Term,
        st: &mut LetElimState,
        env: &mut E,
    ) -> Option<Term> {
        if let Some(r) = st.cache.get(t) {
            return r.clone();
        }
        let r: Option<Term> = match t.repr() {
            alg::Term::Constant(..) | alg::Term::Global(..) => None,
            alg::Term::Local(l) => st.env.lookup(&l.id).flatten(),
            alg::Term::App(_, ts, _)
            | alg::Term::Distinct(ts)
            | alg::Term::And(ts)
            | alg::Term::Or(ts)
            | alg::Term::Xor(ts) => {
                let ts_rec = let_elim_terms(ts, st, env);
                ts_rec.map(|ts_rec| rebuild_nary(env, t, ts_rec))
            }
            // the `let` node itself is gone, so this is always a change
            alg::Term::Let(vs, body) => {
                let frame = let_elim_bindings(vs, st, env);
                st.env.push(frame);
                let body_rec = let_elim_rec(body, st, env);
                st.env.pop();
                Some(body_rec.unwrap_or_else(|| body.clone()))
            }
            alg::Term::Exists(vs, body) | alg::Term::Forall(vs, body) => {
                st.env.push(vs.iter().map(|v| (v.1, None)).collect());
                let body_rec = let_elim_rec(body, st, env);
                st.env.pop();
                body_rec.map(|body_rec| {
                    if matches!(t.repr(), alg::Term::Forall(..)) {
                        env.arena().forall(vs.to_vec(), body_rec)
                    } else {
                        env.arena().exists(vs.to_vec(), body_rec)
                    }
                })
            }
            alg::Term::Matching(scrutinee, cases) => {
                let scrutinee_rec = let_elim_rec(scrutinee, st, env);
                let arms = let_elim_arms(cases, st, env);
                if scrutinee_rec.is_none() && arms.is_none() {
                    None
                } else {
                    let scrutinee_new = scrutinee_rec.unwrap_or_else(|| scrutinee.clone());
                    let arms_new = arms.unwrap_or_else(|| cases.to_vec());
                    Some(env.arena().matching(scrutinee_new, arms_new))
                }
            }
            alg::Term::Annotated(body, anns) => {
                let body_rec = let_elim_rec(body, st, env);
                let anns_rec = let_elim_attributes(anns, st, env);
                if body_rec.is_none() && anns_rec.is_none() {
                    None
                } else {
                    let body_new = body_rec.unwrap_or_else(|| body.clone());
                    let anns_new = anns_rec.unwrap_or_else(|| anns.to_vec());
                    Some(env.arena().annotated(body_new, anns_new))
                }
            }
            alg::Term::Eq(a, b) => {
                let a_rec = let_elim_rec(a, st, env);
                let b_rec = let_elim_rec(b, st, env);
                if a_rec.is_none() && b_rec.is_none() {
                    None
                } else {
                    let a_new = a_rec.unwrap_or_else(|| a.clone());
                    let b_new = b_rec.unwrap_or_else(|| b.clone());
                    Some(env.arena().eq(a_new, b_new))
                }
            }
            alg::Term::Not(x) => {
                let x_rec = let_elim_rec(x, st, env);
                x_rec.map(|x_rec| env.arena().not(x_rec))
            }
            alg::Term::Implies(ts, concl) => {
                let ts_rec = let_elim_terms(ts, st, env);
                let concl_rec = let_elim_rec(concl, st, env);
                if ts_rec.is_none() && concl_rec.is_none() {
                    None
                } else {
                    let premises = ts_rec.unwrap_or_else(|| ts.to_vec());
                    let conclusion = concl_rec.unwrap_or_else(|| concl.clone());
                    Some(env.arena().implies(premises, conclusion))
                }
            }
            alg::Term::Ite(b, x, e) => {
                let b_rec = let_elim_rec(b, st, env);
                let x_rec = let_elim_rec(x, st, env);
                let e_rec = let_elim_rec(e, st, env);
                if b_rec.is_none() && x_rec.is_none() && e_rec.is_none() {
                    None
                } else {
                    let b_new = b_rec.unwrap_or_else(|| b.clone());
                    let x_new = x_rec.unwrap_or_else(|| x.clone());
                    let e_new = e_rec.unwrap_or_else(|| e.clone());
                    Some(env.arena().ite(b_new, x_new, e_new))
                }
            }
        };
        st.cache.insert(Term::clone(t), r.clone());
        r
    }

    /// The new children, or [`None`] when every one of them is unchanged.
    fn let_elim_terms<E: HasArena>(
        ts: &[Term],
        st: &mut LetElimState,
        env: &mut E,
    ) -> Option<Vec<Term>> {
        let mut out = None;
        let mut i = 0usize;
        while i < ts.len() {
            let rec = let_elim_rec(&ts[i], st, env);
            push_if_changed(&mut out, ts, i, rec);
            i += 1;
        }
        out
    }

    /// The scope frame of a `let`: each bound variable mapped to its eliminated right-hand side,
    /// or to the original one when it is unchanged.
    fn let_elim_bindings<E: HasArena>(
        vs: &[VarBinding<Str, Term>],
        st: &mut LetElimState,
        env: &mut E,
    ) -> HashMap<LocalId, Option<Term>> {
        let mut frame = HashMap::with_capacity(vs.len());
        let mut i = 0usize;
        while i < vs.len() {
            let rec = let_elim_rec(&vs[i].2, st, env);
            frame.insert(vs[i].1, Some(rec.unwrap_or_else(|| vs[i].2.clone())));
            i += 1;
        }
        frame
    }

    /// The new arms, each eliminated under the scope of its pattern, or [`None`] when every one
    /// of them is unchanged.
    fn let_elim_arms<E: HasArena>(
        cases: &[PatternArm],
        st: &mut LetElimState,
        env: &mut E,
    ) -> Option<Vec<PatternArm>> {
        let mut out = None;
        let mut i = 0usize;
        while i < cases.len() {
            push_arm_scope(st, &cases[i]);
            let rec = let_elim_rec(arm_body(&cases[i]), st, env);
            st.env.pop();
            let arm = rec.map(|body| PatternArm {
                pattern: cases[i].pattern.clone(),
                body,
            });
            push_if_changed(&mut out, cases, i, arm);
            i += 1;
        }
        out
    }

    /// The new attributes, or [`None`] when every one of them is unchanged.
    fn let_elim_attributes<E: HasArena>(
        anns: &[Attribute],
        st: &mut LetElimState,
        env: &mut E,
    ) -> Option<Vec<Attribute>> {
        let mut out = None;
        let mut i = 0usize;
        while i < anns.len() {
            let rec = match &anns[i] {
                Attribute::Pattern(ps) => let_elim_terms(ps, st, env).map(Attribute::Pattern),
                #[cfg(feature = "no-pattern")]
                Attribute::NoPattern(p) => let_elim_rec(p, st, env).map(Attribute::NoPattern),
                _ => None,
            };
            push_if_changed(&mut out, anns, i, rec);
            i += 1;
        }
        out
    }
}

#[cfg(test)]
#[allow(deprecated)] // `test_let_elim_unchanged_is_none` exercises `LetEliminator`
mod tests {
    use super::*;
    use crate::ast::fv::FreeLocalVars;
    use crate::ast::{AlphaEquiv, Context, Typecheck};
    use crate::untyped::UntypedAst;

    #[test]
    fn test_let_elim1() {
        let mut context = Context::default();
        context.ensure_logic();
        let t = UntypedAst
            .parse_term_str("(let ((x (+ 1 2))) (* x x))")
            .unwrap()
            .type_check(&mut context)
            .unwrap()
            .let_elim(&mut context);
        let equiv = UntypedAst
            .parse_term_str("(* (+ 1 2) (+ 1 2))")
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        assert_eq!(t, equiv);
    }

    #[test]
    fn test_let_elim2() {
        let mut context = Context::default();
        context.ensure_logic();
        let t = UntypedAst
            .parse_term_str("(let ((x (+ 1 2))) (! (* x x) :pattern (x)))")
            .unwrap()
            .type_check(&mut context)
            .unwrap()
            .let_elim(&mut context);
        let equiv = UntypedAst
            .parse_term_str("(! (* (+ 1 2) (+ 1 2)) :pattern ((+ 1 2)))")
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        assert_eq!(t, equiv);
    }

    #[test]
    fn test_let_elim_xor() {
        let mut context = Context::default();
        context.ensure_logic();
        let t = UntypedAst
            .parse_term_str("(let ((p true) (q false)) (xor p q))")
            .unwrap()
            .type_check(&mut context)
            .unwrap()
            .let_elim(&mut context);
        let equiv = UntypedAst
            .parse_term_str("(xor true false)")
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        assert_eq!(t, equiv);
    }

    /// A term with no `let` must come back as the very same term, not a rebuilt copy.
    ///
    /// `recurse_on_term` reporting [`None`] is what guarantees nothing was re-allocated.
    #[test]
    fn test_let_elim_unchanged_is_none() {
        let mut context = Context::default();
        context.ensure_logic();
        let t = UntypedAst
            .parse_term_str(
                "(forall ((y Int)) (! (=> (> y 0) (distinct (ite true y 1) 2)) :named a))",
            )
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        assert_eq!(
            LetEliminator::create(&mut context).recurse_on_term_no_err(&t),
            None
        );
        assert_eq!(t.let_elim(&mut context), t);
    }

    /// Only the spine down to the inlined variable is rebuilt; the untouched sibling of a
    /// changed node is reported unchanged and so stays shared.
    #[test]
    fn test_let_elim_partial_change() {
        let mut context = Context::default();
        context.ensure_logic();
        let t = UntypedAst
            .parse_term_str("(and (let ((x 1)) (> x 0)) (< 2 3))")
            .unwrap()
            .type_check(&mut context)
            .unwrap()
            .let_elim(&mut context);
        let equiv = UntypedAst
            .parse_term_str("(and (> 1 0) (< 2 3))")
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        assert_eq!(t, equiv);
    }

    /// Elimination must not leave a let-bound variable behind.
    ///
    /// Every local in a well-formed term is bound, and elimination deletes the `let` binders,
    /// so a variable that was not replaced by its bound term would show up here as a free local
    /// variable. The quantifier-bound `y` stays bound, so it is not free.
    #[test]
    fn test_let_elim_leaves_no_free_locals() {
        let mut context = Context::default();
        context.ensure_logic();
        let t = UntypedAst
            .parse_term_str(
                "(let ((a 1)) (forall ((y Int)) (let ((b (+ a y))) (! (= b b) :pattern (b)))))",
            )
            .unwrap()
            .type_check(&mut context)
            .unwrap()
            .let_elim(&mut context);
        assert!(
            t.free_loc_vars().is_empty(),
            "{t} still has free local variables"
        );
    }

    /// A `let` inside one match arm is eliminated while the untouched arms stay shared.
    ///
    /// This pins down that rebuilt arms keep their own patterns: mispairing arms with patterns
    /// would still produce a well-sorted term, just the wrong one.
    #[test]
    fn test_let_elim_under_match() {
        let mut context = Context::default();
        UntypedAst
            .parse_script_str(
                "(set-logic ALL)
                 (declare-datatypes ((Color 0)) (((red) (green) (blue))))
                 (declare-const c Color)",
            )
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        let t = UntypedAst
            .parse_term_str("(match c ((red (let ((x 1)) (+ x 0))) (green 2) (blue 3)))")
            .unwrap()
            .type_check(&mut context)
            .unwrap()
            .let_elim(&mut context);
        let equiv = UntypedAst
            .parse_term_str("(match c ((red (+ 1 0)) (green 2) (blue 3)))")
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        assert_eq!(t, equiv);
    }

    /// A `let` inside a quantifier body must still be eliminated, and the quantifier rebuilt.
    ///
    /// Compared up to alpha equivalence, since each `type_check` mints a fresh id for `y`.
    #[test]
    fn test_let_elim_under_quantifier() {
        let mut context = Context::default();
        context.ensure_logic();
        let t = UntypedAst
            .parse_term_str("(forall ((y Int)) (let ((x (+ y 1))) (= x x)))")
            .unwrap()
            .type_check(&mut context)
            .unwrap()
            .let_elim(&mut context);
        let equiv = UntypedAst
            .parse_term_str("(forall ((y Int)) (= (+ y 1) (+ y 1)))")
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        assert!(t.aeq(&equiv), "{t} is not alpha-equivalent to {equiv}");
    }
}

#[cfg(test)]
mod stack_safety {
    use super::*;
    use crate::ast::fv::FreeLocalVars;
    use crate::ast::{Context, Typecheck};
    use crate::untyped::UntypedAst;

    /// `(forall ((x0 Int)) (let ((y0 x0)) (forall ((x1 Int)) (let ((y1 (+ y0 x1))) (… (> y 0))))))`.
    fn deep_binders(depth: usize) -> String {
        let mut s = String::from("(forall ((x0 Int)) (let ((y0 x0)) ");
        for i in 1..depth {
            s.push_str(&format!(
                "(forall ((x{i} Int)) (let ((y{i} (+ y{} x{i}))) ",
                i - 1
            ));
        }
        s.push_str(&format!("(> y{} 0)", depth - 1));
        s.push_str(&"))".repeat(depth));
        s
    }

    #[test]
    fn let_elim_is_flat() {
        let ok = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut ctx = Context::new();
                ctx.ensure_logic();
                let src = deep_binders(5_000);
                let u = UntypedAst.parse_term_str(&src).unwrap();
                let t = u.type_check(&mut ctx).unwrap();
                let r = t.let_elim(&mut ctx);
                // every `let` is gone, and with it every let-bound variable
                let ok = !r.to_string().contains("let") && r.free_loc_vars().is_empty();
                std::mem::forget((u, t, r));
                ok
            })
            .expect("spawn")
            .join();
        assert_eq!(ok.ok(), Some(true));
    }
}
