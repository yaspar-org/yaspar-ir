// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Free variable computation for terms.
//!
//! This module provides the [`FreeLocalVars`] trait, which computes the set of free (unbound)
//! local variables in a term. A variable is free if it is not bound by any enclosing `let`,
//! `forall`, `exists`, or `match` binder.
//!
//! Use [`is_closed`] as a convenience check for whether a term has
//! no free local variables.

use crate::ast::alg::{self, LocalId};
use crate::ast::{Attribute, PatternArm, Repr, Str, Term};
use std::collections::HashSet;
use yaspar_macros::stack_safe;

/// Compute the set of free local variables in a term.
///
/// A local variable is free if it is not bound by any enclosing binder (`let`, `forall`,
/// `exists`, or `match` pattern).
pub trait FreeLocalVars {
    fn free_loc_vars(&self) -> HashSet<(Str, LocalId)>;
}

impl FreeLocalVars for Term {
    fn free_loc_vars(&self) -> HashSet<(Str, LocalId)> {
        let mut finder = FreeLocalVariableFinder::default();
        fv_rec(self, &mut finder);
        finder.vars
    }
}

#[derive(Default)]
struct FreeLocalVariableFinder {
    vars: HashSet<(Str, LocalId)>,
    /// The sub-terms already visited, which are not walked again. A sub-term's locals are the
    /// same wherever it occurs, and every binder introduces fresh ids, so the variables a binder
    /// removes are never free elsewhere and skipping a revisit cannot change the answer.
    visited: HashSet<Term>,
}

impl FreeLocalVariableFinder {
    fn remove_bindings<T, F>(&mut self, bindings: impl Iterator<Item = T>, f: F)
    where
        F: Fn(T) -> (Str, LocalId),
    {
        for b in bindings {
            let loc = f(b);
            self.vars.remove(&loc);
        }
    }
}

/// Collect the free local variables of `t` into `finder`, which recurses over a term of unbounded
/// nesting.
#[stack_safe]
fn fv_rec(t: &Term, finder: &mut FreeLocalVariableFinder) {
    if finder.visited.contains(t) {
        return;
    }
    match t.repr() {
        alg::Term::Constant(..) | alg::Term::Global(..) => {}
        alg::Term::Local(l) => {
            finder.vars.insert((l.symbol.clone(), l.id));
        }
        alg::Term::App(_, ts, _)
        | alg::Term::Distinct(ts)
        | alg::Term::And(ts)
        | alg::Term::Or(ts)
        | alg::Term::Xor(ts) => {
            for x in ts {
                fv_rec(x, finder);
            }
        }
        alg::Term::Let(vs, body) => {
            for v in vs {
                fv_rec(&v.2, finder);
            }
            fv_rec(body, finder);
            finder.remove_bindings(vs.iter(), |v| (v.0.clone(), v.1));
        }
        alg::Term::Exists(vs, body) | alg::Term::Forall(vs, body) => {
            finder.remove_bindings(vs.iter(), |v| (v.0.clone(), v.1));
            fv_rec(body, finder);
            finder.remove_bindings(vs.iter(), |v| (v.0.clone(), v.1));
        }
        alg::Term::Matching(scrutinee, arms) => {
            fv_rec(scrutinee, finder);
            for arm in arms {
                fv_rec(arm_body(arm), finder);
                finder.remove_bindings(arm_variables(arm).into_iter(), |v| v);
            }
        }
        alg::Term::Annotated(body, anns) => {
            fv_rec(body, finder);
            for ann in anns {
                for p in attribute_terms(ann) {
                    fv_rec(p, finder);
                }
            }
        }
        alg::Term::Eq(a, b) => {
            fv_rec(a, finder);
            fv_rec(b, finder);
        }
        alg::Term::Not(x) => fv_rec(x, finder),
        alg::Term::Implies(ts, x) => {
            for y in ts {
                fv_rec(y, finder);
            }
            fv_rec(x, finder);
        }
        alg::Term::Ite(a, b, c) => {
            fv_rec(a, finder);
            fv_rec(b, finder);
            fv_rec(c, finder);
        }
    }
    finder.visited.insert(Term::clone(t));
}

// The loops over match arms and attributes resume after a recursive call, where `#[stack_safe]`
// leaves the type of the loop variable to inference that has not seen it yet. These typed
// accessors give it one.

fn arm_body(arm: &PatternArm) -> &Term {
    &arm.body
}

fn arm_variables(arm: &PatternArm) -> Vec<(Str, LocalId)> {
    arm.pattern.variables_and_ids()
}

/// The sub-terms of an attribute: those of `:pattern` and `:no-pattern`, and none otherwise.
fn attribute_terms(ann: &Attribute) -> &[Term] {
    match ann {
        Attribute::Pattern(ps) => ps,
        #[cfg(feature = "no-pattern")]
        Attribute::NoPattern(p) => std::slice::from_ref(p),
        _ => &[],
    }
}

/// check whether a term is closed; i.e. no open local variables
pub fn is_closed(t: &Term) -> bool {
    t.free_loc_vars().is_empty()
}

#[cfg(test)]
mod stack_safety {
    use super::*;
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
    fn free_loc_vars_is_flat() {
        let ok = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut ctx = Context::new();
                ctx.ensure_logic();
                let src = deep_binders(5_000);
                let u = UntypedAst.parse_term_str(&src).unwrap();
                let t = u.type_check(&mut ctx).unwrap();
                let r = t.free_loc_vars().is_empty();
                std::mem::forget((u, t));
                r
            })
            .expect("spawn")
            .join();
        assert_eq!(ok.ok(), Some(true));
    }
}
