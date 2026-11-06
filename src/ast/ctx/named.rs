// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Where `:named` labels may occur (#162).
//!
//! A label `(! t :named f)` defines `f` as `t` (SMT-LIB 2.7, §4.1.6). By decision of the
//! specification (`Term.assertOk` and `Term.termOk` in `SmtLibSpec`), labels are `assert`'s alone,
//! and only at its top: an asserted term may be a chain of annotations, each carrying exactly one
//! attribute, a `:named`, as in `(! (! φ :named a) :named b)`, over a term with no label in it.
//! The terms of every other command have no label at all. The sort of a labelled term is not
//! restricted.

use crate::ast::alg;
use crate::ast::{Attribute, PatternArm, Repr, Str, SymbolQuote, Term};
use crate::raw::tc::TC;
use std::collections::HashSet;
use yaspar_macros::stack_safe;

/// The labels at the top of an asserted term, outermost first, each with the term it names.
///
/// An error if the term has a label anywhere else, or if an annotation with a label carries any
/// other attribute.
pub(crate) fn top_labels(t: &Term) -> TC<Vec<(Str, Term)>> {
    let mut labels = vec![];
    let mut current = t;
    while let alg::Term::Annotated(body, anns) = current.repr() {
        let [Attribute::Named(name)] = anns.as_slice() else {
            if let Some(name) = anns.iter().find_map(named) {
                return Err(format!(
                    "TC: named annotation {} must be the only attribute of its annotation!",
                    name.sym_quote()
                ));
            }
            break;
        };
        labels.push((name.clone(), body.clone()));
        current = body;
    }
    no_named(current)?;
    Ok(labels)
}

/// Check that `t` has no `:named` label anywhere.
pub(crate) fn no_named(t: &Term) -> TC<()> {
    match find_named(t) {
        None => Ok(()),
        Some(name) => Err(format!(
            "TC: named annotation {} is only allowed at the top of an assertion!",
            name.sym_quote()
        )),
    }
}

/// A `:named` label in `t`, if there is one.
fn find_named(t: &Term) -> Option<Str> {
    let mut finder = NamedFinder::default();
    find_named_rec(t, &mut finder);
    finder.found
}

#[derive(Default)]
struct NamedFinder {
    /// The label found, after which nothing else is walked.
    found: Option<Str>,
    /// The sub-terms already visited, which are not walked again.
    visited: HashSet<Term>,
}

/// Look for a label in `t`, visiting each distinct sub-term once.
#[stack_safe]
fn find_named_rec(t: &Term, finder: &mut NamedFinder) {
    if finder.found.is_some() || !finder.visited.insert(t.clone()) {
        return;
    }
    match t.repr() {
        alg::Term::Constant(..) | alg::Term::Global(..) | alg::Term::Local(..) => {}
        alg::Term::App(_, ts, _)
        | alg::Term::Distinct(ts)
        | alg::Term::And(ts)
        | alg::Term::Or(ts)
        | alg::Term::Xor(ts) => {
            for x in ts {
                find_named_rec(x, finder);
            }
        }
        alg::Term::Let(vs, body) => {
            for v in vs {
                find_named_rec(&v.2, finder);
            }
            find_named_rec(body, finder);
        }
        alg::Term::Exists(_, body) | alg::Term::Forall(_, body) => find_named_rec(body, finder),
        alg::Term::Matching(scrutinee, arms) => {
            find_named_rec(scrutinee, finder);
            for arm in arms {
                find_named_rec(arm_body(arm), finder);
            }
        }
        alg::Term::Annotated(body, anns) => {
            finder.found = anns.iter().find_map(named);
            for ann in anns {
                for p in attribute_terms(ann) {
                    find_named_rec(p, finder);
                }
            }
            find_named_rec(body, finder);
        }
        alg::Term::Eq(a, b) => {
            find_named_rec(a, finder);
            find_named_rec(b, finder);
        }
        alg::Term::Not(x) => find_named_rec(x, finder),
        alg::Term::Implies(ts, x) => {
            for y in ts {
                find_named_rec(y, finder);
            }
            find_named_rec(x, finder);
        }
        alg::Term::Ite(a, b, c) => {
            find_named_rec(a, finder);
            find_named_rec(b, finder);
            find_named_rec(c, finder);
        }
    }
}

fn named(ann: &Attribute) -> Option<Str> {
    match ann {
        Attribute::Named(name) => Some(name.clone()),
        _ => None,
    }
}

// The loops over match arms and attributes resume after a recursive call, where `#[stack_safe]`
// leaves the type of the loop variable to inference that has not seen it yet. These typed
// accessors give it one.

fn arm_body(arm: &PatternArm) -> &Term {
    &arm.body
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
