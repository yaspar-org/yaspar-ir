// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! The checks on a `match` expression, shared by the type checker and the
//! [`MatchContext`](crate::ast::MatchContext) builder.
//!
//! A [`MatchChecker`] is created for one scrutinee and sees the arms one at a time:
//!
//! 1. [`ctor_arm`](MatchChecker::ctor_arm) or [`wildcard_arm`](MatchChecker::wildcard_arm)
//!    resolves an arm's pattern, and returns the variables it binds;
//! 2. once the arm's body has been checked under those variables,
//!    [`add_arm`](MatchChecker::add_arm) checks that its sort agrees with the other arms, and
//!    records which constructors it covers;
//! 3. [`finish`](MatchChecker::finish) checks that the arms are exhaustive.

use super::{TC, TCEnvGen, sort_mismatch, tc_determine_datatype_sort_map};
use crate::allocator::LocalVarAllocator;
use crate::ast::{SymbolQuote, Theory};
use crate::containers::sanitize_bindings;
use crate::raw::alg::VarBinding;
use crate::raw::instance::{FetchSort, HasArenaAlt, Pattern, Sort, Str, Term};
use std::collections::{HashMap, HashSet};
use std::fmt::Display;

/// What a `match` over one scrutinee has seen so far.
pub(crate) struct MatchChecker {
    scrutinee_sort: Sort,
    /// Each constructor of the scrutinee's sort, with the sorts of its arguments.
    constructors: HashMap<Str, Vec<Sort>>,
    /// The constructors no arm has matched yet.
    unseen: HashSet<Str>,
    /// Whether the arms so far are exhaustive.
    covered: bool,
    /// The sort of the first arm's body, which every other arm must share.
    arm_sort: Option<Sort>,
}

/// An arm's pattern, and the variables it binds.
pub(crate) type ArmScope = (Pattern, Vec<VarBinding<Str, Sort>>);

impl MatchChecker {
    /// Start checking a `match` on `scrutinee`, which must be of a datatype sort.
    pub(crate) fn new<L>(env: &mut TCEnvGen<'_, L>, scrutinee: &Term, meta: &str) -> TC<Self> {
        if !env.meta.theories.contains(&Theory::Datatypes) {
            return Err("TC: current logic does not support the theory of datatypes!".into());
        }
        let constructors = tc_determine_datatype_sort_map(env, scrutinee, meta)?;
        Ok(Self {
            scrutinee_sort: scrutinee.get_sort(env),
            unseen: constructors.keys().cloned().collect(),
            constructors,
            covered: false,
            arm_sort: None,
        })
    }

    pub(crate) fn scrutinee_sort(&self) -> &Sort {
        &self.scrutinee_sort
    }

    pub(crate) fn constructors(&self) -> &HashMap<Str, Vec<Sort>> {
        &self.constructors
    }

    pub(crate) fn unseen(&self) -> &HashSet<Str> {
        &self.unseen
    }

    pub(crate) fn is_covered(&self) -> bool {
        self.covered
    }

    /// Resolve the pattern `(ctor x₁ … xₙ)`, or `ctor` alone when `vars` is empty. A `None` among
    /// `vars` is a `_` that binds nothing. `meta` locates `ctor`, and each variable comes with what
    /// locates it.
    pub(crate) fn ctor_arm<L>(
        &self,
        env: &mut TCEnvGen<'_, L>,
        ctor: Str,
        meta: &str,
        vars: Vec<Option<(Str, String)>>,
    ) -> TC<ArmScope> {
        let Some(sorts) = self.constructors.get(&ctor) else {
            return Err(not_a_constructor(&ctor, meta, &self.scrutinee_sort));
        };
        if sorts.len() != vars.len() {
            return Err(arity_mismatch(&ctor, meta, sorts.len(), vars.len()));
        }
        let mut arguments = Vec::with_capacity(vars.len());
        let mut bindings = Vec::with_capacity(vars.len());
        for (var, sort) in vars.into_iter().zip(sorts) {
            match var {
                None => arguments.push(None),
                Some((name, name_meta)) => {
                    env.meta
                        .check_sym_validity(&name)
                        .map_err(|e| format!("TC: {e}{name_meta}"))?;
                    let id = env.arena.new_local();
                    arguments.push(Some((name.clone(), id)));
                    bindings.push(VarBinding(name, id, sort.clone()));
                }
            }
        }
        sanitize_bindings(&bindings, |v| v.0.clone())?;
        let pattern = if arguments.is_empty() {
            Pattern::Ctor(ctor)
        } else {
            Pattern::Applied { ctor, arguments }
        };
        Ok((pattern, bindings))
    }

    /// Resolve the pattern `x`, or `_` when `var` is `None`, which matches anything.
    ///
    /// The concrete syntax cannot tell a variable from a nullary constructor, so with
    /// `ctor_if_nullary` a `var` naming one is that constructor's pattern instead. Without it,
    /// naming any constructor is an error.
    pub(crate) fn wildcard_arm<L>(
        &self,
        env: &mut TCEnvGen<'_, L>,
        var: Option<(Str, String)>,
        ctor_if_nullary: bool,
    ) -> TC<ArmScope> {
        let Some((name, meta)) = var else {
            return Ok((Pattern::Wildcard(None), vec![]));
        };
        if let Some(sorts) = self.constructors.get(&name) {
            return if !ctor_if_nullary {
                Err(format!(
                    "TC: variable {}{meta} is a constructor; it cannot be used as a wildcard variable for matching a term of sort {}!",
                    name.sym_quote(),
                    self.scrutinee_sort
                ))
            } else if sorts.is_empty() {
                Ok((Pattern::Ctor(name), vec![]))
            } else {
                Err(arity_mismatch(&name, &meta, sorts.len(), 0))
            };
        }
        env.meta
            .check_sym_validity(&name)
            .map_err(|e| format!("TC: {e}{meta}"))?;
        let id = env.arena.new_local();
        let binding = VarBinding(name.clone(), id, self.scrutinee_sort.clone());
        Ok((Pattern::Wildcard(Some((name, id))), vec![binding]))
    }

    /// Record an arm with the given `pattern` and checked `body`, which `shown` and `meta` locate.
    /// Its sort must be that of the earlier arms.
    pub(crate) fn add_arm<E: HasArenaAlt>(
        &mut self,
        env: &mut E,
        pattern: &Pattern,
        body: &Term,
        shown: impl Display,
        meta: &str,
    ) -> TC<()> {
        let sort = body.get_sort(env);
        match &self.arm_sort {
            Some(expected) if *expected != sort => {
                return sort_mismatch(expected, &sort, shown, meta);
            }
            Some(_) => {}
            None => self.arm_sort = Some(sort),
        }
        match pattern {
            Pattern::Wildcard(_) => self.covered = true,
            Pattern::Ctor(ctor) | Pattern::Applied { ctor, .. } => {
                self.unseen.remove(ctor);
            }
        }
        if self.unseen.is_empty() {
            self.covered = true;
        }
        Ok(())
    }

    /// Check that the arms seen are exhaustive. `meta` locates the `match` expression.
    pub(crate) fn finish(&self, meta: &str) -> TC<()> {
        if self.arm_sort.is_none() {
            return Err(format!(
                "TC: match expression{meta} must have at least one arm!"
            ));
        }
        if self.covered {
            return Ok(());
        }
        let mut unseen: Vec<String> = self.unseen.iter().map(|c| c.sym_quote()).collect();
        unseen.sort();
        Err(format!(
            "TC: arms for constructors {} are needed in the match expression{meta}!",
            unseen.join(", ")
        ))
    }
}

fn not_a_constructor(ctor: &Str, meta: &str, sort: &Sort) -> String {
    format!(
        "TC: {}{meta} is not a constructor of sort {sort}!",
        ctor.sym_quote()
    )
}

fn arity_mismatch(ctor: &Str, meta: &str, expected: usize, given: usize) -> String {
    format!(
        "TC: constructor {}{meta} expects {expected} argument(s), but {given} are given!",
        ctor.sym_quote()
    )
}
