// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::allocator::SortAllocator;
use crate::ast::{HasArenaAlt, Sort, Str, TC};
use crate::traits::Repr;
use std::collections::HashMap;

/// A [SortSubst] is a substitution from sort variables to ground sorts (sorts with no open variables)
pub(crate) type SortSubst = HashMap<Str, Option<Sort>>;

/// Unify a ground sort with an expected sort with potential open sort variables; update the
/// substitution if necessary
pub fn sort_unification(subst: &mut SortSubst, expected: &Sort, ground: &Sort) -> TC<bool> {
    // 1. if [ground] has arity > 0, then it's not possible for [expected] itself to be parametric
    if ground.1.is_empty() {
        // 2. in this case, it is possible for expected to be a variable, so we must check it
        let esymb = &expected.repr().0.symbol;
        if let Some(v) = subst.get(esymb) {
            // 3. then it is a variable,
            match v {
                None => {
                    // 3.1. but this variable is not unified, so we unify it with a ground type
                    subst.insert(esymb.clone(), Some(ground.clone()));
                    Ok(true)
                }
                Some(v) => Ok(*v == *ground), // otherwise, we must make sure the unified sort matches with [ground]
            }
        } else {
            // 3. then expected and ground must be equal
            Ok(*expected == *ground)
        }
    } else if expected.1.len() != ground.1.len() {
        Err(format!(
            "TC: sort mismatch: {} and {} cannot be unified!",
            ground, expected
        ))
    } else {
        // 2. [expected] and [ground]'s sort parameters are recursively unified
        for (e, g) in expected.1.iter().zip(ground.1.iter()) {
            if !sort_unification(subst, e, g)? {
                return Ok(false);
            }
        }
        // 3. in this case, we know all sort parameters match up, so sorts are unified
        Ok(true)
    }
}

pub fn empty_subst(vs: &[Str]) -> SortSubst {
    vs.iter().map(|s| (s.clone(), None)).collect()
}

/// Return variables in a substitutions that have not determined a sort
pub fn subst_missed_vars(subst: &SortSubst) -> Vec<Str> {
    subst
        .iter()
        .filter_map(|(k, v)| if v.is_none() { Some(k.clone()) } else { None })
        .collect()
}

pub(crate) fn apply_subst<A: HasArenaAlt>(arena: &mut A, subst: &SortSubst, s: &Sort) -> Sort {
    if s.1.is_empty() {
        let sym = &s.repr().0.symbol;
        if let Some(Some(v)) = subst.get(sym) {
            v.clone()
        } else {
            s.clone()
        }
    } else {
        let ss = s.1.iter().map(|s| apply_subst(arena, subst, s)).collect();
        arena.arena_alt().sort(s.repr().0.clone(), ss)
    }
}

pub fn format_subst(subst: &SortSubst) -> String {
    subst
        .iter()
        .map(|(k, v)| match v {
            None => {
                format!("?/{}", k)
            }
            Some(v) => {
                format!("{}/{}", v, k)
            }
        })
        .collect::<Vec<_>>()
        .join(", ")
}
