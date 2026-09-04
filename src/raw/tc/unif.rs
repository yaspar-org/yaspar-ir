// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::allocator::SortAllocator;
use crate::ast::{HasArenaAlt, Sort, Str, TC};
use crate::traits::Repr;
use std::collections::HashMap;
use yaspar_macros::stack_safe;

/// A [SortSubst] is a partial substitution from sort variables to ground sorts (sorts with no open sort variables)
///
/// If a variable does not map to a ground sort, it maps to [None].
pub type SortSubst = HashMap<Str, Option<Sort>>;

/// Unify a ground sort with an expected sort with potential open sort variables; update the
/// substitution if necessary
#[stack_safe]
pub(crate) mod unify {
    use super::*;

    pub fn sort_unification(subst: &mut SortSubst, expected: &Sort, ground: &Sort) -> TC<bool> {
        // 1. if [expected] has arity > 0, then it's not possible for [expected] itself to be parametric
        if expected.1.is_empty() {
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
                ground, expected,
            ))
        } else {
            // 2. [expected] and [ground]'s sort parameters are recursively unified
            let mut i = 0usize;
            while i < expected.1.len() {
                if !sort_unification(subst, &expected.1[i], &ground.1[i])? {
                    return Ok(false);
                }
                i += 1;
            }
            // 3. in this case, we know all sort parameters match up, so sorts are unified
            Ok(true)
        }
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

#[stack_safe]
pub(crate) mod substitute {
    use super::*;

    pub(crate) fn apply_subst<A: HasArenaAlt>(arena: &mut A, subst: &SortSubst, s: &Sort) -> Sort {
        if s.1.is_empty() {
            let sym = &s.repr().0.symbol;
            if let Some(Some(v)) = subst.get(sym) {
                v.clone()
            } else {
                s.clone()
            }
        } else {
            let mut ss: Vec<Sort> = Vec::with_capacity(s.1.len());
            let mut i = 0usize;
            while i < s.1.len() {
                ss.push(apply_subst(arena, subst, &s.1[i]));
                i += 1;
            }
            arena.arena_alt().sort(s.repr().0.clone(), ss)
        }
    }
}

/// instantiate a given sort substitution with a sequence of (expected, ground) sort pairs
pub fn instantiate_subst<'a, 'b>(
    subst: &mut SortSubst,
    eg_pairs: impl IntoIterator<Item = (&'a Sort, &'b Sort)>,
) -> TC<bool> {
    for (expected, ground) in eg_pairs {
        if !sort_unification(subst, expected, ground)? {
            return Ok(false);
        }
    }
    Ok(true)
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

#[cfg(test)]
mod stack_safety {
    use super::*;
    use crate::allocator::ObjectAllocatorExt;
    use crate::ast::Context;

    /// `Array Int (Array Int (… Int))`, nested `depth` deep.
    fn deep_array(ctx: &mut Context, depth: usize) -> Sort {
        let mut s = ctx.int_sort();
        for _ in 0..depth {
            let idx = ctx.int_sort();
            s = ctx.array_sort(idx, s);
        }
        s
    }

    #[test]
    fn unification_is_flat() {
        let ok = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut ctx = Context::new();
                ctx.ensure_logic();
                let s = deep_array(&mut ctx, 100_000);
                let mut subst = empty_subst(&[]);
                let unified = sort_unification(&mut subst, &s, &s).unwrap();
                let applied = apply_subst(&mut ctx, &subst, &s);
                let r = unified && applied == s;
                std::mem::forget((s, applied));
                r
            })
            .expect("spawn")
            .join();
        assert_eq!(ok.ok(), Some(true));
    }
}
