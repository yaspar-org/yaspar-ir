// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::allocator::ObjectAllocatorExt;
use crate::ast::{ATerm, FetchSort, HasArena, HasArenaAlt, TC, Term};
use crate::raw::tc::sort_mismatch;
use crate::traits::Repr;

/// check whether the given term is boolean
pub(crate) fn is_term_bool_alt<E: HasArenaAlt>(ctx: &mut E, t: &Term, meta: &str) -> TC<()> {
    let s = t.get_sort(ctx);
    if s.is_bool() {
        Ok(())
    } else {
        let bool = ctx.arena_alt().bool_sort();
        sort_mismatch(&bool, &s, t, meta)
    }
}

/// check whether the given term is boolean
pub fn is_term_bool<E: HasArena>(ctx: &mut E, t: &Term) -> TC<()> {
    is_term_bool_alt(ctx, t, "")
}

/// Check whether the current term is quantifier-free
pub fn is_quantifier_free(term: &Term) -> TC<()> {
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if matches!(t.repr(), ATerm::Forall(..) | ATerm::Exists(..)) {
            return Err(format!("{} includes a quantifier", t));
        }
        stack.extend(t.sub_terms());
    }
    Ok(())
}
