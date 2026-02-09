// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::allocator::ObjectAllocatorExt;
use crate::ast::{FetchSort, HasArena, HasArenaAlt, TC, Term};
use crate::raw::tc::sort_mismatch;

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
