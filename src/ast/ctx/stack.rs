// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! The stack of assertion levels holding the declared sorts and symbols.
//!
//! Following SMT-LIB, every `push` opens a new assertion level and every `pop` discards the
//! most recent levels together with all sorts and symbols declared in them. Each
//! [`ContextFrame`] only holds the declarations made at its own level, so popping simply drops
//! frames; lookups walk the stack from the top down. `reset-assertions` pops all levels and
//! empties the first one. Under `:global-declarations`, declarations go into the frame below the
//! assertion levels instead, which neither removes (§4.1.5).

use crate::ast::ctx::FunctionMeta;
use crate::raw::instance::{Sig, SortDef, Str};
use std::collections::HashMap;

/// The declarations made at one assertion level: sorts and symbols.
#[derive(Default)]
pub(crate) struct ContextFrame {
    /// Custom sorts; mapping sort names to arities or definitions.
    pub(crate) sorts: HashMap<Str, SortDef>,
    /// Mapping custom functions to their signatures and potentially their definitions.
    pub(crate) symbol_table: HashMap<Str, Vec<(Sig, FunctionMeta)>>,
}

/// The stack of assertion levels.
///
/// The bottom frame holds the builtin sorts and symbols of the current logic, and the global
/// declarations; it is not an assertion level, so neither `pop` nor `reset-assertions` can remove
/// it. The frame above it is the first assertion level, so there are always at least two frames.
///
/// Invariant: the topmost frame containing a symbol holds *all* of its visible overloads, so a
/// lookup can stop at the first hit. Overloading a symbol from a lower level therefore copies its
/// overloads to the top frame first (see [`Self::push_symbol`]).
pub(crate) struct ContextStack {
    frames: Vec<ContextFrame>,
    /// Whether declarations go into the bottom frame (`:global-declarations`)
    global: bool,
}

impl ContextStack {
    pub(crate) fn new(builtins: ContextFrame, global: bool) -> Self {
        Self {
            frames: vec![builtins, ContextFrame::default()],
            global,
        }
    }

    /// Set `:global-declarations`
    pub(crate) fn set_global(&mut self, global: bool) {
        self.global = global;
    }

    /// The number of assertion levels pushed on top of the first one
    pub(crate) fn level(&self) -> usize {
        self.frames.len() - 2
    }

    /// Open `n` new assertion levels
    pub(crate) fn push(&mut self, n: usize) {
        self.frames
            .extend(std::iter::repeat_with(ContextFrame::default).take(n));
    }

    /// Drop the top `n` assertion levels and return them; `n` must not exceed [`Self::level`].
    pub(crate) fn pop(&mut self, n: usize) -> Vec<ContextFrame> {
        let keep = self.frames.len() - n;
        self.frames.split_off(keep)
    }

    /// Drop all assertion levels, including the first one, and return them; the first level is
    /// replaced by an empty one.
    pub(crate) fn reset_assertions(&mut self) -> Vec<ContextFrame> {
        let levels = self.frames.split_off(1);
        self.frames.push(ContextFrame::default());
        levels
    }

    /// The index of the frame declarations go into
    fn decl_index(&self) -> usize {
        if self.global {
            0
        } else {
            self.frames.len() - 1
        }
    }

    fn decl_frame_mut(&mut self) -> &mut ContextFrame {
        let i = self.decl_index();
        &mut self.frames[i]
    }

    /// The frame below the assertion levels, where theories place their builtins
    pub(crate) fn builtins_mut(&mut self) -> &mut ContextFrame {
        &mut self.frames[0]
    }

    pub(crate) fn get_sort(&self, name: &Str) -> Option<&SortDef> {
        self.frames.iter().rev().find_map(|f| f.sorts.get(name))
    }

    pub(crate) fn contains_sort(&self, name: &Str) -> bool {
        self.get_sort(name).is_some()
    }

    /// Declare a sort in the current assertion level, or globally
    pub(crate) fn insert_sort(&mut self, name: Str, def: SortDef) {
        self.decl_frame_mut().sorts.insert(name, def);
    }

    /// Remove a sort from all assertion levels
    pub(crate) fn remove_sort(&mut self, name: &Str) {
        for f in &mut self.frames {
            f.sorts.remove(name);
        }
    }

    pub(crate) fn get_symbol(&self, name: &Str) -> Option<&Vec<(Sig, FunctionMeta)>> {
        self.frames
            .iter()
            .rev()
            .find_map(|f| f.symbol_table.get(name))
    }

    pub(crate) fn contains_symbol(&self, name: &Str) -> bool {
        self.get_symbol(name).is_some()
    }

    /// Bind a symbol in the current assertion level, or globally, replacing its overloads there
    pub(crate) fn insert_symbol(&mut self, name: Str, sigs: Vec<(Sig, FunctionMeta)>) {
        self.decl_frame_mut().symbol_table.insert(name, sigs);
    }

    /// Add an overload of a symbol in the current assertion level, or globally
    pub(crate) fn push_symbol(&mut self, name: Str, sig: (Sig, FunctionMeta)) {
        let i = self.decl_index();
        let (lower, rest) = self.frames.split_at_mut(i);
        rest[0]
            .symbol_table
            .entry(name)
            .or_insert_with_key(|name| {
                // maintain the invariant: bring along the overloads visible from below
                lower
                    .iter()
                    .rev()
                    .find_map(|f| f.symbol_table.get(name))
                    .cloned()
                    .unwrap_or_default()
            })
            .push(sig);
    }

    /// Remove a symbol from all assertion levels
    pub(crate) fn remove_symbol(&mut self, name: &Str) {
        for f in &mut self.frames {
            f.symbol_table.remove(name);
        }
    }

    /// Iterate the visible sorts, i.e. those not shadowed by a higher level
    pub(crate) fn sorts(&self) -> impl Iterator<Item = (&Str, &SortDef)> {
        self.frames.iter().enumerate().flat_map(move |(i, f)| {
            f.sorts.iter().filter(move |(n, _)| {
                !self.frames[i + 1..]
                    .iter()
                    .any(|g| g.sorts.contains_key(*n))
            })
        })
    }

    /// Iterate the visible symbols, i.e. those not shadowed by a higher level
    pub(crate) fn symbols(&self) -> impl Iterator<Item = (&Str, &Vec<(Sig, FunctionMeta)>)> {
        self.frames.iter().enumerate().flat_map(move |(i, f)| {
            f.symbol_table.iter().filter(move |(n, _)| {
                !self.frames[i + 1..]
                    .iter()
                    .any(|g| g.symbol_table.contains_key(*n))
            })
        })
    }
}
