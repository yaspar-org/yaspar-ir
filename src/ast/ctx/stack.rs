// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! The stack of assertion levels holding the declared sorts and symbols.
//!
//! Following SMT-LIB, every `push` opens a new assertion level and every `pop` discards the
//! most recent levels together with all sorts and symbols declared in them. Each
//! [`ContextFrame`] only holds the declarations made at its own level, so popping simply drops
//! frames; lookups walk the stack from the top down.

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

/// The stack of assertion levels; never empty.
///
/// The bottom frame is the first assertion level; it additionally holds the builtin sorts and
/// symbols of the current logic.
///
/// Invariant: the topmost frame containing a symbol holds *all* of its visible overloads, so a
/// lookup can stop at the first hit. Overloading a symbol from a lower level therefore copies its
/// overloads to the top frame first (see [`Self::push_symbol`]).
pub(crate) struct ContextStack {
    frames: Vec<ContextFrame>,
}

impl ContextStack {
    pub(crate) fn new(base: ContextFrame) -> Self {
        Self { frames: vec![base] }
    }

    /// The number of assertion levels pushed on top of the first one
    pub(crate) fn level(&self) -> usize {
        self.frames.len() - 1
    }

    /// Open `n` new assertion levels
    pub(crate) fn push(&mut self, n: usize) {
        self.frames
            .extend(std::iter::repeat_with(ContextFrame::default).take(n));
    }

    /// Drop the top `n` assertion levels and return them; `n` must not exceed [`Self::level`].
    pub(crate) fn pop(&mut self, n: usize) -> std::vec::Drain<'_, ContextFrame> {
        let keep = self.frames.len() - n;
        self.frames.drain(keep..)
    }

    fn top_mut(&mut self) -> &mut ContextFrame {
        self.frames.last_mut().unwrap()
    }

    /// The first assertion level, where theories place their builtins
    pub(crate) fn base_mut(&mut self) -> &mut ContextFrame {
        &mut self.frames[0]
    }

    pub(crate) fn get_sort(&self, name: &Str) -> Option<&SortDef> {
        self.frames.iter().rev().find_map(|f| f.sorts.get(name))
    }

    pub(crate) fn contains_sort(&self, name: &Str) -> bool {
        self.get_sort(name).is_some()
    }

    /// Declare a sort in the current assertion level
    pub(crate) fn insert_sort(&mut self, name: Str, def: SortDef) {
        self.top_mut().sorts.insert(name, def);
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

    /// Bind a symbol in the current assertion level, replacing its overloads there
    pub(crate) fn insert_symbol(&mut self, name: Str, sigs: Vec<(Sig, FunctionMeta)>) {
        self.top_mut().symbol_table.insert(name, sigs);
    }

    /// Add an overload of a symbol in the current assertion level
    pub(crate) fn push_symbol(&mut self, name: Str, sig: (Sig, FunctionMeta)) {
        let (top, lower) = self.frames.split_last_mut().unwrap();
        top.symbol_table
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
