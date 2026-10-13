// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Containers of [`Cvc5Env`](super::Cvc5Env) that follow the SMT-LIB assertion levels.
//!
//! Like the declarations of a [`Context`](crate::ast::Context), every `push` opens a new level
//! and every `pop` discards whatever was added in the popped levels.

use crate::containers::{InsertableMapping, Mapping};
use bimap::BiHashMap;
use std::collections::HashMap;
use std::hash::Hash;

/// A map with one frame per assertion level; each frame only holds the entries added at its
/// own level, so popping drops frames and lookups walk the stack from the top down.
pub(super) struct ScopedMap<K, V> {
    /// Never empty; the bottom frame is the first assertion level.
    frames: Vec<HashMap<K, V>>,
}

impl<K: Eq + Hash, V> ScopedMap<K, V> {
    pub(super) fn new() -> Self {
        Self {
            frames: vec![HashMap::new()],
        }
    }

    /// The number of levels pushed on top of the first one
    pub(super) fn level(&self) -> usize {
        self.frames.len() - 1
    }

    pub(super) fn get(&self, key: &K) -> Option<&V> {
        self.frames.iter().rev().find_map(|f| f.get(key))
    }

    /// Add an entry to the current assertion level
    pub(super) fn insert(&mut self, key: K, value: V) {
        self.frames.last_mut().unwrap().insert(key, value);
    }

    /// Iterate the visible values, i.e. those not shadowed by a higher level
    pub(super) fn values(&self) -> impl Iterator<Item = &V> {
        self.frames.iter().enumerate().flat_map(move |(i, f)| {
            f.iter()
                .filter(move |(k, _)| !self.frames[i + 1..].iter().any(|g| g.contains_key(*k)))
                .map(|(_, v)| v)
        })
    }

    pub(super) fn push(&mut self, n: usize) {
        self.frames
            .extend(std::iter::repeat_with(HashMap::new).take(n));
    }

    /// Drop the top `n` levels; `n` must not exceed the number of pushed levels.
    pub(super) fn pop(&mut self, n: usize) {
        self.frames.truncate(self.frames.len() - n);
    }
}

/// A bidirectional translation cache whose entries added within a pushed assertion level are
/// evicted when that level is popped, since they may refer to objects declared in it.
///
/// Entries added below a level cannot refer to anything declared in it, so they survive.
///
/// `pub` only because it appears as the `Cache` of [`Memoizing`](crate::raw::alg::rec_memo::Memoizing);
/// the module is private, so it cannot be named outside [`crate::cvc5`].
pub struct ScopedBiCache<L, R> {
    map: BiHashMap<L, R>,
    /// The left keys added at each pushed level; one entry per level above the first.
    added: Vec<Vec<L>>,
}

impl<L, R> ScopedBiCache<L, R>
where
    L: Eq + Hash + Clone,
    R: Eq + Hash,
{
    pub(super) fn new() -> Self {
        Self {
            map: BiHashMap::new(),
            added: vec![],
        }
    }

    pub(super) fn get_by_left(&self, left: &L) -> Option<&R> {
        self.map.get_by_left(left)
    }

    pub(super) fn get_by_right(&self, right: &R) -> Option<&L> {
        self.map.get_by_right(right)
    }

    pub(super) fn insert(&mut self, left: L, right: R) {
        if let Some(added) = self.added.last_mut() {
            added.push(left.clone());
        }
        self.map.insert(left, right);
    }

    pub(super) fn remove_by_right(&mut self, right: &R) {
        // a stale key in `added` is harmless: evicting it later finds nothing
        self.map.remove_by_right(right);
    }

    pub(super) fn right_values(&self) -> impl Iterator<Item = &R> {
        self.map.right_values()
    }

    pub(super) fn push(&mut self, n: usize) {
        self.added.extend(std::iter::repeat_with(Vec::new).take(n));
    }

    /// Evict the entries added in the top `n` levels; `n` must not exceed the number of pushed
    /// levels.
    pub(super) fn pop(&mut self, n: usize) {
        let keep = self.added.len() - n;
        for left in self.added.drain(keep..).flatten() {
            self.map.remove_by_left(&left);
        }
    }
}

// The cache is treated as a left-keyed mapping for memoization purposes: `lookup` finds the
// right value by left key, and `insert` populates the bijection in both directions.
impl<L, R> Mapping for ScopedBiCache<L, R>
where
    L: Eq + Hash + Clone,
    R: Eq + Hash + Clone,
{
    type Key = L;
    type Value = R;

    fn lookup(&self, key: &Self::Key) -> Option<Self::Value> {
        self.get_by_left(key).cloned()
    }
}

impl<L, R> InsertableMapping for ScopedBiCache<L, R>
where
    L: Eq + Hash + Clone,
    R: Eq + Hash + Clone,
{
    fn insert(&mut self, key: Self::Key, value: Self::Value) {
        ScopedBiCache::insert(self, key, value);
    }
}
