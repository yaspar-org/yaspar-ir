// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::ast::SymbolQuote;
use crate::raw::alg::VarBinding;
use crate::traits::Contains;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// A read-only key-value mapping that supports lookup by key.
///
/// This trait abstracts over different mapping backends ([`HashMap`], [`Vec`], linked lists,
/// etc.) so that algorithms can be written generically over the storage strategy.
/// Values must be [`Clone`] because lookups return owned copies.
pub trait Mapping {
    type Key;
    type Value: Clone;

    /// Look up a key in the mapping, returning a clone of the associated value if present.
    fn lookup(&self, key: &Self::Key) -> Option<Self::Value>;
}

impl<T> Mapping for Vec<T>
where
    [T]: Mapping,
{
    type Key = <[T] as Mapping>::Key;
    type Value = <[T] as Mapping>::Value;

    fn lookup(&self, key: &Self::Key) -> Option<Self::Value> {
        self.as_slice().lookup(key)
    }
}

impl<C> Mapping for [C]
where
    C: Mapping,
{
    type Key = C::Key;
    type Value = C::Value;

    fn lookup(&self, key: &Self::Key) -> Option<Self::Value> {
        self.iter().rev().find_map(|l| l.lookup(key))
    }
}

impl<K, V> Mapping for HashMap<K, V>
where
    K: Eq + Hash,
    V: Clone,
{
    type Key = K;
    type Value = V;

    fn lookup(&self, key: &Self::Key) -> Option<Self::Value> {
        self.get(key).cloned()
    }
}

impl<S, T> Mapping for [VarBinding<S, T>]
where
    S: Eq,
    T: Clone,
{
    type Key = S;
    type Value = (usize, T);

    fn lookup(&self, key: &Self::Key) -> Option<Self::Value> {
        self.iter()
            .find(|v| v.0 == *key)
            .map(|v| (v.1, v.2.clone()))
    }
}

impl<C> Mapping for &C
where
    C: Mapping,
{
    type Key = C::Key;
    type Value = C::Value;

    fn lookup(&self, key: &Self::Key) -> Option<Self::Value> {
        (*self).lookup(key)
    }
}

impl<C> Mapping for &mut C
where
    C: Mapping,
{
    type Key = C::Key;
    type Value = C::Value;

    fn lookup(&self, key: &Self::Key) -> Option<Self::Value> {
        <C>::lookup(self, key)
    }
}

/// A [`Mapping`] that additionally supports inserting new key-value pairs.
pub trait InsertableMapping: Mapping {
    /// Insert a key-value pair into the mapping, overwriting any existing entry for the key.
    fn insert(&mut self, key: Self::Key, value: Self::Value);
}

impl<C> InsertableMapping for &mut C
where
    C: InsertableMapping,
{
    fn insert(&mut self, key: Self::Key, value: Self::Value) {
        <C>::insert(self, key, value);
    }
}

impl<K, V> InsertableMapping for HashMap<K, V>
where
    K: Eq + Hash,
    V: Clone,
{
    fn insert(&mut self, key: Self::Key, value: Self::Value) {
        self.insert(key, value);
    }
}

/// An in-memory linked list
#[derive(Default)]
pub(crate) enum MemLinkedList<'a, T: ?Sized> {
    #[default]
    Nil,
    Cons {
        car: &'a T,
        cdr: &'a MemLinkedList<'a, T>,
    },
}

impl<C: ?Sized> Mapping for MemLinkedList<'_, C>
where
    C: Mapping,
{
    type Key = C::Key;
    type Value = C::Value;

    fn lookup(&self, key: &Self::Key) -> Option<Self::Value> {
        match self {
            MemLinkedList::Nil => None,
            MemLinkedList::Cons { car, cdr: next } => car.lookup(key).or_else(|| next.lookup(key)),
        }
    }
}

/// A cheap representation for a local environment of some sort as a stack-based linked list
///
/// This representation is very efficient as it entirely lives in stack. Each recursion builds
/// a bounded number of [LocEnv::Cons]s as local variables, which only stores references. As a
/// result, it forms a linked list in stack and automatically goes away as recursion finishes.
/// The tricky part is lifetime, which luckily Rust is very good at sanitizing.
pub(crate) type LocEnv<'b, S, T> = MemLinkedList<'b, [VarBinding<S, T>]>;

/// Valid character in a symbol.
pub(crate) fn valid_symbol_char(c: char) -> bool {
    let code = c as u32;
    ((32..=126).contains(&code) || 128 <= code || c.is_ascii_whitespace()) && c != '\\' && c != '|'
}

pub(crate) fn sanitize_bindings<Str: Contains<T = String> + Hash + Eq, T>(
    vars: &[T],
    f: impl Fn(&T) -> Str,
) -> Result<(), String> {
    let mut inserted = HashSet::new();
    for v in vars.iter() {
        let s = f(v);
        if s.inner().contains(|c| !valid_symbol_char(c)) {
            return Err(format!(
                "a symbol can only contain printable chars and white spaces, but not `\\` or `|`: {}",
                s.inner()
            ));
        }
        if inserted.contains(&s) {
            return Err(format!(
                "duplicated local identifier '{}'!",
                s.inner().sym_quote()
            ));
        } else {
            inserted.insert(s);
        }
    }
    Ok(())
}
