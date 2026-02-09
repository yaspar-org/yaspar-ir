// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::ast::SymbolQuote;
use crate::raw::alg::VarBinding;
use crate::traits::Contains;
use std::collections::HashSet;
use std::hash::Hash;

/// An in-memory linked list
pub(crate) enum MemLinkedList<'a, T: ?Sized> {
    Nil,
    Cons {
        car: &'a T,
        cdr: &'a MemLinkedList<'a, T>,
    },
}

/// A cheap representation for a local environment of some sort as a stack-based linked list
///
/// This representation is very efficient as it entirely lives in stack. Each recursion builds
/// a bounded number of [LocEnv::Cons]s as local variables, which only stores references. As a
/// result, it forms a linked list in stack and automatically goes away as recursion finishes.
/// The tricky part is lifetime, which luckily Rust is very good at sanitizing.
pub(crate) type LocEnv<'b, S, T> = MemLinkedList<'b, [VarBinding<S, T>]>;

pub(crate) fn valid_char(c: char) -> bool {
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
        if s.inner().contains(|c| !valid_char(c)) {
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

impl<'b, Str, T> LocEnv<'b, Str, T>
where
    Str: Contains<T = String> + Hash + Eq + Clone,
    T: Clone,
{
    pub(crate) fn insert<'c>(
        &'c self,
        vars: &'b [VarBinding<Str, T>],
    ) -> Result<LocEnv<'b, Str, T>, String>
    where
        'c: 'b,
    {
        sanitize_bindings(vars, |v| v.0.clone())?;
        Ok(LocEnv::Cons {
            car: vars,
            cdr: self,
        })
    }

    pub(crate) fn lookup(&self, n: &Str) -> Option<(usize, T)> {
        match self {
            LocEnv::Nil => None,
            LocEnv::Cons {
                car: bindings,
                cdr: next,
            } => {
                for vb in bindings.iter() {
                    if vb.0 == *n {
                        return Some((vb.1, vb.2.clone()));
                    }
                }
                next.lookup(n)
            }
        }
    }
}
