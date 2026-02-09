// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! This module instantiates typed AST
//!
//! A typed AST is hashconsed AST. It is managed by a memory Arena. There are a number of advantages
//! to use hashconsing:
//! * An object of a fixed set of fields is globally uniquely allocated in the one arena at most once.
//! * A hashconsed object is cheap to represent (as an [Arc]).
//! * A hashconsed object is cheap to compare, hash, and clone.
//!
//! Therefore, typed ASTs have optimized memory representation, and are time-efficient to use.

use super::alg;
pub use crate::allocator::{
    CommandAllocator, LocalVarAllocator, ObjectAllocatorExt, SortAllocator, StrAllocator,
    TermAllocator,
};
use crate::ast::{ACommand, ATerm, Context};
use crate::instantiate_ast;
use crate::locenv::valid_char;
use crate::traits::{Allocatable, Contains, MetaData, Repr};
use hashconsing::{HConsed, HConsign, HashConsign};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fmt::Display;

type P<T> = HConsed<T>;

impl<T> Contains for P<T> {
    type T = T;

    #[inline]
    fn inner(&self) -> &Self::T {
        self.get()
    }
}

// an allocated string has no meaningful meta data
impl<T> MetaData for P<T> {
    type T = &'static str;

    #[inline]
    fn meta_data(&self) -> &Self::T {
        &""
    }

    fn display_meta_data(&self) -> String {
        "".into()
    }
}

impl<Env, T> Allocatable<Env> for P<T> {
    type Out = P<T>;

    #[inline]
    fn allocate(&self, _env: &mut Env) -> Self::Out {
        self.clone()
    }
}

instantiate_ast!(P);

/// A list of different theories supported by the crate
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Theory {
    Quantifiers,
    Ints,
    Reals,
    RealInts,
    Strings,
    ArrayEx,
    /// Floating point support is only partial
    FloatingPoints,
    Bitvectors,
    Datatypes,
}

impl Theory {
    pub fn has_int(&self) -> bool {
        matches!(self, Theory::Ints | Theory::RealInts | Theory::Strings)
    }
}

impl Display for Theory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Theory::Quantifiers => "quantifiers".fmt(f),
            Theory::Ints => "ints".fmt(f),
            Theory::Reals => "reals".fmt(f),
            Theory::RealInts => "reals and ints".fmt(f),
            Theory::Strings => "strings".fmt(f),
            Theory::ArrayEx => "arrays".fmt(f),
            Theory::FloatingPoints => "floating points".fmt(f),
            Theory::Bitvectors => "bit vectors".fmt(f),
            Theory::Datatypes => "datatypes".fmt(f),
        }
    }
}

/// The arena for allocating different instances of ASTs
pub struct Arena {
    string: HConsign<String>,
    sort: HConsign<RSort>,
    term: HConsign<RTerm>,
    command: HConsign<RCommand>,
    symbols: HashSet<Str>,
    var_counter: u128,
    lvar_id: usize,
}

impl Arena {
    pub fn new() -> Self {
        Self {
            string: HConsign::empty(),
            sort: HConsign::empty(),
            term: HConsign::empty(),
            command: HConsign::empty(),
            symbols: Default::default(),
            var_counter: 0,
            lvar_id: 0,
        }
    }
}

impl Default for Arena {
    fn default() -> Self {
        Self::new()
    }
}

fn strip_symbol_quote(s: &str) -> &str {
    if s.starts_with("|") {
        &s[1..s.len() - 1]
    } else {
        s
    }
}

impl StrAllocator for Arena {
    type Str = Str;

    fn allocate_str(&mut self, s: &str) -> Self::Str {
        self.string.mk(s.into())
    }

    fn allocate_string(&mut self, s: String) -> Self::Str {
        self.string.mk(s)
    }

    fn allocate_symbol(&mut self, s: &str) -> Self::Str {
        let sym = self.allocate_str(strip_symbol_quote(s));
        self.symbols.insert(sym.clone());
        sym
    }
}

impl SortAllocator<Str, Sort> for Arena {
    fn allocate_sort(&mut self, s: crate::raw::alg::Sort<Str, Sort>) -> Sort {
        self.sort.mk(s.into())
    }
}

impl TermAllocator<Str, Sort, Term> for Arena {
    fn allocate_term(&mut self, t: crate::raw::alg::Term<Str, Sort, Term>) -> Term {
        self.term.mk(t.into())
    }
}

impl CommandAllocator<Str, Sort, Term, Command> for Arena {
    fn allocate_command(&mut self, c: crate::raw::alg::Command<Str, Sort, Term>) -> Command {
        self.command.mk(c.into())
    }
}

impl LocalVarAllocator for Arena {
    fn new_local(&mut self) -> usize {
        let id = self.lvar_id;
        if id == usize::MAX {
            panic!("Maximum number of local variables reached!");
        }
        self.lvar_id += 1;
        id
    }
}

/// A helper trait that flattens connectives by one layer; it is useful to build a flatter AST.
pub trait FlatConnectivesExt: TermAllocator<Str, Sort, Term> {
    /// Create an AST for `and` and flattens one layer of nested `and`'s if necessary
    ///
    /// If an AST is built by always calling `flat_*` then it is guaranteed to have a flat boolean structure.
    fn flat_and(&mut self, ts: Vec<Term>) -> Term {
        let mut acc = vec![];
        for t in ts {
            if let alg::Term::And(ts) = t.repr() {
                acc.extend(ts.clone());
            } else {
                acc.push(t);
            }
        }
        self.and(acc)
    }

    /// Create an AST for `or` and flattens one layer of nested `or`'s if necessary
    ///
    /// If an AST is built by always calling `flat_*` then it is guaranteed to have a flat boolean structure.
    fn flat_or(&mut self, ts: Vec<Term>) -> Term {
        let mut acc = vec![];
        for t in ts {
            if let alg::Term::Or(ts) = t.repr() {
                acc.extend(ts.clone());
            } else {
                acc.push(t);
            }
        }
        self.or(acc)
    }
}

impl<X> FlatConnectivesExt for X where X: TermAllocator<Str, Sort, Term> {}

/// A trait for fresh variable generator
pub trait FreshVar {
    type Str;

    /// Generate a fresh variable, with the given prefix
    fn fresh_var(&mut self, prefix: &str) -> Self::Str;

    /// Generate a fresh variable with "x" as the prefix
    fn fresh_x(&mut self) -> Self::Str {
        self.fresh_var("x")
    }
}

impl FreshVar for Arena {
    type Str = Str;

    fn fresh_var(&mut self, prefix: &str) -> Self::Str {
        // avoid special char
        let prefix = prefix.replace(|c| !valid_char(c), "");
        // we make sure the prefix is not empty
        let prefix = if prefix.is_empty() { "x" } else { &prefix };
        // it is ok for prefix to be weird; when it is printed, pipes will be added if it contains
        // strange chars. we just need to avoid invalid chars.
        loop {
            // use `-` to avoid `bvX`, which is a bit vector literal.
            let candidate = format!("{}-{}", prefix, self.var_counter);
            let sym = self.allocate_string(candidate);
            if self.symbols.insert(sym.clone()) {
                return sym;
            }
            // here we know sym is already seen
            if let Some(v) = self.var_counter.checked_add(1) {
                self.var_counter = v;
            } else {
                // very unlikely!
                panic!("Maximum number of variables reached!");
            }
        }
    }
}

/// This trait is internal; it captures a structure that contains an [Arena].
///
/// The more convenient exposed trait is [HasArena], which can be implemented by users.
pub(crate) trait HasArenaAlt {
    fn arena_alt(&mut self) -> &mut Arena;
}

/// This trait returns a mutable reference to the underlying [Arena], but it avoids [Arena] itself
/// being an instance.
pub trait HasArena {
    fn arena(&mut self) -> &mut Arena;
}

impl<T> StrAllocator for T
where
    T: HasArena,
{
    type Str = Str;

    fn allocate_str(&mut self, s: &str) -> Self::Str {
        self.arena().allocate_str(s)
    }

    fn allocate_string(&mut self, s: String) -> Self::Str {
        self.arena().allocate_string(s)
    }

    fn allocate_symbol(&mut self, s: &str) -> Self::Str {
        self.arena().allocate_symbol(s)
    }
}

impl<T> SortAllocator<Str, Sort> for T
where
    T: HasArena,
{
    fn allocate_sort(&mut self, s: crate::raw::alg::Sort<Str, Sort>) -> Sort {
        self.arena().allocate_sort(s)
    }
}

impl<T> TermAllocator<Str, Sort, Term> for T
where
    T: HasArena,
{
    fn allocate_term(&mut self, t: ATerm<Str, Sort, Term>) -> Term {
        self.arena().allocate_term(t)
    }
}

impl CommandAllocator<Str, Sort, Term, Command> for Context {
    fn allocate_command(&mut self, c: ACommand<Str, Sort, Term>) -> Command {
        self.arena().allocate_command(c)
    }
}

impl<T> LocalVarAllocator for T
where
    T: HasArena,
{
    fn new_local(&mut self) -> usize {
        self.arena().new_local()
    }
}

impl<T> FreshVar for T
where
    T: HasArena,
{
    type Str = Str;

    fn fresh_var(&mut self, prefix: &str) -> Self::Str {
        self.arena().fresh_var(prefix)
    }
}

impl<T> HasArenaAlt for T
where
    T: HasArena,
{
    #[inline]
    fn arena_alt(&mut self) -> &mut Arena {
        self.arena()
    }
}

/// The trait to obtain a sort from an object
///
/// Invariant: typed AST must return a sort, i.e. [FetchSort::get_sort] must succeed.
pub trait FetchSort<T> {
    /// Retrieve the sort
    fn maybe_sort(&self, arena: &mut T) -> Option<Sort>;

    /// Get the sort if we know sort must be there. This is usually the case after type-checking
    fn get_sort(&self, arena: &mut T) -> Sort {
        self.maybe_sort(arena).expect("This is a fatal violation of sort invariance; a well-sorted term must be aware of its own sort!")
    }
}

impl HasArenaAlt for Arena {
    #[inline]
    fn arena_alt(&mut self) -> &mut Arena {
        self
    }
}

impl<T: HasArenaAlt> FetchSort<T> for Term {
    fn maybe_sort(&self, arena: &mut T) -> Option<Sort> {
        match self.repr() {
            alg::Term::Constant(_, s) => s.clone(),
            alg::Term::Global(_, so) => so.clone(),
            alg::Term::Local(id) => id.sort.clone(),
            alg::Term::App(_, _, s) => s.clone(),
            alg::Term::Let(_, t) => t.maybe_sort(arena),
            alg::Term::Exists(_, _) => Some(arena.arena_alt().bool_sort()),
            alg::Term::Forall(_, _) => Some(arena.arena_alt().bool_sort()),
            alg::Term::Annotated(t, _) => t.maybe_sort(arena),
            alg::Term::Ite(_, t, _) => t.maybe_sort(arena),
            alg::Term::Matching(_, arms) => arms[0].body.maybe_sort(arena), // there must be at least one branch
            _ => Some(arena.arena_alt().bool_sort()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::SymbolQuote;
    #[test]
    fn symbol_quote1() {
        let mut arena = Arena::new();
        let sym = arena.allocate_symbol("test");
        assert_eq!(sym.sym_quote(), "test");
    }

    #[test]
    fn symbol_quote2() {
        let mut arena = Arena::new();
        let s = r"|foo
        bar|";
        let sym = arena.allocate_symbol(s);
        assert_eq!(sym.inner().sym_quote(), s);
    }
}
