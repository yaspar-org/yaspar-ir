// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Dialects: variants of the input language that a [`Context`](super::Context) accepts.
//!
//! A dialect is a type, used as a type parameter of [`Context`](super::Context) and of every API
//! that works in one (the type checker, the builder contexts, global substitution and the cvc5
//! conversions). So a dialect's rules are fixed when the context is created, and resolved at compile
//! time. Every such parameter defaults to [`DefaultDialect`], so code that never names a dialect
//! works in the default dialect: [`SmtLib`], or [`AtsLib`] with the `atslib` feature.
//!
//! Create a context of a given dialect with
//! [`Context::new_dialect`](super::Context::new_dialect), e.g. `Context::<AtsLib>::new_dialect()`;
//! [`Context::new`](super::Context::new) creates one in the default dialect.
//!
//! The dialects are uninhabited types: they are only ever named, never built. What tells them apart
//! is how they implement [`Dialect`], whose sealed supertrait keeps the dialects a closed set: only
//! this crate can add one.

use crate::raw::instance::Term;
use crate::raw::tc::matching::MatchChecker;
use crate::raw::tc::{TC, TCEnvGen};

/// A dialect of SMT-LIB, implemented by [`SmtLib`] and [`AtsLib`].
///
/// Its items are the rules that tell the dialects apart, for code generic over the dialect to call.
/// The supertrait `Sealed` is private, so this trait cannot be implemented outside this crate.
///
/// `Sized`, because every type parameter is `Sized` unless it says otherwise: so a rule that names
/// e.g. `TCEnvGen<'_, L, Self>` needs `Self: Sized`. Saying it here, once, spares each rule a
/// `where Self: Sized`; and the dialects, as empty enums, are `Sized` anyway.
pub trait Dialect: sealed::Sealed + Sized + 'static {
    /// The length in bytes that a declared or bound symbol must stay below, if any.
    const SYMBOL_LIMIT: Option<usize>;

    /// Start checking a `match` on `scrutinee`, which `meta` locates, or reject it if the dialect
    /// has no `match` terms.
    #[doc(hidden)]
    fn start_match<L>(
        env: &mut TCEnvGen<'_, L, Self>,
        scrutinee: &Term,
        meta: &str,
    ) -> TC<MatchChecker>;
}

/// Standard SMT-LIB.
pub enum SmtLib {}

/// The ATSLIB dialect.
pub enum AtsLib {}

impl Dialect for SmtLib {
    const SYMBOL_LIMIT: Option<usize> = None;

    fn start_match<L>(
        env: &mut TCEnvGen<'_, L, Self>,
        scrutinee: &Term,
        meta: &str,
    ) -> TC<MatchChecker> {
        MatchChecker::new(env, scrutinee, meta)
    }
}

impl Dialect for AtsLib {
    const SYMBOL_LIMIT: Option<usize> = Some(ATSLIB_SYMBOL_LIMIT);

    fn start_match<L>(
        _env: &mut TCEnvGen<'_, L, Self>,
        _scrutinee: &Term,
        meta: &str,
    ) -> TC<MatchChecker> {
        Err(format!(
            "TC: match expression{meta} is not supported in ATSLIB!"
        ))
    }
}

/// The dialects that are SMT-LIB itself: an API that only SMT-LIB has requires this, e.g. checking
/// a `match`.
pub trait IsSmtLib: Dialect {}

impl IsSmtLib for SmtLib {}

/// The dialects that are ATSLIB: an API that only ATSLIB has requires this.
pub trait IsAtsLib: Dialect {}

impl IsAtsLib for AtsLib {}

/// The dialect of a context that does not name one.
#[cfg(not(feature = "atslib"))]
pub type DefaultDialect = SmtLib;

/// The dialect of a context that does not name one.
#[cfg(feature = "atslib")]
pub type DefaultDialect = AtsLib;

/// In [`AtsLib`], a declared or bound symbol must be shorter than this many bytes.
pub const ATSLIB_SYMBOL_LIMIT: usize = 512;

mod sealed {
    /// Public in a private module: [`Dialect`](super::Dialect) can name it as a supertrait, while
    /// nothing outside this crate can implement it.
    pub trait Sealed {}

    impl Sealed for super::SmtLib {}

    impl Sealed for super::AtsLib {}
}
