// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Dialects: variants of the input language that a [`Context`](super::Context) accepts.
//!
//! The dialect is a const parameter of [`Context`](super::Context), and of every API that works in
//! one (the type checker, the builder contexts, global substitution and the cvc5 conversions). So a
//! dialect's rules are fixed when the context is created, and checked without any cost at run time.
//! Every such parameter defaults to [`DEFAULT_DIALECT`], so code that never names a dialect works in
//! SMT-LIB.
//!
//! Create a context of another dialect with
//! [`Context::new_dialect`](super::Context::new_dialect), e.g.
//! `Context::<DIALECT_ATSLIB>::new_dialect()`.

/// A dialect, used as a const parameter.
///
/// It is a number rather than an enum because a const parameter of an enum type is not supported
/// on stable Rust.
pub type Dialect = u8;

/// Standard SMT-LIB.
pub const DIALECT_SMTLIB: Dialect = 0;

/// The ATSLIB dialect: SMT-LIB, with symbols limited to fewer than 512 bytes
/// (`ATSLIB_SYMBOL_LIMIT`).
pub const DIALECT_ATSLIB: Dialect = 1;

/// The dialect of a context that does not name one.
#[cfg(not(feature = "atslib"))]
pub const DEFAULT_DIALECT: Dialect = DIALECT_SMTLIB;
#[cfg(feature = "atslib")]
pub const DEFAULT_DIALECT: Dialect = DIALECT_ATSLIB;

/// In [`DIALECT_ATSLIB`], a declared or bound symbol must be shorter than this many bytes.
pub const ATSLIB_SYMBOL_LIMIT: usize = 512;
