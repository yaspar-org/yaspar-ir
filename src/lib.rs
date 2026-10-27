// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Yaspar-IR: typed representations of SMTLib scripts with checked building APIs.
//!
//! This crate provides parsing, type-checking, and programmatic construction of SMTLib-2.7
//! scripts. It is fully compliant with the SMTLib standard, supporting quantifiers, datatypes
//! (including polymorphic and mutually recursive declarations), and all standard logics.
//!
//! # Architecture
//!
//! The crate is organized around a two-level AST design:
//!
//! - **Untyped ASTs** ([`untyped`]) — faithful parsing results that preserve source location
//!   information for error reporting. These may be semantically malformed.
//! - **Typed ASTs** ([`ast`]) — hashconsed, well-formed representations managed by a memory
//!   [`Arena`](ast::Arena). Hashconsing ensures that structurally identical sub-terms share a
//!   single allocation, making `clone()`, `==`, and `hash()` O(1) operations.
//!
//! # Typical workflow
//!
//! ```rust
//! use yaspar_ir::ast::{Context, Typecheck};
//! use yaspar_ir::untyped::UntypedAst;
//!
//! // 1. Parse
//! let commands = UntypedAst.parse_script_str("(set-logic QF_LIA) (declare-const x Int)").unwrap();
//! // 2. Type-check into a context
//! let mut context = Context::new();
//! let typed_commands = commands.type_check(&mut context).unwrap();
//! // 3. Analyze or transform the typed terms
//! ```
//!
//! # Building terms programmatically
//!
//! Typed ASTs can also be built without parsing, using either:
//!
//! - **Unchecked APIs** — low-level allocator methods on [`Context`](ast::Context) (e.g.
//!   `context.app(...)`, `context.forall(...)`). These are efficient but require the caller to
//!   maintain well-formedness invariants manually.
//! - **Checked APIs** — the [`CheckedApi`](ast::CheckedApi) and
//!   [`ScopedSortApi`](ast::ScopedSortApi) traits, which validate scope, sort compatibility,
//!   and arity automatically via the `TC<T>` monad (`Result<T, String>`).
//!
//! See the [`ast`] module and the README for a comprehensive guide to the checked APIs.
//!
//! # Feature flags
//!
//! - `cnf` — enables NNF/CNF conversion (see `ast::cnf` module).
//! - `implicant-generation` — enables implicant computation (see `ast::implicant` module).
//! - `cache` — enables caching infrastructure for CNF and other algorithms.
//! - `cvc5` — enables translation to cvc5 1.4.x (see `cvc5` module and the `ConvertToCvc5` trait),
//!   linking cvc5 statically.
//! - `cvc5-dynamic` — same as `cvc5`, but links cvc5 dynamically. Use it when linking against a
//!   system-provided cvc5 shared library.
//! - `cvc5-parser` — additionally enables the cvc5 `parser`. Only takes effect alongside `cvc5` or
//!   `cvc5-dynamic`.
//! - `cvc5-1.3.x`, `cvc5-dynamic-1.3.x`, `cvc5-parser-1.3.x` — the same for cvc5 1.3.x, through
//!   cvc5-rs 0.5. The `cvc5` module then has the API it had before cvc5 1.4.x support. The unversioned
//!   features are aliases of `cvc5-1.4.x`, `cvc5-dynamic-1.4.x` and `cvc5-parser-1.4.x`. The 1.3.x
//!   and 1.4.x features are mutually exclusive, and `CVC5_DIR`, if set, must point at a build of the
//!   matching cvc5 release.
//! - `finite-set` — enables the theory of finite sets (`Set` sort and `set.*` operators) and the
//!   logics that include it.
//!
//! # Modules
//!
//! | Module | Description |
//! |---|---|
//! | [`ast`] | Typed AST types, the [`Context`](ast::Context), checked/unchecked building APIs, and term transformations |
//! | [`untyped`] | Untyped ASTs with location information, and the parser entry point [`UntypedAst`](untyped::UntypedAst) |
//! | [`traits`] | Core abstraction traits ([`Contains`](traits::Contains), [`Repr`](traits::Repr), [`AllocatableString`](traits::AllocatableString)) |
//! | [`statics`] | Static constants (sort name strings, regex patterns) |
//! | [`cvc5`] | Translation to cvc5 objects (`Sort`, `Term`, `Command`). Requires a `cvc5` or `cvc5-dynamic` feature, of either cvc5 version. |

mod allocator;
pub mod ast;
mod containers;
mod deep_drop;
#[cfg(all(feature = "cvc5-dep-1.3.x", feature = "cvc5-dep-1.4.x"))]
compile_error!(
    "the cvc5 1.3.x and 1.4.x features are mutually exclusive: both link a cvc5 library, \
     whose symbols clash. Enable either the `-1.3.x` features or the others."
);
#[cfg(all(feature = "cvc5-dep-1.3.x", not(feature = "cvc5-dep-1.4.x")))]
#[path = "cvc5_1_3/mod.rs"]
pub mod cvc5;
#[cfg(feature = "cvc5-dep-1.4.x")]
#[path = "cvc5_1_4/mod.rs"]
pub mod cvc5;
mod macros;
mod meta;
mod raw;
pub mod statics;
pub mod traits;
pub mod untyped;
