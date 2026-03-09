// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Low-level, parametric AST definitions and core algorithms.
//!
//! This module contains the foundational building blocks of the crate:
//!
//! - [`alg`] — the parametric algebraic AST types ([`Term`](alg::Term), [`Sort`](alg::Sort),
//!   [`Command`](alg::Command), etc.) that are instantiated into both untyped and typed
//!   representations.
//! - `instance` — the typed (hashconsed) instantiation of the algebraic ASTs, managed by an
//!   [`Arena`](instance::Arena).
//! - `tc` — the type-checking algorithm, organized as constraint programming over the algebraic
//!   ASTs.
//! - `letelim` — let-elimination (inlining let-bound variables).
//! - `template` — the [`instantiate_ast!`](crate::instantiate_ast) macro for creating new AST
//!   instantiations.

pub mod alg;
pub(crate) mod instance;
pub(crate) mod letelim;
pub(crate) mod tc;
mod template;
