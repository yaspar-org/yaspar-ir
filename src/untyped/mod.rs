// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Untyped ASTs with source location information, and the parser entry point.
//!
//! This module provides the untyped representation of SMTLib scripts. Untyped ASTs are the
//! direct result of parsing and preserve source location information ([`Range`](yaspar::position::Range))
//! for error reporting. They may be semantically malformed (e.g. referencing undeclared symbols).
//!
//! The main entry point is [`UntypedAst`], which provides parsing methods:
//!
//! - [`parse_script_str`](UntypedAst::parse_script_str) — parse a full SMTLib script.
//! - [`parse_command_str`](UntypedAst::parse_command_str) — parse a single command.
//! - [`parse_term_str`](UntypedAst::parse_term_str) — parse a single term.
//! - [`parse_sort_str`](UntypedAst::parse_sort_str) — parse a single sort.
//!
//! After parsing, call [`.type_check(&mut context)`](crate::ast::Typecheck::type_check) to
//! convert untyped ASTs into typed, hashconsed representations.
//!
//! See [crate::ast] for typed ASTs.

mod instance;

pub use instance::*;
