// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Static constants and regex patterns used throughout the crate.
//!
//! This module defines the canonical string names for built-in SMTLib sorts (`Bool`, `Int`,
//! `Real`, `String`, `RegLan`, `Array`, `BitVec`) and regex patterns for validating bitvector
//! literal symbols and SMTLib symbol syntax.

use lazy_static::lazy_static;
use regex::Regex;

lazy_static! {
    pub static ref BV_RE: Regex = Regex::new("^bv(0|[1-9][0-9]*)$").unwrap();
    pub static ref SYMBOL_RE: Regex =
        Regex::new(r"^[A-Za-z~!@$%^&*_\-+=<>.?/]+[0-9A-Za-z~!@$%^&*_\-+=<>.?/]*$").unwrap();
}

pub static BOOL: &str = "Bool";
pub static INT: &str = "Int";
pub static REAL: &str = "Real";
pub static STRING: &str = "String";
pub static REGLAN: &str = "Reglan";
pub static ARRAY: &str = "Array";
pub static BITVEC: &str = "BitVec";
