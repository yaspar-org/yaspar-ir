// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! This module stores the static constants in the crate

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
