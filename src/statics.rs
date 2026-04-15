// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Static constants and regex patterns used throughout the crate.
//!
//! This module defines the canonical string names for built-in SMTLib sorts, operators,
//! and functions, as well as regex patterns for validating bitvector literal symbols and
//! SMTLib symbol syntax.

use lazy_static::lazy_static;
use regex::Regex;

lazy_static! {
    pub static ref BV_RE: Regex = Regex::new("^bv(0|[1-9][0-9]*)$").unwrap();
    pub static ref SYMBOL_RE: Regex =
        Regex::new(r"^[A-Za-z~!@$%^&*_\-+=<>.?/]+[0-9A-Za-z~!@$%^&*_\-+=<>.?/]*$").unwrap();
}

// Sort names
pub const BOOL: &str = "Bool";
pub const INT: &str = "Int";
pub const REAL: &str = "Real";
pub const STRING: &str = "String";
pub const REGLAN: &str = "RegLan";
pub const ARRAY: &str = "Array";
pub const BITVEC: &str = "BitVec";

// Core logic operators
pub const AND: &str = "and";
pub const OR: &str = "or";
pub const NOT: &str = "not";
pub const IMPLIES: &str = "=>";
pub const XOR: &str = "xor";
pub const EQ: &str = "=";
pub const DISTINCT: &str = "distinct";
pub const ITE: &str = "ite";

// Arithmetic and comparison operators (Ints / Reals)
pub const ADD: &str = "+";
pub const SUB: &str = "-";
pub const MUL: &str = "*";
pub const IDIV: &str = "div";
pub const RDIV: &str = "/";
pub const MOD: &str = "mod";
pub const ABS: &str = "abs";
pub const LE: &str = "<=";
pub const LT: &str = "<";
pub const GE: &str = ">=";
pub const GT: &str = ">";
pub const TO_REAL: &str = "to_real";
pub const TO_INT: &str = "to_int";
pub const IS_INT: &str = "is_int";

// Array operators
pub const SELECT: &str = "select";
pub const STORE: &str = "store";

// String operators
pub const CHAR: &str = "char";
pub const STR_CONCAT: &str = "str.++";
pub const STR_LEN: &str = "str.len";
pub const STR_LT: &str = "str.<";
pub const STR_TO_RE: &str = "str.to_re";
pub const STR_IN_RE: &str = "str.in_re";
pub const STR_LE: &str = "str.<=";
pub const STR_AT: &str = "str.at";
pub const STR_SUBSTR: &str = "str.substr";
pub const STR_PREFIXOF: &str = "str.prefixof";
pub const STR_SUFFIXOF: &str = "str.suffixof";
pub const STR_CONTAINS: &str = "str.contains";
pub const STR_INDEXOF: &str = "str.indexof";
pub const STR_REPLACE: &str = "str.replace";
pub const STR_REPLACE_ALL: &str = "str.replace_all";
pub const STR_REPLACE_RE: &str = "str.replace_re";
pub const STR_REPLACE_RE_ALL: &str = "str.replace_re_all";
pub const STR_IS_DIGIT: &str = "str.is_digit";
pub const STR_TO_CODE: &str = "str.to_code";
pub const STR_FROM_CODE: &str = "str.from_code";
pub const STR_TO_INT: &str = "str.to_int";
pub const STR_FROM_INT: &str = "str.from_int";

// Regex operators
pub const RE_NONE: &str = "re.none";
pub const RE_ALL: &str = "re.all";
pub const RE_ALLCHAR: &str = "re.allchar";
pub const RE_CONCAT: &str = "re.++";
pub const RE_UNION: &str = "re.union";
pub const RE_INTER: &str = "re.inter";
pub const RE_STAR: &str = "re.*";
pub const RE_COMP: &str = "re.comp";
pub const RE_DIFF: &str = "re.diff";
pub const RE_ADD: &str = "re.+";
pub const RE_OPT: &str = "re.opt";
pub const RE_RANGE: &str = "re.range";
pub const RE_POWER: &str = "re.^";
pub const RE_LOOP: &str = "re.loop";

// Bitvector operators
pub const BV_CONCAT: &str = "concat";
pub const BV_EXTRACT: &str = "extract";
pub const BV_NOT: &str = "bvnot";
pub const BV_NEG: &str = "bvneg";
pub const BV_AND: &str = "bvand";
pub const BV_OR: &str = "bvor";
pub const BV_ADD: &str = "bvadd";
pub const BV_MUL: &str = "bvmul";
pub const BV_UDIV: &str = "bvudiv";
pub const BV_UREM: &str = "bvurem";
pub const BV_SHL: &str = "bvshl";
pub const BV_LSHR: &str = "bvlshr";
pub const BV_ULT: &str = "bvult";
pub const BV_NEGO: &str = "bvnego";
pub const BV_UADDO: &str = "bvuaddo";
pub const BV_SADDO: &str = "bvsaddo";
pub const BV_UMULO: &str = "bvumulo";
pub const BV_SMULO: &str = "bvsmulo";
pub const BV_NAND: &str = "bvnand";
pub const BV_NOR: &str = "bvnor";
pub const BV_XOR: &str = "bvxor";
pub const BV_XNOR: &str = "bvxnor";
pub const BV_COMP: &str = "bvcomp";
pub const BV_SUB: &str = "bvsub";
pub const BV_SDIV: &str = "bvsdiv";
pub const BV_SREM: &str = "bvsrem";
pub const BV_SMOD: &str = "bvsmod";
pub const BV_ASHR: &str = "bvashr";
pub const BV_USUBO: &str = "bvusubo";
pub const BV_SSUBO: &str = "bvssubo";
pub const BV_SDIVO: &str = "bvsdivo";
pub const BV_REPEAT: &str = "repeat";
pub const BV_ZERO_EXTEND: &str = "zero_extend";
pub const BV_SIGN_EXTEND: &str = "sign_extend";
pub const BV_ROTATE_LEFT: &str = "rotate_left";
pub const BV_ROTATE_RIGHT: &str = "rotate_right";
pub const BV_ULE: &str = "bvule";
pub const BV_UGT: &str = "bvugt";
pub const BV_UGE: &str = "bvuge";
pub const BV_SLT: &str = "bvslt";
pub const BV_SLE: &str = "bvsle";
pub const BV_SGT: &str = "bvsgt";
pub const BV_SGE: &str = "bvsge";

// Bitvector-integer conversion operators
pub const UBV_TO_INT: &str = "ubv_to_int";
pub const SBV_TO_INT: &str = "sbv_to_int";
pub const BV2NAT: &str = "bv2nat";
pub const BV2INT: &str = "bv2int";
pub const INT_TO_BV: &str = "int_to_bv";
pub const NAT2BV: &str = "nat2bv";
pub const INT2BV: &str = "int2bv";

// Datatype operators
pub const IS: &str = "is";
pub const IS_DASH: &str = "is-";
