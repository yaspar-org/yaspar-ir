// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::ast::alg::Index;
use crate::statics::*;
use dashu::integer::UBig;
use serde::{Deserialize, Serialize};

/// Describe pre-defined kinds for identifiers
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum IdentifierKind<Str> {
    // Core
    And,
    Or,
    Not,
    Implies,
    Xor,
    Eq,
    Distinct,
    Ite,

    // ArrayEx
    Const,
    Select,
    Store,

    // Ints and Reals
    Add,
    /// includes unary minus
    Sub,
    Mul,
    /// div; integer division
    Idiv,
    /// /; real division
    Rdiv,
    Mod,
    Abs,
    Le,
    Lt,
    Ge,
    Gt,
    ToReal,
    ToInt,
    IsInt,

    // Strings
    Char(Vec<u8>, usize),
    StrConcat,
    StrLen,
    StrLt,
    StrToRe,
    StrInRe,
    ReNone,
    ReAll,
    ReAllChar,
    ReConcat,
    ReUnion,
    ReInter,
    ReStar,
    StrLe,
    StrAt,
    StrSubstr,
    StrPrefixof,
    StrSuffixof,
    StrContains,
    StrIndexof,
    StrReplace,
    StrReplaceAll,
    StrReplaceRe,
    StrReplaceReAll,
    ReComp,
    ReDiff,
    ReAdd,
    ReOpt,
    ReRange,
    RePower(UBig),
    ReLoop(UBig, UBig),
    StrIsDigit,
    StrToCode,
    StrFromCode,
    StrToInt,
    StrFromInt,

    // Bit Vectors
    Concat,
    Extract(UBig, UBig),
    BvNot,
    BvNeg,
    BvAnd,
    BvOr,
    BvAdd,
    BvMul,
    BvUdiv,
    BvUrem,
    BvShl,
    BvLshr,
    BvUlt,
    BvNego,
    BvUaddo,
    BvSaddo,
    BvUmulo,
    BvSmulo,
    /// standard
    UbvToInt,
    /// standard
    SbvToInt,
    /// non-standard
    Bv2Nat,
    /// non-standard
    Bv2Int,
    /// standard
    IntToBv(UBig),
    /// non-standard
    Nat2Bv(UBig),
    /// non-standard
    Int2Bv(UBig),
    BvNand,
    BvNor,
    BvXor,
    BvNxor,
    BvComp,
    BvSub,
    BvSdiv,
    BvSrem,
    BvSmod,
    BvAShr,
    BvUsubo,
    BvSsubo,
    BvSdivo,
    Repeat(UBig),
    ZeroExtend(UBig),
    SignExtend(UBig),
    RotateLeft(UBig),
    RotateRight(UBig),
    BvUle,
    BvUgt,
    BvUge,
    BvSlt,
    BvSle,
    BvSgt,
    BvSge,

    // datatypes
    Is(Str),
}

impl<Str> IdentifierKind<Str> {
    pub fn name(&self) -> &'static str {
        match self {
            IdentifierKind::And => AND,
            IdentifierKind::Or => OR,
            IdentifierKind::Not => NOT,
            IdentifierKind::Implies => IMPLIES,
            IdentifierKind::Xor => XOR,
            IdentifierKind::Eq => EQ,
            IdentifierKind::Distinct => DISTINCT,
            IdentifierKind::Ite => ITE,
            IdentifierKind::Const => CONST,
            IdentifierKind::Select => SELECT,
            IdentifierKind::Store => STORE,
            IdentifierKind::Add => ADD,
            IdentifierKind::Sub => SUB,
            IdentifierKind::Mul => MUL,
            IdentifierKind::Idiv => IDIV,
            IdentifierKind::Rdiv => RDIV,
            IdentifierKind::Mod => MOD,
            IdentifierKind::Abs => ABS,
            IdentifierKind::Le => LE,
            IdentifierKind::Lt => LT,
            IdentifierKind::Ge => GE,
            IdentifierKind::Gt => GT,
            IdentifierKind::ToReal => TO_REAL,
            IdentifierKind::ToInt => TO_INT,
            IdentifierKind::IsInt => IS_INT,
            IdentifierKind::Char(_, _) => CHAR,
            IdentifierKind::StrConcat => STR_CONCAT,
            IdentifierKind::StrLen => STR_LEN,
            IdentifierKind::StrLt => STR_LT,
            IdentifierKind::StrToRe => STR_TO_RE,
            IdentifierKind::StrInRe => STR_IN_RE,
            IdentifierKind::ReNone => RE_NONE,
            IdentifierKind::ReAll => RE_ALL,
            IdentifierKind::ReAllChar => RE_ALLCHAR,
            IdentifierKind::ReConcat => RE_CONCAT,
            IdentifierKind::ReUnion => RE_UNION,
            IdentifierKind::ReInter => RE_INTER,
            IdentifierKind::ReStar => RE_STAR,
            IdentifierKind::StrLe => STR_LE,
            IdentifierKind::StrAt => STR_AT,
            IdentifierKind::StrSubstr => STR_SUBSTR,
            IdentifierKind::StrPrefixof => STR_PREFIXOF,
            IdentifierKind::StrSuffixof => STR_SUFFIXOF,
            IdentifierKind::StrContains => STR_CONTAINS,
            IdentifierKind::StrIndexof => STR_INDEXOF,
            IdentifierKind::StrReplace => STR_REPLACE,
            IdentifierKind::StrReplaceAll => STR_REPLACE_ALL,
            IdentifierKind::StrReplaceRe => STR_REPLACE_RE,
            IdentifierKind::StrReplaceReAll => STR_REPLACE_RE_ALL,
            IdentifierKind::ReComp => RE_COMP,
            IdentifierKind::ReDiff => RE_DIFF,
            IdentifierKind::ReAdd => RE_ADD,
            IdentifierKind::ReOpt => RE_OPT,
            IdentifierKind::ReRange => RE_RANGE,
            IdentifierKind::RePower(_) => RE_POWER,
            IdentifierKind::ReLoop(_, _) => RE_LOOP,
            IdentifierKind::StrIsDigit => STR_IS_DIGIT,
            IdentifierKind::StrToCode => STR_TO_CODE,
            IdentifierKind::StrFromCode => STR_FROM_CODE,
            IdentifierKind::StrToInt => STR_TO_INT,
            IdentifierKind::StrFromInt => STR_FROM_INT,
            IdentifierKind::Concat => BV_CONCAT,
            IdentifierKind::Extract(_, _) => BV_EXTRACT,
            IdentifierKind::BvNot => BV_NOT,
            IdentifierKind::BvNeg => BV_NEG,
            IdentifierKind::BvAnd => BV_AND,
            IdentifierKind::BvOr => BV_OR,
            IdentifierKind::BvAdd => BV_ADD,
            IdentifierKind::BvMul => BV_MUL,
            IdentifierKind::BvUdiv => BV_UDIV,
            IdentifierKind::BvUrem => BV_UREM,
            IdentifierKind::BvShl => BV_SHL,
            IdentifierKind::BvLshr => BV_LSHR,
            IdentifierKind::BvUlt => BV_ULT,
            IdentifierKind::BvNego => BV_NEGO,
            IdentifierKind::BvUaddo => BV_UADDO,
            IdentifierKind::BvSaddo => BV_SADDO,
            IdentifierKind::BvUmulo => BV_UMULO,
            IdentifierKind::BvSmulo => BV_SMULO,
            IdentifierKind::UbvToInt => UBV_TO_INT,
            IdentifierKind::SbvToInt => SBV_TO_INT,
            IdentifierKind::Bv2Nat => BV2NAT,
            IdentifierKind::Bv2Int => BV2INT,
            IdentifierKind::IntToBv(_) => INT_TO_BV,
            IdentifierKind::Nat2Bv(_) => NAT2BV,
            IdentifierKind::Int2Bv(_) => INT2BV,
            IdentifierKind::BvNand => BV_NAND,
            IdentifierKind::BvNor => BV_NOR,
            IdentifierKind::BvXor => BV_XOR,
            IdentifierKind::BvNxor => BV_XNOR,
            IdentifierKind::BvComp => BV_COMP,
            IdentifierKind::BvSub => BV_SUB,
            IdentifierKind::BvSdiv => BV_SDIV,
            IdentifierKind::BvSrem => BV_SREM,
            IdentifierKind::BvSmod => BV_SMOD,
            IdentifierKind::BvAShr => BV_ASHR,
            IdentifierKind::BvUsubo => BV_USUBO,
            IdentifierKind::BvSsubo => BV_SSUBO,
            IdentifierKind::BvSdivo => BV_SDIVO,
            IdentifierKind::Repeat(_) => BV_REPEAT,
            IdentifierKind::ZeroExtend(_) => BV_ZERO_EXTEND,
            IdentifierKind::SignExtend(_) => BV_SIGN_EXTEND,
            IdentifierKind::RotateLeft(_) => BV_ROTATE_LEFT,
            IdentifierKind::RotateRight(_) => BV_ROTATE_RIGHT,
            IdentifierKind::BvUle => BV_ULE,
            IdentifierKind::BvUgt => BV_UGT,
            IdentifierKind::BvUge => BV_UGE,
            IdentifierKind::BvSlt => BV_SLT,
            IdentifierKind::BvSle => BV_SLE,
            IdentifierKind::BvSgt => BV_SGT,
            IdentifierKind::BvSge => BV_SGE,
            IdentifierKind::Is(_) => IS,
        }
    }

    pub fn indices(&self) -> Vec<Index<Str>>
    where
        Str: Clone,
    {
        match self {
            IdentifierKind::And
            | IdentifierKind::Or
            | IdentifierKind::Not
            | IdentifierKind::Implies
            | IdentifierKind::Xor
            | IdentifierKind::Eq
            | IdentifierKind::Distinct
            | IdentifierKind::Ite
            | IdentifierKind::Const
            | IdentifierKind::Select
            | IdentifierKind::Store
            | IdentifierKind::Add
            | IdentifierKind::Sub
            | IdentifierKind::Mul
            | IdentifierKind::Idiv
            | IdentifierKind::Rdiv
            | IdentifierKind::Mod
            | IdentifierKind::Abs
            | IdentifierKind::Le
            | IdentifierKind::Lt
            | IdentifierKind::Ge
            | IdentifierKind::Gt
            | IdentifierKind::ToReal
            | IdentifierKind::ToInt
            | IdentifierKind::IsInt
            | IdentifierKind::StrConcat
            | IdentifierKind::StrLen
            | IdentifierKind::StrLt
            | IdentifierKind::StrToRe
            | IdentifierKind::StrInRe
            | IdentifierKind::ReNone
            | IdentifierKind::ReAll
            | IdentifierKind::ReAllChar
            | IdentifierKind::ReConcat
            | IdentifierKind::ReUnion
            | IdentifierKind::ReInter
            | IdentifierKind::ReStar
            | IdentifierKind::StrLe
            | IdentifierKind::StrAt
            | IdentifierKind::StrSubstr
            | IdentifierKind::StrPrefixof
            | IdentifierKind::StrSuffixof
            | IdentifierKind::StrContains
            | IdentifierKind::StrIndexof
            | IdentifierKind::StrReplace
            | IdentifierKind::StrReplaceAll
            | IdentifierKind::StrReplaceRe
            | IdentifierKind::StrReplaceReAll
            | IdentifierKind::ReComp
            | IdentifierKind::ReDiff
            | IdentifierKind::ReAdd
            | IdentifierKind::ReOpt
            | IdentifierKind::ReRange
            | IdentifierKind::StrIsDigit
            | IdentifierKind::StrToCode
            | IdentifierKind::StrFromCode
            | IdentifierKind::StrToInt
            | IdentifierKind::StrFromInt
            | IdentifierKind::Concat
            | IdentifierKind::BvNot
            | IdentifierKind::BvNeg
            | IdentifierKind::BvAnd
            | IdentifierKind::BvOr
            | IdentifierKind::BvAdd
            | IdentifierKind::BvMul
            | IdentifierKind::BvUdiv
            | IdentifierKind::BvUrem
            | IdentifierKind::BvShl
            | IdentifierKind::BvLshr
            | IdentifierKind::BvUlt
            | IdentifierKind::BvNego
            | IdentifierKind::BvUaddo
            | IdentifierKind::BvSaddo
            | IdentifierKind::BvUmulo
            | IdentifierKind::BvSmulo
            | IdentifierKind::UbvToInt
            | IdentifierKind::SbvToInt
            | IdentifierKind::Bv2Nat
            | IdentifierKind::Bv2Int
            | IdentifierKind::BvNand
            | IdentifierKind::BvNor
            | IdentifierKind::BvXor
            | IdentifierKind::BvNxor
            | IdentifierKind::BvComp
            | IdentifierKind::BvSub
            | IdentifierKind::BvSdiv
            | IdentifierKind::BvSrem
            | IdentifierKind::BvSmod
            | IdentifierKind::BvAShr
            | IdentifierKind::BvUsubo
            | IdentifierKind::BvSsubo
            | IdentifierKind::BvSdivo
            | IdentifierKind::BvUle
            | IdentifierKind::BvUgt
            | IdentifierKind::BvUge
            | IdentifierKind::BvSlt
            | IdentifierKind::BvSle
            | IdentifierKind::BvSgt
            | IdentifierKind::BvSge => {
                vec![]
            }
            IdentifierKind::RePower(n)
            | IdentifierKind::IntToBv(n)
            | IdentifierKind::Nat2Bv(n)
            | IdentifierKind::Int2Bv(n)
            | IdentifierKind::Repeat(n)
            | IdentifierKind::ZeroExtend(n)
            | IdentifierKind::SignExtend(n)
            | IdentifierKind::RotateLeft(n)
            | IdentifierKind::RotateRight(n) => {
                vec![Index::Numeral(n.clone())]
            }
            IdentifierKind::ReLoop(n, m) | IdentifierKind::Extract(n, m) => {
                vec![Index::Numeral(n.clone()), Index::Numeral(m.clone())]
            }
            IdentifierKind::Char(bs, l) => {
                vec![Index::Hexadecimal(bs.clone(), *l)]
            }

            IdentifierKind::Is(s) => {
                vec![Index::Symbol(s.clone())]
            }
        }
    }
}
