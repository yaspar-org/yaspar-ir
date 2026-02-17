// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::ast::alg::Index;
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
    /// non-standard
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
            IdentifierKind::And => "and",
            IdentifierKind::Or => "or",
            IdentifierKind::Not => "not",
            IdentifierKind::Implies => "=>",
            IdentifierKind::Xor => "xor",
            IdentifierKind::Eq => "=",
            IdentifierKind::Distinct => "distinct",
            IdentifierKind::Ite => "ite",
            IdentifierKind::Select => "select",
            IdentifierKind::Store => "store",
            IdentifierKind::Add => "+",
            IdentifierKind::Sub => "-",
            IdentifierKind::Mul => "*",
            IdentifierKind::Idiv => "div",
            IdentifierKind::Rdiv => "/",
            IdentifierKind::Mod => "mod",
            IdentifierKind::Abs => "abs",
            IdentifierKind::Le => "<=",
            IdentifierKind::Lt => "<",
            IdentifierKind::Ge => ">=",
            IdentifierKind::Gt => ">",
            IdentifierKind::ToReal => "to_real",
            IdentifierKind::ToInt => "to_int",
            IdentifierKind::IsInt => "is_int",
            IdentifierKind::Char(_, _) => "char",
            IdentifierKind::StrConcat => "str.++",
            IdentifierKind::StrLen => "str.len",
            IdentifierKind::StrLt => "str.<",
            IdentifierKind::StrToRe => "str.to_re",
            IdentifierKind::StrInRe => "str.in_re",
            IdentifierKind::ReNone => "re.none",
            IdentifierKind::ReAll => "re.all",
            IdentifierKind::ReAllChar => "re.allchar",
            IdentifierKind::ReConcat => "re.++",
            IdentifierKind::ReUnion => "re.union",
            IdentifierKind::ReInter => "re.inter",
            IdentifierKind::ReStar => "re.*",
            IdentifierKind::StrLe => "str.<=",
            IdentifierKind::StrAt => "str.at",
            IdentifierKind::StrSubstr => "str.substr",
            IdentifierKind::StrPrefixof => "str.prefixof",
            IdentifierKind::StrSuffixof => "str.suffixof",
            IdentifierKind::StrContains => "str.contains",
            IdentifierKind::StrIndexof => "str.indexof",
            IdentifierKind::StrReplace => "str.replace",
            IdentifierKind::StrReplaceAll => "str.replace_all",
            IdentifierKind::StrReplaceRe => "str.replace_re",
            IdentifierKind::StrReplaceReAll => "str.replace_re_all",
            IdentifierKind::ReComp => "re.comp",
            IdentifierKind::ReDiff => "re.diff",
            IdentifierKind::ReAdd => "re.+",
            IdentifierKind::ReOpt => "re.opt",
            IdentifierKind::ReRange => "re.range",
            IdentifierKind::RePower(_) => "re.^",
            IdentifierKind::ReLoop(_, _) => "re.loop",
            IdentifierKind::StrIsDigit => "str.is_digit",
            IdentifierKind::StrToCode => "str.to_code",
            IdentifierKind::StrFromCode => "str.from_code",
            IdentifierKind::StrToInt => "str.to_int",
            IdentifierKind::StrFromInt => "str.from_int",
            IdentifierKind::Concat => "concat",
            IdentifierKind::Extract(_, _) => "extract",
            IdentifierKind::BvNot => "bvnot",
            IdentifierKind::BvNeg => "bvneg",
            IdentifierKind::BvAnd => "bvand",
            IdentifierKind::BvOr => "bvor",
            IdentifierKind::BvAdd => "bvadd",
            IdentifierKind::BvMul => "bvmul",
            IdentifierKind::BvUdiv => "bvudiv",
            IdentifierKind::BvUrem => "bvurem",
            IdentifierKind::BvShl => "bvshl",
            IdentifierKind::BvLshr => "bvlshr",
            IdentifierKind::BvUlt => "bvult",
            IdentifierKind::BvNego => "bvnego",
            IdentifierKind::BvUaddo => "bvuaddo",
            IdentifierKind::BvSaddo => "bvsaddo",
            IdentifierKind::BvUmulo => "bvumulo",
            IdentifierKind::BvSmulo => "bvsmulo",
            IdentifierKind::UbvToInt => "ubv_to_int",
            IdentifierKind::SbvToInt => "sbv_to_int",
            IdentifierKind::Bv2Nat => "bv2nat",
            IdentifierKind::Bv2Int => "bv2int",
            IdentifierKind::IntToBv(_) => "int_to_bv",
            IdentifierKind::Nat2Bv(_) => "nat2bv",
            IdentifierKind::Int2Bv(_) => "int2bv",
            IdentifierKind::BvNand => "bvnand",
            IdentifierKind::BvNor => "bvnor",
            IdentifierKind::BvXor => "bvxor",
            IdentifierKind::BvNxor => "bvnxor",
            IdentifierKind::BvComp => "bvcomp",
            IdentifierKind::BvSub => "bvsub",
            IdentifierKind::BvSdiv => "bvsdiv",
            IdentifierKind::BvSrem => "bvsrem",
            IdentifierKind::BvSmod => "bvsmod",
            IdentifierKind::BvAShr => "bvashr",
            IdentifierKind::BvUsubo => "bvusubo",
            IdentifierKind::BvSsubo => "bvssubo",
            IdentifierKind::BvSdivo => "bvsdivo",
            IdentifierKind::Repeat(_) => "repeat",
            IdentifierKind::ZeroExtend(_) => "zero_extend",
            IdentifierKind::SignExtend(_) => "sign_extend",
            IdentifierKind::RotateLeft(_) => "rotate_left",
            IdentifierKind::RotateRight(_) => "rotate_right",
            IdentifierKind::BvUle => "bvule",
            IdentifierKind::BvUgt => "bvugt",
            IdentifierKind::BvUge => "bvuge",
            IdentifierKind::BvSlt => "bvslt",
            IdentifierKind::BvSle => "bvsle",
            IdentifierKind::BvSgt => "bvsgt",
            IdentifierKind::BvSge => "bvsge",
            IdentifierKind::Is(_) => "is",
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
