// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! # Algebra of Abstract Syntax Trees (ASTs)
//!
//! This module models ASTs as their respective (polynomial) algebras. The idea is to use
//! type variables to capture critical subcomponents, e.g. strings, so that they can be handled
//! later on by special instantiations. For example,  [Constant] below abstracts a type variable `Str`
//! to represent strings. One possible instantiation is [`Constant<String>`], which uses [String] to
//! represent all strings. However, subsequently, in `super::instance`, we show a different instantiation,
//! which uses an interning library to make string representation more efficient.
//!
//! Another advantage of this algebraic approach is to break recursion. For example, [Term] below
//! uses the type variable `T` to represent the recursive reference. We can then later use different
//! fixpoints to tie up the knots to create different instantiations of ASTs, possibly with different
//! motivations. One obvious instantiation is to set `T` a boxed version of itself. Again, in
//! `super::instance`, we show a more memory-efficient version using an interning library.

use crate::statics::{ARRAY, BITVEC, BOOL, INT, REAL, REGLAN, STRING, SYMBOL_RE};
use crate::traits::Contains;
use dashu::float::DBig;
use dashu::integer::UBig;
pub use kind::IdentifierKind;
use num_order::NumHash;
use serde::{Deserialize, Serialize};
use std::fmt::{Display, Formatter, Write};
use std::hash::{Hash, Hasher};
use std::ops::{Add, Mul, Sub};
use yaspar::ast::Keyword;
use yaspar::tokens::SPECIAL_SYMBOLS;
use yaspar::{binary_to_string, hex_to_string};

mod kind;

/// Represent a literal constant in SMTLib
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Constant<Str> {
    /// numerals are non-negative
    Numeral(UBig),
    Decimal(DBig),
    /// escape "" has been handled
    String(Str),
    /// #b
    Binary(Vec<u8>, usize),
    /// #x
    Hexadecimal(Vec<u8>, usize),
    Bool(bool),
}

// this trait needs to be implemented by hand, because DBig, or FBig in general, does not implement
// [Hash], but only `NumHash`.
impl<Str> Hash for Constant<Str>
where
    Str: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Constant::Numeral(u) => {
                state.write_u8(0);
                u.hash(state);
            }
            Constant::Decimal(d) => {
                state.write_u8(1);
                d.num_hash(state);
            }
            Constant::String(s) => {
                state.write_u8(2);
                s.hash(state);
            }
            Constant::Binary(v, l) => {
                state.write_u8(3);
                v.hash(state);
                l.hash(state);
            }
            Constant::Hexadecimal(v, l) => {
                state.write_u8(4);
                v.hash(state);
                l.hash(state);
            }
            Constant::Bool(b) => {
                state.write_u8(5);
                b.hash(state);
            }
        }
    }
}

/// Represent an index object that appear in an identifier
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Index<Str> {
    Numeral(UBig),
    Symbol(Str),
    Hexadecimal(Vec<u8>, usize), // #x
}

impl<Str> Index<Str> {
    pub fn is_numeral(&self) -> bool {
        matches!(self, Index::Numeral(_))
    }

    pub fn get_numeral(&self) -> Option<UBig> {
        match self {
            Index::Numeral(n) => Some(n.clone()),
            _ => None,
        }
    }
}

/// Represent an identifier in SMTLib
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Identifier<Str> {
    pub symbol: Str,
    pub indices: Vec<Index<Str>>,
}

/// This trait checks whether som identifier is a given string
pub trait CheckIdentifier<Str>
where
    Str: Contains<T = String>,
{
    fn get_kind(&self) -> Option<IdentifierKind<Str>>;
}

impl<Str> Identifier<Str> {
    /// Return a simple identifier without indices
    pub fn simple(s: Str) -> Self {
        Self {
            symbol: s,
            indices: vec![],
        }
    }
}

impl<Str> Identifier<Str>
where
    Str: Contains<T = String>,
{
    fn is_simple(&self, s: &str) -> bool {
        self.symbol.inner() == s && self.indices.is_empty()
    }
}

impl<Str> CheckIdentifier<Str> for Identifier<Str>
where
    Str: Contains<T = String> + Clone,
{
    fn get_kind(&self) -> Option<IdentifierKind<Str>> {
        match self.indices.as_slice() {
            [] => match self.symbol.inner().as_str() {
                "and" => Some(IdentifierKind::And),
                "or" => Some(IdentifierKind::Or),
                "not" => Some(IdentifierKind::Not),
                "=>" => Some(IdentifierKind::Implies),
                "xor" => Some(IdentifierKind::Xor),
                "=" => Some(IdentifierKind::Eq),
                "distinct" => Some(IdentifierKind::Distinct),
                "ite" => Some(IdentifierKind::Ite),
                "select" => Some(IdentifierKind::Select),
                "store" => Some(IdentifierKind::Store),
                "+" => Some(IdentifierKind::Add),
                "-" => Some(IdentifierKind::Sub),
                "*" => Some(IdentifierKind::Mul),
                "div" => Some(IdentifierKind::Idiv),
                "/" => Some(IdentifierKind::Rdiv),
                "mod" => Some(IdentifierKind::Mod),
                "abs" => Some(IdentifierKind::Abs),
                "<=" => Some(IdentifierKind::Le),
                "<" => Some(IdentifierKind::Lt),
                ">=" => Some(IdentifierKind::Ge),
                ">" => Some(IdentifierKind::Gt),
                "to_real" => Some(IdentifierKind::ToReal),
                "to_int" => Some(IdentifierKind::ToInt),
                "is_int" => Some(IdentifierKind::IsInt),
                "str.++" => Some(IdentifierKind::StrConcat),
                "str.len" => Some(IdentifierKind::StrLen),
                "str.<" => Some(IdentifierKind::StrLt),
                "str.to_re" => Some(IdentifierKind::StrToRe),
                "str.in_re" => Some(IdentifierKind::StrInRe),
                "re.none" => Some(IdentifierKind::ReNone),
                "re.all" => Some(IdentifierKind::ReAll),
                "re.allchar" => Some(IdentifierKind::ReAllChar),
                "re.++" => Some(IdentifierKind::ReConcat),
                "re.union" => Some(IdentifierKind::ReUnion),
                "re.inter" => Some(IdentifierKind::ReInter),
                "re.*" => Some(IdentifierKind::ReStar),
                "str.<=" => Some(IdentifierKind::StrLe),
                "str.at" => Some(IdentifierKind::StrAt),
                "str.substr" => Some(IdentifierKind::StrSubstr),
                "str.prefixof" => Some(IdentifierKind::StrPrefixof),
                "str.suffixof" => Some(IdentifierKind::StrSuffixof),
                "str.contains" => Some(IdentifierKind::StrContains),
                "str.indexof" => Some(IdentifierKind::StrIndexof),
                "str.replace" => Some(IdentifierKind::StrReplace),
                "str.replace_all" => Some(IdentifierKind::StrReplaceAll),
                "str.replace_re" => Some(IdentifierKind::StrReplaceRe),
                "str.replace_re_all" => Some(IdentifierKind::StrReplaceReAll),
                "re.comp" => Some(IdentifierKind::ReComp),
                "re.diff" => Some(IdentifierKind::ReDiff),
                "re.+" => Some(IdentifierKind::ReAdd),
                "re.opt" => Some(IdentifierKind::ReOpt),
                "re.range" => Some(IdentifierKind::ReRange),
                "str.is_digit" => Some(IdentifierKind::StrIsDigit),
                "str.to_code" => Some(IdentifierKind::StrToCode),
                "str.from_code" => Some(IdentifierKind::StrFromCode),
                "str.to_int" => Some(IdentifierKind::StrToInt),
                "str.from_int" => Some(IdentifierKind::StrFromInt),
                "concat" => Some(IdentifierKind::Concat),
                "bvnot" => Some(IdentifierKind::BvNot),
                "bvneg" => Some(IdentifierKind::BvNeg),
                "bvand" => Some(IdentifierKind::BvAnd),
                "bvor" => Some(IdentifierKind::BvOr),
                "bvadd" => Some(IdentifierKind::BvAdd),
                "bvmul" => Some(IdentifierKind::BvMul),
                "bvudiv" => Some(IdentifierKind::BvUdiv),
                "bvurem" => Some(IdentifierKind::BvUrem),
                "bvshl" => Some(IdentifierKind::BvShl),
                "bvlshr" => Some(IdentifierKind::BvLshr),
                "bvult" => Some(IdentifierKind::BvUlt),
                "bvnego" => Some(IdentifierKind::BvNego),
                "bvuaddo" => Some(IdentifierKind::BvUaddo),
                "bvsaddo" => Some(IdentifierKind::BvSaddo),
                "bvumulo" => Some(IdentifierKind::BvUmulo),
                "bvsmulo" => Some(IdentifierKind::BvSmulo),
                "ubv_to_int" => Some(IdentifierKind::UbvToInt),
                "sbv_to_int" => Some(IdentifierKind::SbvToInt),
                "bv2nat" => Some(IdentifierKind::Bv2Nat),
                "bv2int" => Some(IdentifierKind::Bv2Int),
                "bvnand" => Some(IdentifierKind::BvNand),
                "bvnor" => Some(IdentifierKind::BvNor),
                "bvxor" => Some(IdentifierKind::BvXor),
                "bvnxor" => Some(IdentifierKind::BvNxor),
                "bvcomp" => Some(IdentifierKind::BvComp),
                "bvsub" => Some(IdentifierKind::BvSub),
                "bvsdiv" => Some(IdentifierKind::BvSdiv),
                "bvsrem" => Some(IdentifierKind::BvSrem),
                "bvsmod" => Some(IdentifierKind::BvSmod),
                "bvashr" => Some(IdentifierKind::BvAShr),
                "bvusubo" => Some(IdentifierKind::BvUsubo),
                "bvssubo" => Some(IdentifierKind::BvSsubo),
                "bvsdivo" => Some(IdentifierKind::BvSdivo),
                "bvule" => Some(IdentifierKind::BvUle),
                "bvugt" => Some(IdentifierKind::BvUgt),
                "bvuge" => Some(IdentifierKind::BvUge),
                "bvslt" => Some(IdentifierKind::BvSlt),
                "bvsle" => Some(IdentifierKind::BvSle),
                "bvsgt" => Some(IdentifierKind::BvSgt),
                "bvsge" => Some(IdentifierKind::BvSge),
                _ => None,
            },
            [Index::Hexadecimal(bytes, l)] => match self.symbol.inner().as_str() {
                "char" => Some(IdentifierKind::Char(bytes.clone(), *l)),
                _ => None,
            },
            [Index::Numeral(n)] => match self.symbol.inner().as_str() {
                "re.^" => Some(IdentifierKind::RePower(n.clone())),
                "int_to_bv" => Some(IdentifierKind::IntToBv(n.clone())),
                "int2bv" => Some(IdentifierKind::Int2Bv(n.clone())),
                "nat2bv" => Some(IdentifierKind::Nat2Bv(n.clone())),
                "repeat" => Some(IdentifierKind::Repeat(n.clone())),
                "zero_extend" => Some(IdentifierKind::ZeroExtend(n.clone())),
                "sign_extend" => Some(IdentifierKind::SignExtend(n.clone())),
                "rotate_left" => Some(IdentifierKind::RotateLeft(n.clone())),
                "rotate_right" => Some(IdentifierKind::RotateRight(n.clone())),
                _ => None,
            },
            [Index::Symbol(sym)] => match self.symbol.inner().as_str() {
                "is" => Some(IdentifierKind::Is(sym.clone())),
                _ => None,
            },
            [Index::Numeral(l), Index::Numeral(h)] => match self.symbol.inner().as_str() {
                "re.loop" => Some(IdentifierKind::ReLoop(l.clone(), h.clone())),
                "extract" => Some(IdentifierKind::Extract(l.clone(), h.clone())),
                _ => None,
            },
            _ => None,
        }
    }
}

/// Represent local variables
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Local<Str, So> {
    /// This is a special number to keep track of the variable, so that it is distinguished from
    /// other variables of the same name.
    ///
    /// This field is necessary to avoid unintentional name clashing.
    ///
    /// c.f. [VarBinding]
    pub id: usize,
    /// The variable name
    pub symbol: Str,
    /// The sort of local variable
    ///
    /// Invariant: this field must be `Some` in typed AST
    pub sort: Option<So>,
}

impl<Str, So> Local<Str, So> {
    /// Return a reference to the variable name
    pub fn id_str(&self) -> &Str {
        &self.symbol
    }
}

/// Represent attributes in SMTLib
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Attribute<Str, T> {
    /// A keyword attribute without a value
    Keyword(Keyword),
    /// A keyword attribute with a constant value
    Constant(Keyword, Constant<Str>),
    /// A keyword attribute with a symbol value
    Symbol(Keyword, Str),
    /// Special attribute :named symbol
    Named(Str),
    /// Special attribute :pattern (term+)
    Pattern(Vec<T>),
}

/// Represent sorts in SMTLib
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Sort<Str, So>(pub Identifier<Str>, pub Vec<So>);

impl<Str, So> Sort<Str, So> {
    pub fn sort_name(&self) -> &Str {
        &self.0.symbol
    }
}

impl<Str, So> Sort<Str, So>
where
    Str: Contains<T = String>,
    So: Clone,
{
    /// Check whether self is a nullary sort with the given name
    pub fn is_sort0(&self, name: &str) -> bool {
        self.0.is_simple(name) && self.1.is_empty()
    }

    /// Check whether it's Bool
    pub fn is_bool(&self) -> bool {
        self.is_sort0(BOOL)
    }

    /// Check whether it's Int
    pub fn is_int(&self) -> bool {
        self.is_sort0(INT)
    }

    /// Check whether it's Real
    pub fn is_real(&self) -> bool {
        self.is_sort0(REAL)
    }

    /// Check whether it's String
    pub fn is_string(&self) -> bool {
        self.is_sort0(STRING)
    }

    /// Check whether it's Reglan
    pub fn is_reglan(&self) -> bool {
        self.is_sort0(REGLAN)
    }

    /// Return `(in sort, out sort)` if the current sort is an `Array`
    pub fn is_array(&self) -> Option<(So, So)> {
        if self.0.is_simple(ARRAY) && self.1.len() == 2 {
            Some((self.1[0].clone(), self.1[1].clone()))
        } else {
            None
        }
    }

    /// Return the size if the current sort is a `BitVec`
    pub fn is_bv(&self) -> Option<UBig> {
        if !self.1.is_empty() || self.0.symbol.inner() != BITVEC || self.0.indices.len() != 1 {
            return None;
        }
        match &self.0.indices[0] {
            Index::Numeral(n) => Some(n.clone()),
            _ => None,
        }
    }
}

/// This type provides a spec of indices to be used in a signature
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SigIndex<Str> {
    Numeral,
    Symbol(Str),
    Hexadecimal,
}

/// An expression to express the calculation of bit vector lengths in the signature
///
/// c.f. [BvOutSort] and [Sig]
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum BvLenExpr {
    Fixed(UBig),
    /// De Bruijn level
    Var(usize),
    Add {
        left: Box<BvLenExpr>,
        right: Box<BvLenExpr>,
    },
    Sub {
        left: Box<BvLenExpr>,
        right: Box<BvLenExpr>,
    },
    Mul {
        left: Box<BvLenExpr>,
        right: Box<BvLenExpr>,
    },
}

impl BvLenExpr {
    /// Return a bit vector length of a fixed size
    pub fn fixed(num: usize) -> Self {
        Self::Fixed(UBig::from(num))
    }

    /// Return a bit vector length as a variable as a de Bruijn level
    pub fn var(idx: usize) -> Self {
        Self::Var(idx)
    }

    /// Given an evaluation environment, we evaluate the expression
    pub fn eval(&self, lengths: &[UBig]) -> Result<UBig, String> {
        match self {
            BvLenExpr::Fixed(sz) => Ok(sz.clone()),
            BvLenExpr::Var(n) => lengths
                .get(*n)
                .cloned()
                .ok_or_else(|| format!("index {n} out of bounds! env: {lengths:?}")),
            BvLenExpr::Add { left, right } => Ok(left.eval(lengths)? + right.eval(lengths)?),
            BvLenExpr::Sub { left, right } => {
                let l = left.eval(lengths)?;
                let r = right.eval(lengths)?;
                if l < r {
                    Err(format!("cannot subtract {r} from {l}!"))
                } else {
                    Ok(l - r)
                }
            }
            BvLenExpr::Mul { left, right } => Ok(left.eval(lengths)? * right.eval(lengths)?),
        }
    }
}

impl Add for BvLenExpr {
    type Output = BvLenExpr;

    fn add(self, right: BvLenExpr) -> Self {
        Self::Add {
            left: Box::new(self),
            right: Box::new(right),
        }
    }
}

impl Sub for BvLenExpr {
    type Output = BvLenExpr;

    fn sub(self, right: BvLenExpr) -> Self {
        Self::Sub {
            left: Box::new(self),
            right: Box::new(right),
        }
    }
}

impl Mul for BvLenExpr {
    type Output = BvLenExpr;

    fn mul(self, right: BvLenExpr) -> Self {
        Self::Mul {
            left: Box::new(self),
            right: Box::new(right),
        }
    }
}

/// An input sort involved in a bit-vector-related signature
///
/// Input sorts can only refer to a bv length variable, so it has to be more restricted than [BvOutSort].
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum BvInSort<So> {
    /// BitVec(n) where n is the index of corresponding length variable
    BitVec(usize),
    Sort(So),
}

/// An output sort involved in a bit-vector-related signature
///
/// It is possible to provide a bit vector, the length of which is a result of computation.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum BvOutSort<So> {
    BitVec(BvLenExpr),
    Sort(So),
}

impl<So> BvOutSort<So> {
    pub fn bv_var(idx: usize) -> Self {
        Self::BitVec(BvLenExpr::var(idx))
    }
}

/// Signature for functions
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Sig<Str, So> {
    /// ParFunc(sig_indices, sort_vars, input_sorts, output_sorts)
    ///
    /// Indices of a function must satisfy sig_indices in the exact order
    ///
    /// A polymorphic function with sort variables, and provided inputs and output
    ///
    /// If the list of variables is empty, then it's just a non-polymorphic function
    ParFunc(Vec<SigIndex<Str>>, Vec<Str>, Vec<So>, So),
    /// A function with a variable number of arguments
    ///
    /// ```text
    /// VarLenFunc(I, n, O) means (I, ... , I) -> O
    ///                             >= n times
    /// ```
    VarLenFunc(So, usize, So),
    /// The signature of a bit-vector-related function with fixed number of input arguments
    ///
    /// BvFunc(sig_indices, more_lens, is_extract, input_sorts, output_sorts)
    ///
    /// * sig_indices: the number of numeral indices as bv length parameters
    /// * more_lens: the number of additional bv length parameters
    ///
    /// `sig_indices + more_lens` is the number of bv length parameters allowed to appear in the
    /// function. Those in the quantifier indices have smaller indices in the list of parameters.
    ///
    /// The inputs must match input_sorts exactly, and the output is inferred to have output_sorts.
    ///
    /// When is_extract is set to true, we perform extra length check for extract.
    BvFunc(usize, usize, bool, Vec<BvInSort<So>>, BvOutSort<So>),
    /// A bit-vector function with a variable number of arguments
    ///
    /// ```text
    /// BvVarLenFunc(num_params, I, n, O) means (I, ... , I) -> O
    ///                                           >= n times
    /// ```
    ///
    /// Where num_params is the number of length parameters.
    BvVarLenFunc(usize, BvInSort<So>, usize, BvOutSort<So>),
    /// The bit-vector concat function
    ///
    /// It is a special case, because concat is an associative operation, which requires accumulation
    /// of bv lengths as well
    BvConcat,
}

impl<Str, So> Sig<Str, So> {
    /// Return a signature of a variable of a given sort
    pub fn sort(s: So) -> Self {
        Self::func(vec![], s)
    }

    /// Return a signature of a function with given input and output sorts
    pub fn func(inputs: Vec<So>, out: So) -> Self {
        Sig::ParFunc(vec![], vec![], inputs, out)
    }
}

impl<Str, So> From<So> for Sig<Str, So> {
    fn from(value: So) -> Self {
        Sig::sort(value)
    }
}

/// Qualified identifier with an optional sort qualification
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct QualifiedIdentifier<Str, So>(pub Identifier<Str>, pub Option<So>);

impl<Str, So> From<Identifier<Str>> for QualifiedIdentifier<Str, So> {
    fn from(value: Identifier<Str>) -> Self {
        Self(value, None)
    }
}

impl<Str, So> QualifiedIdentifier<Str, So> {
    /// Return a simple qualified identifier without indices
    pub fn simple(s: Str) -> Self {
        Self(Identifier::simple(s), None)
    }

    /// Return a simple identifier without indices, qualified by a sort
    pub fn simple_sorted(s: Str, sort: So) -> Self {
        Self(Identifier::simple(s), Some(sort))
    }

    /// Return a variant of the given identifier qualified with the given sort
    pub fn with_sort(&self, sort: So) -> Self
    where
        Str: Clone,
    {
        Self(self.0.clone(), Some(sort))
    }

    /// Return a reference to the symbol string
    pub fn id_str(&self) -> &Str {
        &self.0.symbol
    }
}

impl<Str, So> CheckIdentifier<Str> for QualifiedIdentifier<Str, So>
where
    Str: Contains<T = String> + Clone,
{
    fn get_kind(&self) -> Option<IdentifierKind<Str>> {
        self.0.get_kind()
    }
}

/// Bindings of a variable with a given piece of data
///
/// The second field is a special number that uniquely tracks the variable to avoid unintentional
/// variable clashing.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct VarBinding<Str, T>(pub Str, pub usize, pub T);

/// Represent terms in SMTLib
///
/// Invariants below only apply for typed ASTs.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Term<Str, So, T> {
    /// A constant literal
    ///
    /// Invariant: the second field must be [Some].
    Constant(Constant<Str>, Option<So>),
    /// A globally defined identifier
    ///
    /// This case is distinguished from [Term::Local], which represents local variables.
    ///
    /// Invariant:
    /// * The identifier must be bound in the symbol table in the global context.
    /// * the second field must be [Some].
    Global(QualifiedIdentifier<Str, So>, Option<So>),
    /// A local variable
    ///
    /// This field can be introduced by let-bindings, quantifiers and match expressions.
    ///
    /// Note that since every local variable is associated with an id, it is possible that two visually
    /// identical expressions to be compared not equal, i.e.
    /// ```text
    /// let x1 = Term::Local(...)  // prints to "x"
    /// let x2 = Term::Local(...)  // also prints to "x"
    /// assert_neq!(x1, x2);
    /// ```
    /// It has the consequence of two visually identical expressions, including quantifiers, comparing
    /// inequal.
    /// ```text
    /// let context = ...;
    /// let expr = "(forall ((x Int)) (do-something x))";
    /// let t1 = UntypedAst.parse_term_str(expr).unwrap().type_check(&mut context).unwrap();
    /// let t2 = UntypedAst.parse_term_str(expr).unwrap().type_check(&mut context).unwrap();
    /// assert_neq!(t1, t2);
    /// ```
    /// This is because we have no cheap way to decide whether two locally defined variables can
    /// coincide. In fact, it is a common mistake to equalize `t1` and `t2`. Consider another expression
    /// ```text
    /// let expr2 = "(forall ((x Int)) (do-something x y))";
    /// ```
    /// where `y` is some free variable. It is possible that `y` has different meanings, of different
    /// sorts in different contexts. Therefore, it is semantically unsafe to coincide printing equality
    /// and equality in ASTs.
    ///
    /// In general, it is possible to decide whether two local variables can coincide, i.e. it is
    /// possible to soundly equalize `t1` and `t2` above, but this decision function must take
    /// **ambient context** into account. In other words, semantic equality is a ternary operation
    /// with a context as an input.
    ///
    /// Invariant: the variable must be bound in an ambient structure that can introduce variables,
    /// as listed above.
    Local(Local<Str, So>),
    /// A function application
    ///
    /// Invariant: the third field must be [Some].
    App(QualifiedIdentifier<Str, So>, Vec<T>, Option<So>),
    /// A let-binding
    Let(Vec<VarBinding<Str, T>>, T),
    /// An existential quantifier
    Exists(Vec<VarBinding<Str, So>>, T),
    /// A universal quantifier
    Forall(Vec<VarBinding<Str, So>>, T),
    /// A match expression for a datatype
    ///
    /// Invariant:
    /// * The first term, i.e. the scrutinee, must have a datatype sort.
    /// * There must be at least one arm.
    /// * All arms must be covering, i.e. all cases of the datatype must find an arm.
    /// * All bodies in the arms must have the same sort.
    Matching(T, Vec<PatternArm<Str, T>>),
    /// A term annotated with attributes
    Annotated(T, Vec<Attribute<Str, T>>),
    /// An equality
    ///
    /// We restrict equality to be binary
    ///
    /// Invariant: two terms must have the same sort.
    Eq(T, T),
    /// Invariant: vector must contain at least two terms of the same sort.
    Distinct(Vec<T>),

    // logical connectives
    /// Invariant: vector must contain at least one term of sort Bool.
    And(Vec<T>),
    /// Invariant: vector must contain at least one term of sort Bool.
    Or(Vec<T>),
    /// Invariant:
    /// * vector must contain at least one term of sort Bool.
    /// * conclusion must have sort Bool.
    Implies(Vec<T>, T),
    /// Invariant: term must have sort Bool.
    Not(T),
    /// Invariant:
    /// * The first term must have sort Bool.
    /// * The other two terms must have the same sort.
    Ite(T, T, T),
}

impl<Str, So, T> Term<Str, So, T> {
    /// Check whether a term is a constant
    pub fn is_constant(&self) -> bool {
        matches!(self, Term::Constant(_, _))
    }
}

impl<Str, So, T> From<Constant<Str>> for Term<Str, So, T> {
    fn from(value: Constant<Str>) -> Self {
        Term::Constant(value, None)
    }
}

/// Pattern representation in a match expression
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Pattern<Str> {
    /// Represents a wildcard case
    ///
    /// Invariant: If the option is a [Some], then the symbol must not be a constructor.
    Wildcard(Option<(Str, usize)>),
    /// Invariant: The symbol must be a constructor with no arguments.
    ///
    /// This is an invariant maintained by the type checker.
    Ctor(Str),
    /// Invariant: `ctor` must be a constructor; `arguments` must have the exact same length as
    /// required by the constructor, i.e. arguments must be non-empty.
    ///
    /// A [None] in arguments means a wildcard.
    Applied {
        ctor: Str,
        arguments: Vec<Option<(Str, usize)>>,
    },
}

impl<Str> Pattern<Str> {
    /// Return variables of the given [Pattern]
    pub fn variables(&self) -> Vec<&Str> {
        match self {
            Pattern::Wildcard(None) | Pattern::Ctor(_) => {
                vec![]
            }
            Pattern::Wildcard(Some((name, _))) => {
                vec![name]
            }
            Pattern::Applied { arguments, .. } => arguments
                .iter()
                .filter_map(|o| {
                    if let Some((name, _)) = o {
                        Some(name)
                    } else {
                        None
                    }
                })
                .collect(),
        }
    }
}

/// An arm in a match expression; there is a pattern and a body
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct PatternArm<Str, T> {
    pub pattern: Pattern<Str>,
    pub body: T,
}

/// A definition of sorts; introduced by `declare-sort` or `define-sort`
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SortDef<Str, So> {
    /// Arity; the sort is opaque
    Opaque(usize),
    /// The sort is defined in terms of other sorts.
    Transparent { params: Vec<Str>, sort: So },
    /// The sort is a datatype.
    Datatype(DatatypeDec<Str, So>),
}

impl<Str, So> SortDef<Str, So> {
    /// Return the arity of the sort definition
    pub fn arity(&self) -> usize {
        match self {
            SortDef::Opaque(n) => *n,
            SortDef::Transparent { params, .. } => params.len(),
            SortDef::Datatype(dt) => dt.params.len(),
        }
    }
}

/// The declaration of a constructor of a datatype
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ConstructorDec<Str, So> {
    /// The name of the constructor
    pub ctor: Str,
    /// The arguments of the constructor with the specified sorts
    pub args: Vec<VarBinding<Str, So>>,
}

/// The declaration of an individual datatype; it is possible for it to be defined recursively with
/// other datatypes.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct DatatypeDec<Str, So> {
    /// sort parameters introduced by `par`
    ///
    /// an empty params means that the datatype is monomorphic.
    pub params: Vec<Str>,
    pub constructors: Vec<ConstructorDec<Str, So>>,
}

/// The definition of a datatype
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct DatatypeDef<Str, So> {
    /// Name of the datatype; sort
    ///
    /// Using this name as a sort might not be well-formed as a datatype could be n-ary.
    pub name: Str,
    /// The actual definition
    pub dec: DatatypeDec<Str, So>,
}

/// The definition of a function
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FunctionDef<Str, So, T> {
    /// Name of the function
    pub name: Str,
    /// Variables of the function
    pub vars: Vec<VarBinding<Str, So>>,
    /// The output sort of the function
    pub out_sort: So,
    /// The actual definition of the function
    pub body: T,
}

/// Represent all SMTLib commands
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Command<Str, So, T> {
    Assert(T),
    CheckSat,
    CheckSatAssuming(Vec<T>),
    DeclareConst(Str, So),
    DeclareDatatype(Str, DatatypeDec<Str, So>),
    DeclareDatatypes(Vec<DatatypeDef<Str, So>>),
    DeclareFun(Str, Vec<So>, So),
    DeclareSort(Str, usize),
    DefineConst(Str, So, T),
    DefineFun(FunctionDef<Str, So, T>),
    DefineFunRec(FunctionDef<Str, So, T>),
    DefineFunsRec(Vec<FunctionDef<Str, So, T>>),
    DefineSort(Str, Vec<Str>, So),
    Echo(Str),
    Exit,
    GetAssertions,
    GetAssignment,
    GetInfo(Keyword),
    GetModel,
    GetOption(Keyword),
    GetProof,
    GetUnsatAssumptions,
    GetUnsatCore,
    GetValue(Vec<T>),
    Pop(UBig),
    Push(UBig),
    Reset,
    ResetAssertions,
    SetInfo(Attribute<Str, T>),
    SetLogic(Str),
    SetOption(Attribute<Str, T>),
}

/// Implement this trait to specify how to quote a string representation
///
/// c.f. [SymbolQuote]
pub trait StrQuote<T: Display> {
    fn quote(&self) -> T;
}

impl StrQuote<String> for String {
    fn quote(&self) -> String {
        format!("\"{}\"", self.replace("\"", "\"\""))
    }
}

impl<T> StrQuote<String> for T
where
    T: Contains<T = String>,
{
    fn quote(&self) -> String {
        self.inner().quote()
    }
}

/// Implement this trait to specify how to quote a *symbol* representation
///
/// c.f. [StrQuote]
pub trait SymbolQuote<T: Display> {
    fn sym_quote(&self) -> T;
}

impl SymbolQuote<String> for String {
    fn sym_quote(&self) -> String {
        if SYMBOL_RE.is_match(self) && !SPECIAL_SYMBOLS.contains_key(self) {
            // in this case, we have a simple symbol, so we just return the same string back
            self.clone()
        } else {
            // in this case, we have some complex symbol. we assume that a valid symbol has no `|`,
            // so we simply return a quoted symbol.
            format!("|{}|", self)
        }
    }
}

impl<T> SymbolQuote<String> for T
where
    T: Contains<T = String>,
{
    fn sym_quote(&self) -> String {
        self.inner().sym_quote()
    }
}

pub(crate) fn fmt_vec(f: &mut impl Write, v: &[impl Display]) -> std::fmt::Result {
    for i in 0..v.len() {
        write!(f, "{}", v[i])?;
        if i != v.len() - 1 {
            write!(f, " ")?;
        }
    }
    Ok(())
}

pub(crate) fn fmt_vec_paren(f: &mut impl Write, v: &[impl Display]) -> std::fmt::Result {
    write!(f, "(")?;
    fmt_vec(f, v)?;
    write!(f, ")")
}

impl<Str: Display + StrQuote<String>> Display for Constant<Str> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Constant::Numeral(n) => write!(f, "{}", n),
            Constant::Decimal(r) => {
                if r.floor() == *r {
                    // need to hard code .0 if r doesn't have a decimal
                    write!(f, "{}.0", r)
                } else {
                    write!(f, "{}", r)
                }
            }
            Constant::String(s) => write!(f, "{}", s.quote()),
            Constant::Binary(bs, n) => write!(f, "#b{}", binary_to_string(bs, *n)),
            Constant::Hexadecimal(bs, n) => write!(f, "#x{}", hex_to_string(bs, *n)),
            Constant::Bool(b) => {
                if *b {
                    "true".fmt(f)
                } else {
                    "false".fmt(f)
                }
            }
        }
    }
}

impl<Str: SymbolQuote<String>> Display for Index<Str> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Index::Numeral(n) => write!(f, "{}", n),
            Index::Symbol(s) => write!(f, "{}", s.sym_quote()),
            Index::Hexadecimal(bs, n) => write!(f, "#x{}", hex_to_string(bs, *n)),
        }
    }
}

impl<Str: SymbolQuote<String>> Display for Identifier<Str> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.indices.is_empty() {
            write!(f, "{}", self.symbol.sym_quote())
        } else {
            write!(f, "(_ {} ", self.symbol.sym_quote())?;
            fmt_vec(f, &self.indices)?;
            write!(f, ")")
        }
    }
}

impl<Str, T> Display for Attribute<Str, T>
where
    Str: Display + StrQuote<String> + SymbolQuote<String>,
    T: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Attribute::Keyword(kw) => write!(f, "{}", kw),
            Attribute::Constant(kw, c) => write!(f, "{} {}", kw, c),
            Attribute::Symbol(kw, s) => write!(f, "{} {}", kw, s.sym_quote()),
            Attribute::Named(s) => write!(f, ":named {}", s.sym_quote()),
            Attribute::Pattern(ts) => {
                ":pattern ".fmt(f)?;
                fmt_vec_paren(f, ts)
            }
        }
    }
}

impl<Str, So> Display for Sort<Str, So>
where
    Str: SymbolQuote<String>,
    So: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.1.is_empty() {
            write!(f, "{}", self.0)
        } else {
            write!(f, "({} ", self.0)?;
            fmt_vec(f, &self.1)?;
            write!(f, ")")
        }
    }
}

impl<Str> Display for SigIndex<Str>
where
    Str: SymbolQuote<String>,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SigIndex::Numeral => "<NUMERAL>".fmt(f),
            SigIndex::Symbol(s) => s.sym_quote().fmt(f),
            SigIndex::Hexadecimal => "<HEXADECIMAL>".fmt(f),
        }
    }
}

impl Display for BvLenExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BvLenExpr::Fixed(n) => n.fmt(f),
            BvLenExpr::Var(n) => {
                "x".fmt(f)?;
                n.fmt(f)
            }
            BvLenExpr::Add { left, right } => fmt_app(f, "+", &[left, right]),
            BvLenExpr::Sub { left, right } => fmt_app(f, "-", &[left, right]),
            BvLenExpr::Mul { left, right } => fmt_app(f, "*", &[left, right]),
        }
    }
}

impl<So> Display for BvInSort<So>
where
    So: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BvInSort::BitVec(n) => {
                "(_ BitVec x".fmt(f)?;
                n.fmt(f)?;
                ")".fmt(f)
            }
            BvInSort::Sort(s) => s.fmt(f),
        }
    }
}

impl<So> Display for BvOutSort<So>
where
    So: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BvOutSort::BitVec(e) => {
                "(_ BitVec ".fmt(f)?;
                e.fmt(f)?;
                ")".fmt(f)
            }
            BvOutSort::Sort(s) => s.fmt(f),
        }
    }
}

impl<Str, So> Display for Sig<Str, So>
where
    Str: SymbolQuote<String>,
    So: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Sig::ParFunc(idx, pars, inps, o) => {
                if !idx.is_empty() {
                    write!(f, "(indices: ")?;
                    fmt_vec(f, idx)?;
                    write!(f, " ")?;
                }
                if !pars.is_empty() {
                    write!(f, "(par ")?;
                    fmt_vec_paren(f, &pars.iter().map(|s| s.sym_quote()).collect::<Vec<_>>())?;
                    write!(f, " ")?;
                }
                if !inps.is_empty() {
                    write!(f, "(=> ")?;
                    fmt_vec(f, inps)?;
                    write!(f, " {})", o)?;
                } else {
                    o.fmt(f)?;
                }
                if !pars.is_empty() {
                    write!(f, ")")?;
                }
                if !idx.is_empty() {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Sig::VarLenFunc(inp, n, out) => {
                write!(f, "(=> {} ...[>= {} times] {} {})", inp, n, inp, out)
            }
            Sig::BvFunc(n, _, _, inps, o) => {
                if *n != 0 {
                    write!(f, "(indices:")?;
                    for _ in 0..*n {
                        " <NUMERAL>".fmt(f)?;
                    }
                    write!(f, " ")?;
                }
                if !inps.is_empty() {
                    write!(f, "(=> ")?;
                    fmt_vec(f, inps)?;
                    write!(f, " {})", o)?;
                } else {
                    o.fmt(f)?;
                }
                if *n != 0 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Sig::BvVarLenFunc(_, inp, n, o) => {
                write!(f, "(=> {} ...[>= {} times] {} {})", inp, n, inp, o)
            }
            Sig::BvConcat => "(=> (_ BitVec l1) ... (_ BitVec ln) (_ BitVec (+ l1 ... ln)))".fmt(f),
        }
    }
}

impl<Str, So> Display for QualifiedIdentifier<Str, So>
where
    Str: SymbolQuote<String>,
    So: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.1 {
            None => write!(f, "{}", self.0),
            Some(s) => write!(f, "(as {} {})", self.0, s),
        }
    }
}

impl<Str, T> Display for VarBinding<Str, T>
where
    Str: SymbolQuote<String>,
    T: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} {})", self.0.sym_quote(), self.2)
    }
}

pub(crate) fn fmt_app(
    f: &mut impl Write,
    func: impl Display,
    args: &[impl Display],
) -> std::fmt::Result {
    write!(f, "({} ", func)?;
    fmt_vec(f, args)?;
    write!(f, ")")
}

/// This struct conveniently provides support for printing applications
pub(crate) struct AppFmt<'a, 'b, A, B> {
    func: &'a A,
    args: &'b [B],
}

impl<'a, 'b, A, B> AppFmt<'a, 'b, A, B> {
    pub fn new(func: &'a A, args: &'b [B]) -> Self {
        Self { func, args }
    }
}

impl<A, B> Display for AppFmt<'_, '_, A, B>
where
    A: Display,
    B: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        fmt_app(f, self.func, self.args)
    }
}

pub(crate) fn fmt_binder(
    f: &mut impl Write,
    binder: &str,
    vs: &[impl Display],
    body: &impl Display,
) -> std::fmt::Result {
    write!(f, "({} ", binder)?;
    fmt_vec_paren(f, vs)?;
    write!(f, " {})", body)
}

impl<Str> Display for Pattern<Str>
where
    Str: Display + SymbolQuote<String>,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Pattern::Wildcard(None) => "_".fmt(f),
            Pattern::Wildcard(Some((sym, _))) => sym.sym_quote().fmt(f),
            Pattern::Ctor(s) => s.sym_quote().fmt(f),
            Pattern::Applied { ctor, arguments } => {
                "(".fmt(f)?;
                ctor.sym_quote().fmt(f)?;
                for n in arguments {
                    match n {
                        None => {
                            " _".fmt(f)?;
                        }
                        Some((sym, _)) => {
                            " ".fmt(f)?;
                            sym.sym_quote().fmt(f)?;
                        }
                    }
                }
                ")".fmt(f)
            }
        }
    }
}
impl<Str, T> Display for PatternArm<Str, T>
where
    Str: Display + SymbolQuote<String>,
    T: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "(")?;
        self.pattern.fmt(f)?;
        write!(f, " {})", self.body)
    }
}

impl<Str, So, T> Display for Term<Str, So, T>
where
    Str: Display + StrQuote<String> + SymbolQuote<String>,
    So: Display,
    T: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Constant(c, _) => c.fmt(f),
            Term::Global(id, _) => id.fmt(f),
            Term::Local(id) => write!(f, "{}", id.symbol.sym_quote()),
            Term::App(id, args, _) => fmt_app(f, id, args),
            Term::Let(vs, body) => fmt_binder(f, "let", vs, body),
            Term::Annotated(t, at) => {
                write!(f, "(! {} ", t)?;
                fmt_vec(f, at)?;
                write!(f, ")")
            }
            Term::Eq(a, b) => fmt_app(f, "=", &[a, b]),
            Term::Distinct(ts) => fmt_app(f, "distinct", ts),
            Term::Exists(vs, t) => fmt_binder(f, "exists", vs, t),
            Term::Forall(vs, t) => fmt_binder(f, "forall", vs, t),
            Term::And(ts) => fmt_app(f, "and", ts),
            Term::Or(ts) => fmt_app(f, "or", ts),
            Term::Not(t) => fmt_app(f, "not", &[t]),
            Term::Implies(ts, r) => {
                write!(f, "(=> ")?;
                fmt_vec(f, ts)?;
                write!(f, " {})", r)
            }
            Term::Ite(b, t, e) => fmt_app(f, "ite", &[b, t, e]),
            Term::Matching(t, cs) => {
                write!(f, "(match {} ", t)?;
                fmt_vec_paren(f, cs)?;
                write!(f, ")")
            }
        }
    }
}

impl<Str, So, T> Display for FunctionDef<Str, So, T>
where
    Str: SymbolQuote<String>,
    So: Display,
    T: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ", self.name.sym_quote())?;
        fmt_vec_paren(f, &self.vars)?;
        write!(f, " {} {}", self.out_sort, self.body)
    }
}

impl<Str, So> Display for ConstructorDec<Str, So>
where
    Str: SymbolQuote<String>,
    So: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.args.is_empty() {
            write!(f, "({})", self.ctor.sym_quote())
        } else {
            fmt_app(f, self.ctor.sym_quote(), &self.args)
        }
    }
}

impl<Str, So> Display for DatatypeDec<Str, So>
where
    Str: SymbolQuote<String>,
    So: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if !self.params.is_empty() {
            write!(f, "(par ")?;
            fmt_vec_paren(
                f,
                &self
                    .params
                    .iter()
                    .map(|s| s.sym_quote())
                    .collect::<Vec<_>>(),
            )?;
            write!(f, " ")?;
        }
        fmt_vec_paren(f, &self.constructors)?;
        if !self.params.is_empty() {
            write!(f, ")")
        } else {
            Ok(())
        }
    }
}

impl<Str, So, T> Display for Command<Str, So, T>
where
    Str: Display + Clone + StrQuote<String> + SymbolQuote<String>,
    So: Display,
    T: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Command::Assert(t) => write!(f, "(assert {})", t),
            Command::CheckSat => write!(f, "(check-sat)"),
            Command::DeclareFun(id, ss, s) => {
                write!(f, "(declare-fun {} ", id.sym_quote())?;
                fmt_vec_paren(f, ss)?;
                write!(f, " {})", s)
            }
            Command::DefineFun(fd) => write!(f, "(define-fun {})", fd),
            Command::Exit => write!(f, "(exit)"),
            Command::GetAssertions => write!(f, "(get-assertions)"),
            Command::GetAssignment => write!(f, "(get-assignment)"),
            Command::GetModel => write!(f, "(get-model)"),
            Command::GetProof => write!(f, "(get-proof)"),
            Command::GetUnsatAssumptions => write!(f, "(get-unsat-assumptions)"),
            Command::GetUnsatCore => write!(f, "(get-unsat-core)"),
            Command::Pop(i) => write!(f, "(pop {})", i),
            Command::Push(i) => write!(f, "(push {})", i),
            Command::Reset => write!(f, "(reset)"),
            Command::ResetAssertions => write!(f, "(reset-assertions)"),
            Command::SetInfo(at) => write!(f, "(set-assertions {})", at),
            Command::SetLogic(l) => write!(f, "(set-logic {})", l),
            Command::SetOption(op) => write!(f, "(set-option {})", op),
            Command::DeclareConst(id, s) => write!(f, "(declare-const {} {})", id, s),
            Command::Echo(s) => write!(f, "(echo {})", s.quote()),
            Command::DeclareSort(id, arity) => write!(f, "(declare-sort {} {})", id, arity),
            Command::CheckSatAssuming(vs) => {
                write!(f, "(check-sat-assuming ")?;
                fmt_vec_paren(f, vs)?;
                write!(f, ")")
            }
            Command::DeclareDatatype(id, dec) => {
                write!(f, "(declare-datatype {} {})", id.sym_quote(), dec)
            }
            Command::DeclareDatatypes(defs) => {
                write!(f, "(declare-datatypes ")?;
                fmt_vec_paren(
                    f,
                    &defs
                        .iter()
                        .map(|d| VarBinding(d.name.clone(), 0, d.dec.params.len()))
                        .collect::<Vec<_>>(),
                )?;
                write!(f, " ")?;
                fmt_vec_paren(f, &defs.iter().map(|d| &d.dec).collect::<Vec<_>>())?;
                write!(f, ")")
            }
            Command::DefineConst(sym, sort, term) => {
                write!(f, "(define-const {} {} {})", sym.sym_quote(), sort, term)
            }
            Command::DefineFunRec(fd) => write!(f, "(define-fun-rec {})", fd),
            Command::DefineFunsRec(fds) => {
                write!(f, "(define-funs-rec (")?;
                for (i, fd) in fds.iter().enumerate() {
                    write!(f, "({} ", fd.name.sym_quote())?;
                    fmt_vec_paren(f, &fd.vars)?;
                    write!(f, " {})", fd.out_sort)?;
                    if i != fds.len() - 1 {
                        write!(f, " ")?;
                    }
                }
                fmt_vec_paren(f, &fds.iter().map(|d| &d.body).collect::<Vec<_>>())?;
                write!(f, ")")
            }
            Command::DefineSort(name, params, sort) => {
                write!(f, "(define-sort {} ", name.sym_quote())?;
                fmt_vec_paren(f, &params.iter().map(|s| s.sym_quote()).collect::<Vec<_>>())?;
                write!(f, " {})", sort)
            }
            Command::GetValue(ts) => {
                write!(f, "(get-value ")?;
                fmt_vec_paren(f, ts)?;
                write!(f, ")")
            }
            Command::GetInfo(kw) => {
                write!(f, "(get-info {})", kw)
            }
            Command::GetOption(kw) => {
                write!(f, "(get-option {})", kw)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    type Pat = Pattern<String>;

    #[test]
    fn test_pattern() {
        assert!(Pat::Wildcard(None).variables().is_empty());
        assert_eq!(Pat::Wildcard(Some(("x".into(), 0))).variables(), vec!["x"]);
        assert!(Pat::Ctor("x".into()).variables().is_empty());
        assert_eq!(
            Pat::Applied {
                ctor: "foobar".into(),
                arguments: vec![Some(("x".into(), 0)), None, Some(("y".into(), 0))],
            }
            .variables(),
            vec!["x", "y"]
        )
    }
}
