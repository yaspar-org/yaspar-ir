// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Translation from yaspar-ir typed ASTs to cvc5-rs `Sort` and `Term`.
//!
//! The entry point is [`Cvc5Env`], which wraps a [`cvc5_rs::TermManager`] reference and a
//! [`Context`] reference, and provides [`translate_sort`](Cvc5Env::translate_sort) and
//! [`translate_term`](Cvc5Env::translate_term).

use crate::ast::*;
use crate::raw::alg;
use crate::raw::alg::CheckIdentifier;
use crate::statics;
use crate::traits::{Contains, Repr};
use cvc5_rs::{Kind, TermManager};
use std::collections::HashMap;
use yaspar::{binary_to_string, hex_to_string};

type CSort = cvc5_rs::Sort;
type CTerm = cvc5_rs::Term;
type Res<T> = std::result::Result<T, std::string::String>;

/// Environment for translating yaspar-ir ASTs to cvc5-rs objects.
pub struct Cvc5Env<'a> {
    pub tm: &'a TermManager,
    pub ctx: &'a mut Context,
    sort_cache: HashMap<std::string::String, CSort>,
    globals: HashMap<std::string::String, CTerm>,
    locals: HashMap<usize, CTerm>,
}

impl<'a> Cvc5Env<'a> {
    pub fn new(tm: &'a TermManager, ctx: &'a mut Context) -> Self {
        Self {
            tm,
            ctx,
            sort_cache: HashMap::new(),
            globals: HashMap::new(),
            locals: HashMap::new(),
        }
    }

    /// Register a global symbol that has already been created in cvc5.
    pub fn register_global(&mut self, name: &str, term: CTerm) {
        self.globals.insert(name.to_string(), term);
    }
}

// ── Sort translation ─────────────────────────────────────────
impl Cvc5Env<'_> {
    /// Translate a yaspar-ir `Sort` to a cvc5-rs `Sort`.
    pub fn translate_sort(&mut self, sort: &Sort) -> Res<CSort> {
        let s = sort.repr();
        let name = s.sort_name().inner().as_str();
        if let Some(n) = s.is_bv() {
            let w: u32 = n
                .clone()
                .try_into()
                .map_err(|_| format!("bv width too large: {n}"))?;
            return Ok(self.tm.mk_bv_sort(w));
        }
        if s.1.is_empty() {
            if name == statics::BOOL {
                return Ok(self.tm.boolean_sort());
            }
            if name == statics::INT {
                return Ok(self.tm.integer_sort());
            }
            if name == statics::REAL {
                return Ok(self.tm.real_sort());
            }
            if name == statics::STRING {
                return Ok(self.tm.string_sort());
            }
            if name == statics::REGLAN {
                return Ok(self.tm.regexp_sort());
            }
        }
        if name == statics::ARRAY {
            if let [idx, elem] = s.1.as_slice() {
                let ci = self.translate_sort(idx)?;
                let ce = self.translate_sort(elem)?;
                return Ok(self.tm.mk_array_sort(ci, ce));
            }
        }
        if let Some(cs) = self.sort_cache.get(name) {
            return Ok(cs.clone());
        }
        Err(format!("unsupported sort: {sort}"))
    }
}

// ── Identifier kind → cvc5 Kind mapping ─────────────────────
fn ident_kind_to_cvc5(k: &alg::IdentifierKind<Str>) -> Option<Kind> {
    use alg::IdentifierKind::*;
    Some(match k {
        Add => Kind::CVC5_KIND_ADD,
        Sub => Kind::CVC5_KIND_SUB,
        Mul => Kind::CVC5_KIND_MULT,
        Idiv => Kind::CVC5_KIND_INTS_DIVISION,
        Rdiv => Kind::CVC5_KIND_DIVISION,
        Mod => Kind::CVC5_KIND_INTS_MODULUS,
        Abs => Kind::CVC5_KIND_ABS,
        Le => Kind::CVC5_KIND_LEQ,
        Lt => Kind::CVC5_KIND_LT,
        Ge => Kind::CVC5_KIND_GEQ,
        Gt => Kind::CVC5_KIND_GT,
        ToReal => Kind::CVC5_KIND_TO_REAL,
        ToInt => Kind::CVC5_KIND_TO_INTEGER,
        IsInt => Kind::CVC5_KIND_IS_INTEGER,
        Select => Kind::CVC5_KIND_SELECT,
        Store => Kind::CVC5_KIND_STORE,
        StrConcat => Kind::CVC5_KIND_STRING_CONCAT,
        StrLen => Kind::CVC5_KIND_STRING_LENGTH,
        StrLt => Kind::CVC5_KIND_STRING_LT,
        StrLe => Kind::CVC5_KIND_STRING_LEQ,
        StrAt => Kind::CVC5_KIND_STRING_CHARAT,
        StrSubstr => Kind::CVC5_KIND_STRING_SUBSTR,
        StrPrefixof => Kind::CVC5_KIND_STRING_PREFIX,
        StrSuffixof => Kind::CVC5_KIND_STRING_SUFFIX,
        StrContains => Kind::CVC5_KIND_STRING_CONTAINS,
        StrIndexof => Kind::CVC5_KIND_STRING_INDEXOF,
        StrReplace => Kind::CVC5_KIND_STRING_REPLACE,
        StrReplaceAll => Kind::CVC5_KIND_STRING_REPLACE_ALL,
        StrReplaceRe => Kind::CVC5_KIND_STRING_REPLACE_RE,
        StrReplaceReAll => Kind::CVC5_KIND_STRING_REPLACE_RE_ALL,
        StrToRe => Kind::CVC5_KIND_STRING_TO_REGEXP,
        StrInRe => Kind::CVC5_KIND_STRING_IN_REGEXP,
        StrIsDigit => Kind::CVC5_KIND_STRING_IS_DIGIT,
        StrToCode => Kind::CVC5_KIND_STRING_TO_CODE,
        StrFromCode => Kind::CVC5_KIND_STRING_FROM_CODE,
        StrToInt => Kind::CVC5_KIND_STRING_TO_INT,
        StrFromInt => Kind::CVC5_KIND_STRING_FROM_INT,
        ReNone => Kind::CVC5_KIND_REGEXP_NONE,
        ReAll => Kind::CVC5_KIND_REGEXP_ALL,
        ReAllChar => Kind::CVC5_KIND_REGEXP_ALLCHAR,
        ReConcat => Kind::CVC5_KIND_REGEXP_CONCAT,
        ReUnion => Kind::CVC5_KIND_REGEXP_UNION,
        ReInter => Kind::CVC5_KIND_REGEXP_INTER,
        ReStar => Kind::CVC5_KIND_REGEXP_STAR,
        ReComp => Kind::CVC5_KIND_REGEXP_COMPLEMENT,
        ReDiff => Kind::CVC5_KIND_REGEXP_DIFF,
        ReAdd => Kind::CVC5_KIND_REGEXP_PLUS,
        ReOpt => Kind::CVC5_KIND_REGEXP_OPT,
        ReRange => Kind::CVC5_KIND_REGEXP_RANGE,
        Concat => Kind::CVC5_KIND_BITVECTOR_CONCAT,
        BvNot => Kind::CVC5_KIND_BITVECTOR_NOT,
        BvNeg => Kind::CVC5_KIND_BITVECTOR_NEG,
        BvAnd => Kind::CVC5_KIND_BITVECTOR_AND,
        BvOr => Kind::CVC5_KIND_BITVECTOR_OR,
        BvAdd => Kind::CVC5_KIND_BITVECTOR_ADD,
        BvMul => Kind::CVC5_KIND_BITVECTOR_MULT,
        BvUdiv => Kind::CVC5_KIND_BITVECTOR_UDIV,
        BvUrem => Kind::CVC5_KIND_BITVECTOR_UREM,
        BvShl => Kind::CVC5_KIND_BITVECTOR_SHL,
        BvLshr => Kind::CVC5_KIND_BITVECTOR_LSHR,
        BvUlt => Kind::CVC5_KIND_BITVECTOR_ULT,
        BvNand => Kind::CVC5_KIND_BITVECTOR_NAND,
        BvNor => Kind::CVC5_KIND_BITVECTOR_NOR,
        BvXor => Kind::CVC5_KIND_BITVECTOR_XOR,
        BvNxor => Kind::CVC5_KIND_BITVECTOR_XNOR,
        BvComp => Kind::CVC5_KIND_BITVECTOR_COMP,
        BvSub => Kind::CVC5_KIND_BITVECTOR_SUB,
        BvSdiv => Kind::CVC5_KIND_BITVECTOR_SDIV,
        BvSrem => Kind::CVC5_KIND_BITVECTOR_SREM,
        BvSmod => Kind::CVC5_KIND_BITVECTOR_SMOD,
        BvAShr => Kind::CVC5_KIND_BITVECTOR_ASHR,
        BvUle => Kind::CVC5_KIND_BITVECTOR_ULE,
        BvUgt => Kind::CVC5_KIND_BITVECTOR_UGT,
        BvUge => Kind::CVC5_KIND_BITVECTOR_UGE,
        BvSlt => Kind::CVC5_KIND_BITVECTOR_SLT,
        BvSle => Kind::CVC5_KIND_BITVECTOR_SLE,
        BvSgt => Kind::CVC5_KIND_BITVECTOR_SGT,
        BvSge => Kind::CVC5_KIND_BITVECTOR_SGE,
        BvNego => Kind::CVC5_KIND_BITVECTOR_NEGO,
        BvUaddo => Kind::CVC5_KIND_BITVECTOR_UADDO,
        BvSaddo => Kind::CVC5_KIND_BITVECTOR_SADDO,
        BvUmulo => Kind::CVC5_KIND_BITVECTOR_UMULO,
        BvSmulo => Kind::CVC5_KIND_BITVECTOR_SMULO,
        UbvToInt => Kind::CVC5_KIND_BITVECTOR_UBV_TO_INT,
        SbvToInt => Kind::CVC5_KIND_BITVECTOR_SBV_TO_INT,
        Bv2Nat => Kind::CVC5_KIND_BITVECTOR_UBV_TO_INT,
        Bv2Int => Kind::CVC5_KIND_BITVECTOR_UBV_TO_INT,
        BvUsubo => Kind::CVC5_KIND_BITVECTOR_USUBO,
        BvSsubo => Kind::CVC5_KIND_BITVECTOR_SSUBO,
        BvSdivo => Kind::CVC5_KIND_BITVECTOR_SDIVO,
        _ => return None,
    })
}

// ── Term translation ─────────────────────────────────────────
impl Cvc5Env<'_> {
    /// Translate a slice of terms.
    pub fn translate_terms(&mut self, ts: &[Term]) -> Res<Vec<CTerm>> {
        ts.iter().map(|t| self.translate_term(t)).collect()
    }

    /// Translate a yaspar-ir `Term` to a cvc5-rs `Term`.
    pub fn translate_term(&mut self, term: &Term) -> Res<CTerm> {
        use alg::Term as AT;
        match term.repr() {
            AT::Constant(c, _) => self.translate_constant(c),
            AT::Global(qid, _) => self.translate_global(qid),
            AT::Local(loc) => self
                .locals
                .get(&loc.id)
                .cloned()
                .ok_or_else(|| format!("unbound local: {}", loc.symbol)),
            AT::Not(t) => Ok(self
                .tm
                .mk_term(Kind::CVC5_KIND_NOT, &[self.translate_term(t)?])),
            AT::Eq(a, b) => {
                let (ca, cb) = (self.translate_term(a)?, self.translate_term(b)?);
                Ok(self.tm.mk_term(Kind::CVC5_KIND_EQUAL, &[ca, cb]))
            }
            AT::Distinct(ts) => Ok(self
                .tm
                .mk_term(Kind::CVC5_KIND_DISTINCT, &self.translate_terms(ts)?)),
            AT::And(ts) => Ok(self
                .tm
                .mk_term(Kind::CVC5_KIND_AND, &self.translate_terms(ts)?)),
            AT::Or(ts) => Ok(self
                .tm
                .mk_term(Kind::CVC5_KIND_OR, &self.translate_terms(ts)?)),
            AT::Xor(ts) => {
                let cts = self.translate_terms(ts)?;
                let mut r = cts[0].clone();
                for c in &cts[1..] {
                    r = self.tm.mk_term(Kind::CVC5_KIND_XOR, &[r, CTerm::clone(c)]);
                }
                Ok(r)
            }
            AT::Implies(premises, concl) => {
                let mut all = self.translate_terms(premises)?;
                all.push(self.translate_term(concl)?);
                Ok(self.tm.mk_term(Kind::CVC5_KIND_IMPLIES, &all))
            }
            AT::Ite(c, t, e) => {
                let (cc, ct, ce) = (
                    self.translate_term(c)?,
                    self.translate_term(t)?,
                    self.translate_term(e)?,
                );
                Ok(self.tm.mk_term(Kind::CVC5_KIND_ITE, &[cc, ct, ce]))
            }
            AT::Forall(vars, body) => self.translate_quantifier(Kind::CVC5_KIND_FORALL, vars, body),
            AT::Exists(vars, body) => self.translate_quantifier(Kind::CVC5_KIND_EXISTS, vars, body),
            AT::Let(bindings, body) => self.translate_let(bindings, body),
            AT::App(qid, args, _) => self.translate_app(qid, args),
            AT::Annotated(t, _) => self.translate_term(t),
            AT::Matching(_, _) => {
                Err("match expressions not yet supported in cvc5 translation".into())
            }
        }
    }

    fn translate_constant(&self, c: &alg::Constant<Str>) -> Res<CTerm> {
        use alg::Constant::*;
        match c {
            Bool(true) => Ok(self.tm.mk_true()),
            Bool(false) => Ok(self.tm.mk_false()),
            Numeral(n) => Ok(self.tm.mk_integer_from_str(&n.to_string())),
            Decimal(d) => Ok(self.tm.mk_real_from_str(&d.to_string())),
            String(s) => Ok(self.tm.mk_string(&s, false)),
            Binary(bytes, len) => {
                let bits = binary_to_string(bytes, *len);
                Ok(self.tm.mk_bv_from_str(*len as u32, &bits, 2))
            }
            Hexadecimal(bytes, len) => {
                let hex = hex_to_string(bytes, *len);
                Ok(self.tm.mk_bv_from_str((*len * 4) as u32, &hex, 16))
            }
        }
    }

    fn translate_global(&self, qid: &QualifiedIdentifier) -> Res<CTerm> {
        use alg::IdentifierKind::*;
        let name = qid.id_str().inner();
        match qid.get_kind() {
            Some(Char(hex, _)) => Ok(self.tm.mk_string(&String::from_utf8_lossy(&hex), false)),
            _ => self
                .globals
                .get(name.as_str())
                .cloned()
                .ok_or_else(|| format!("unknown global symbol: {name}")),
        }
    }

    fn translate_quantifier(
        &mut self,
        kind: Kind,
        vars: &[alg::VarBinding<Str, Sort>],
        body: &Term,
    ) -> Res<CTerm> {
        let mut bound = Vec::with_capacity(vars.len());
        for v in vars {
            let cs = self.translate_sort(&v.2)?;
            let bv = self.tm.mk_var(cs, &v.0);
            self.locals.insert(v.1, bv.clone());
            bound.push(bv);
        }
        let bvl = self.tm.mk_term(Kind::CVC5_KIND_VARIABLE_LIST, &bound);
        let cbody = self.translate_term(body)?;
        for v in vars {
            self.locals.remove(&v.1);
        }
        Ok(self.tm.mk_term(kind, &[bvl, cbody]))
    }

    fn translate_let(
        &mut self,
        bindings: &[alg::VarBinding<Str, Term>],
        body: &Term,
    ) -> Res<CTerm> {
        for b in bindings {
            let ct = self.translate_term(&b.2)?;
            self.locals.insert(b.1, ct);
        }
        let result = self.translate_term(body);
        for b in bindings {
            self.locals.remove(&b.1);
        }
        result
    }

    fn translate_app(&mut self, qid: &QualifiedIdentifier, args: &[Term]) -> Res<CTerm> {
        let cargs = self.translate_terms(args)?;
        let id = &qid.0;
        let kind = id.get_kind();
        // Handle unary minus: (- x) → NEG
        if let Some(alg::IdentifierKind::Sub) = kind {
            if cargs.len() == 1 {
                return Ok(self.tm.mk_term(Kind::CVC5_KIND_NEG, &cargs));
            }
        }
        if let Some(kind) = kind.as_ref().and_then(ident_kind_to_cvc5) {
            return Ok(self.tm.mk_term(kind, &cargs));
        }
        if let Some(ref ik) = kind {
            return self.translate_indexed_app(ik, &cargs);
        }
        let name = id.symbol.inner();
        let f = self
            .globals
            .get(name.as_str())
            .cloned()
            .ok_or_else(|| format!("unknown function: {name}"))?;
        let mut all = vec![f];
        all.extend(cargs);
        Ok(self.tm.mk_term(Kind::CVC5_KIND_APPLY_UF, &all))
    }

    fn translate_indexed_app(&self, ik: &IdentifierKind, cargs: &[CTerm]) -> Res<CTerm> {
        use alg::IdentifierKind::*;
        let mk = |kind, indices: &[u32]| {
            let op = self.tm.mk_op(kind, indices);
            Ok(self.tm.mk_term_from_op(op, cargs))
        };
        let to_u32 = |n: &dashu::integer::UBig| -> Res<u32> {
            n.try_into().map_err(|_| format!("index too large: {n}"))
        };
        match ik {
            Extract(hi, lo) => mk(
                Kind::CVC5_KIND_BITVECTOR_EXTRACT,
                &[to_u32(hi)?, to_u32(lo)?],
            ),
            Repeat(n) => mk(Kind::CVC5_KIND_BITVECTOR_REPEAT, &[to_u32(n)?]),
            ZeroExtend(n) => mk(Kind::CVC5_KIND_BITVECTOR_ZERO_EXTEND, &[to_u32(n)?]),
            SignExtend(n) => mk(Kind::CVC5_KIND_BITVECTOR_SIGN_EXTEND, &[to_u32(n)?]),
            RotateLeft(n) => mk(Kind::CVC5_KIND_BITVECTOR_ROTATE_LEFT, &[to_u32(n)?]),
            RotateRight(n) => mk(Kind::CVC5_KIND_BITVECTOR_ROTATE_RIGHT, &[to_u32(n)?]),
            IntToBv(n) | Int2Bv(n) | Nat2Bv(n) => {
                mk(Kind::CVC5_KIND_INT_TO_BITVECTOR, &[to_u32(n)?])
            }
            RePower(n) => mk(Kind::CVC5_KIND_REGEXP_REPEAT, &[to_u32(n)?]),
            ReLoop(lo, hi) => mk(Kind::CVC5_KIND_REGEXP_LOOP, &[to_u32(lo)?, to_u32(hi)?]),
            Is(cname) => {
                let op = self
                    .tm
                    .mk_op_from_str(Kind::CVC5_KIND_APPLY_TESTER, cname.inner().as_str());
                Ok(self.tm.mk_term_from_op(op, cargs))
            }
            _ => Err(format!("unsupported indexed operator: {:?}", ik)),
        }
    }
}

// ── Command translation ──────────────────────────────────────
impl Cvc5Env<'_> {
    /// Process a typed command, updating the cvc5 solver state.
    ///
    /// Returns the cvc5 term for `Assert` commands, or `None` for others.
    pub fn translate_command(
        &mut self,
        solver: &mut cvc5_rs::Solver,
        cmd: &Command,
    ) -> Res<Option<CTerm>> {
        use alg::Command as AC;
        match cmd.inner().repr() {
            AC::SetLogic(l) => {
                solver.set_logic(&l);
                Ok(None)
            }
            AC::DeclareConst(name, sort) => {
                let cs = self.translate_sort(sort)?;
                let ct = self.tm.mk_const(cs, &name);
                self.globals.insert(name.inner().clone(), ct);
                Ok(None)
            }
            AC::DeclareFun(name, inp, out) => {
                let co = self.translate_sort(out)?;
                if inp.is_empty() {
                    let ct = self.tm.mk_const(co, &name);
                    self.globals.insert(name.inner().clone(), ct);
                } else {
                    let ci: Vec<CSort> = inp
                        .iter()
                        .map(|s| self.translate_sort(s))
                        .collect::<Res<_>>()?;
                    let fs = self.tm.mk_fun_sort(&ci, co);
                    let ct = self.tm.mk_const(fs, &name);
                    self.globals.insert(name.inner().clone(), ct);
                }
                Ok(None)
            }
            AC::DeclareSort(name, arity) => {
                if arity != &0 {
                    return Err(format!(
                        "parametric uninterpreted sorts not supported: {name}"
                    ));
                }
                let cs = self.tm.mk_uninterpreted_sort(&name);
                self.sort_cache.insert(name.inner().clone(), cs);
                Ok(None)
            }
            AC::Assert(t) => {
                let ct = self.translate_term(t)?;
                solver.assert_formula(CTerm::clone(&ct));
                Ok(Some(ct))
            }
            AC::CheckSat => {
                let _ = solver.check_sat();
                Ok(None)
            }
            AC::Push(n) => {
                let n: u32 = n
                    .try_into()
                    .map_err(|_| "push level too large".to_string())?;
                solver.push(n);
                Ok(None)
            }
            AC::Pop(n) => {
                let n: u32 = n
                    .try_into()
                    .map_err(|_| "pop level too large".to_string())?;
                solver.pop(n);
                Ok(None)
            }
            _ => Ok(None),
        }
    }
}
