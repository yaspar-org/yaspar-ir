// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Translation from yaspar-ir typed ASTs to cvc5-rs `Sort` and `Term`.
//!
//! The entry point is [`Cvc5Env`], which wraps a [`cvc5_rs::TermManager`] reference and a
//! [`Context`] reference. The [`ConvertToCvc5`] trait provides `to_cvc5` for [`Sort`] and
//! [`Term`].

use crate::ast::*;
use crate::raw::alg;
use crate::raw::alg::CheckIdentifier;
use crate::statics;
use crate::traits::{Contains, Repr};
use cvc5_rs::{Kind, TermManager};
use std::borrow::Borrow;
use std::collections::HashMap;
use yaspar::{binary_to_string, hex_to_string};

type CSort = cvc5_rs::Sort;
type CTerm = cvc5_rs::Term;
type Res<T> = std::result::Result<T, String>;

/// Convert a yaspar-ir typed AST node to its cvc5-rs counterpart.
pub trait ConvertToCvc5<Env> {
    type Output;
    fn to_cvc5(&self, env: &mut Env) -> Res<Self::Output>;
}

/// Environment for translating yaspar-ir ASTs to cvc5-rs objects.
pub struct Cvc5Env {
    tm: TermManager,
    sort: HashMap<String, CSort>,
    globals: HashMap<String, CTerm>,
    locals: HashMap<usize, CTerm>,
    sort_cache: HashMap<Sort, CSort>,
    term_cache: HashMap<Term, CTerm>,
}

impl Cvc5Env {
    pub fn new(tm: impl Borrow<TermManager>) -> Self {
        Self {
            tm: tm.borrow().clone(),
            sort: HashMap::new(),
            globals: HashMap::new(),
            locals: HashMap::new(),
            sort_cache: HashMap::new(),
            term_cache: HashMap::new(),
        }
    }

    /// Register a global symbol that has already been created in cvc5.
    pub fn register_global(&mut self, name: &str, term: CTerm) {
        self.globals.insert(name.to_string(), term);
    }
}

// ── Sort translation ─────────────────────────────────────────
impl ConvertToCvc5<Cvc5Env> for Sort {
    type Output = CSort;

    fn to_cvc5(&self, env: &mut Cvc5Env) -> Res<CSort> {
        if let Some(cs) = env.sort_cache.get(self) {
            return Ok(cs.clone());
        }
        let cs = translate_sort_inner(self, env)?;
        env.sort_cache.insert(self.clone(), cs.clone());
        Ok(cs)
    }
}

fn translate_sort_inner(sort: &Sort, env: &mut Cvc5Env) -> Res<CSort> {
    let s = sort.repr();
    let name = s.sort_name().inner().as_str();
    if let Some(n) = s.is_bv() {
        let w: u32 = n
            .clone()
            .try_into()
            .map_err(|_| format!("bv width too large: {n}"))?;
        return Ok(env.tm.mk_bv_sort(w));
    }
    if s.1.is_empty() {
        if name == statics::BOOL {
            return Ok(env.tm.boolean_sort());
        }
        if name == statics::INT {
            return Ok(env.tm.integer_sort());
        }
        if name == statics::REAL {
            return Ok(env.tm.real_sort());
        }
        if name == statics::STRING {
            return Ok(env.tm.string_sort());
        }
        if name == statics::REGLAN {
            return Ok(env.tm.regexp_sort());
        }
    }
    if name == statics::ARRAY
        && let [idx, elem] = s.1.as_slice()
    {
        let ci = idx.to_cvc5(env)?;
        let ce = elem.to_cvc5(env)?;
        return Ok(env.tm.mk_array_sort(ci, ce));
    }
    if let Some(cs) = env.sort.get(name) {
        return Ok(cs.clone());
    }
    Err(format!("unsupported sort: {sort}"))
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
        Bv2Nat => Kind::CVC5_KIND_BITVECTOR_SBV_TO_INT,
        Bv2Int => Kind::CVC5_KIND_BITVECTOR_SBV_TO_INT,
        BvUsubo => Kind::CVC5_KIND_BITVECTOR_USUBO,
        BvSsubo => Kind::CVC5_KIND_BITVECTOR_SSUBO,
        BvSdivo => Kind::CVC5_KIND_BITVECTOR_SDIVO,
        _ => return None,
    })
}

// ── Term translation ─────────────────────────────────────────
impl ConvertToCvc5<Cvc5Env> for Term {
    type Output = CTerm;

    fn to_cvc5(&self, env: &mut Cvc5Env) -> Res<CTerm> {
        if let Some(ct) = env.term_cache.get(self) {
            return Ok(ct.clone());
        }
        let ct = translate_term_inner(self, env)?;
        env.term_cache.insert(self.clone(), ct.clone());
        Ok(ct)
    }
}

fn translate_term_inner(term: &Term, env: &mut Cvc5Env) -> Res<CTerm> {
    use alg::Term as AT;
    match term.repr() {
        AT::Constant(c, _) => env.translate_constant(c),
        AT::Global(qid, _) => env.translate_global(qid),
        AT::Local(loc) => env
            .locals
            .get(&loc.id)
            .cloned()
            .ok_or_else(|| format!("unbound local: {}", loc.symbol)),
        AT::Not(t) => {
            let nt = t.to_cvc5(env)?;
            Ok(env.tm.mk_term(Kind::CVC5_KIND_NOT, &[nt]))
        }
        AT::Eq(a, b) => {
            let (ca, cb) = (a.to_cvc5(env)?, b.to_cvc5(env)?);
            Ok(env.tm.mk_term(Kind::CVC5_KIND_EQUAL, &[ca, cb]))
        }
        AT::Distinct(ts) => {
            let cts = env.translate_terms(ts)?;
            Ok(env.tm.mk_term(Kind::CVC5_KIND_DISTINCT, &cts))
        }
        AT::And(ts) => {
            let cts = env.translate_terms(ts)?;
            Ok(env.tm.mk_term(Kind::CVC5_KIND_AND, &cts))
        }
        AT::Or(ts) => {
            let cts = env.translate_terms(ts)?;
            Ok(env.tm.mk_term(Kind::CVC5_KIND_OR, &cts))
        }
        AT::Xor(ts) => {
            let cts = env.translate_terms(ts)?;
            let mut r = cts[0].clone();
            for c in &cts[1..] {
                r = env.tm.mk_term(Kind::CVC5_KIND_XOR, &[r, CTerm::clone(c)]);
            }
            Ok(r)
        }
        AT::Implies(premises, concl) => {
            let mut all = env.translate_terms(premises)?;
            all.push(concl.to_cvc5(env)?);
            Ok(env.tm.mk_term(Kind::CVC5_KIND_IMPLIES, &all))
        }
        AT::Ite(c, t, e) => {
            let (cc, ct, ce) = (c.to_cvc5(env)?, t.to_cvc5(env)?, e.to_cvc5(env)?);
            Ok(env.tm.mk_term(Kind::CVC5_KIND_ITE, &[cc, ct, ce]))
        }
        AT::Forall(vars, body) => env.translate_quantifier(Kind::CVC5_KIND_FORALL, vars, body),
        AT::Exists(vars, body) => env.translate_quantifier(Kind::CVC5_KIND_EXISTS, vars, body),
        AT::Let(bindings, body) => env.translate_let(bindings, body),
        AT::App(qid, args, _) => env.translate_app(qid, args),
        AT::Annotated(t, _) => {
            // wild annotations are ignored
            t.to_cvc5(env)
        }
        AT::Matching(_, _) => Err("match expressions not yet supported in cvc5 translation".into()),
    }
}

impl ConvertToCvc5<Cvc5Env> for [Term] {
    type Output = Vec<CTerm>;

    fn to_cvc5(&self, env: &mut Cvc5Env) -> Res<Vec<CTerm>> {
        self.iter().map(|t| t.to_cvc5(env)).collect()
    }
}

impl Cvc5Env {
    fn translate_terms(&mut self, ts: &[Term]) -> Res<Vec<CTerm>> {
        ts.to_cvc5(self)
    }

    fn translate_constant(&self, c: &Constant) -> Res<CTerm> {
        use alg::Constant::*;
        match c {
            Bool(true) => Ok(self.tm.mk_true()),
            Bool(false) => Ok(self.tm.mk_false()),
            Numeral(n) => Ok(self.tm.mk_integer_from_str(&n.to_string())),
            Decimal(d) => Ok(self.tm.mk_real_from_str(&d.to_string())),
            String(s) => Ok(self.tm.mk_string(s, false)),
            Binary(bytes, len) => {
                let bits = binary_to_string(bytes, *len);
                let w: u32 = (*len)
                    .try_into()
                    .map_err(|_| format!("binary literal width too large: {len}"))?;
                Ok(self.tm.mk_bv_from_str(w, &bits, 2))
            }
            Hexadecimal(bytes, len) => {
                let hex = hex_to_string(bytes, *len);
                let w: u32 = len
                    .checked_mul(4)
                    .and_then(|n| n.try_into().ok())
                    .ok_or_else(|| format!("hex literal width too large: {len}"))?;
                Ok(self.tm.mk_bv_from_str(w, &hex, 16))
            }
        }
    }

    fn translate_global(&self, qid: &QualifiedIdentifier) -> Res<CTerm> {
        use alg::IdentifierKind::*;
        let name = qid.id_str().inner();
        match qid.get_kind() {
            Some(Char(hex, _)) => Ok(self.tm.mk_string(
                &String::from_utf8(hex).map_err(|err| {
                    format!("symbol {qid} cannot be converted to a String: {err}")
                })?,
                false,
            )),
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
            let cs = v.2.to_cvc5(self)?;
            let bv = self.tm.mk_var(cs, &v.0);
            self.locals.insert(v.1, bv.clone());
            bound.push(bv);
        }
        let result = self.translate_quantifier_body(kind, body, &bound);
        for v in vars {
            self.locals.remove(&v.1);
        }
        result
    }

    fn translate_quantifier_body(
        &mut self,
        kind: Kind,
        body: &Term,
        bound: &[CTerm],
    ) -> Res<CTerm> {
        let bvl = self.tm.mk_term(Kind::CVC5_KIND_VARIABLE_LIST, bound);

        // Peel off annotations from the body to extract :pattern triggers
        let (inner_body, attrs) = match body.repr() {
            ATerm::Annotated(t, attrs) => (t, Some(attrs)),
            _ => (body, None),
        };
        let cbody = inner_body.to_cvc5(self)?;

        // Build INST_PATTERN_LIST from :pattern annotations
        if let Some(attrs) = attrs {
            let mut pats = Vec::new();
            for attr in attrs {
                if let Attribute::Pattern(terms) = attr {
                    let cterms = self.translate_terms(terms)?;
                    pats.push(self.tm.mk_term(Kind::CVC5_KIND_INST_PATTERN, &cterms));
                }
            }
            if !pats.is_empty() {
                let plist = self.tm.mk_term(Kind::CVC5_KIND_INST_PATTERN_LIST, &pats);
                return Ok(self.tm.mk_term(kind, &[bvl, cbody, plist]));
            }
        }

        Ok(self.tm.mk_term(kind, &[bvl, cbody]))
    }

    fn translate_let(
        &mut self,
        bindings: &[alg::VarBinding<Str, Term>],
        body: &Term,
    ) -> Res<CTerm> {
        let new_bindings = bindings
            .iter()
            .map(|b| Ok((b.1, b.2.to_cvc5(self)?)))
            .collect::<Res<Vec<_>>>()?;
        for b in new_bindings {
            self.locals.insert(b.0, b.1);
        }
        let result = body.to_cvc5(self);
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
        if let Some(alg::IdentifierKind::Sub) = kind
            && cargs.len() == 1
        {
            return Ok(self.tm.mk_term(Kind::CVC5_KIND_NEG, &cargs));
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
impl Cvc5Env {
    /// Process a typed command, updating the cvc5 solver state.
    pub fn translate_command(&mut self, solver: &mut cvc5_rs::Solver, cmd: &Command) -> Res<()> {
        use alg::Command as AC;
        match cmd.inner().repr() {
            AC::SetLogic(l) => {
                solver.set_logic(l);
                Ok(())
            }
            AC::SetInfo(attr) => {
                if let alg::Attribute::Symbol(kw, val) = attr {
                    solver.set_info(kw.symbol_of(), val);
                } else if let alg::Attribute::Constant(kw, alg::Constant::String(s)) = attr {
                    solver.set_info(kw.symbol_of(), s);
                }
                Ok(())
            }
            AC::SetOption(attr) => {
                if let alg::Attribute::Symbol(kw, val) = attr {
                    solver.set_option(kw.symbol_of(), val);
                } else if let alg::Attribute::Constant(kw, alg::Constant::String(s)) = attr {
                    solver.set_option(kw.symbol_of(), s);
                }
                Ok(())
            }
            AC::DeclareConst(name, sort) => {
                let cs = sort.to_cvc5(self)?;
                let ct = self.tm.mk_const(cs, name);
                self.globals.insert(name.inner().clone(), ct);
                Ok(())
            }
            AC::DeclareFun(name, inp, out) => {
                let co = out.to_cvc5(self)?;
                if inp.is_empty() {
                    let ct = self.tm.mk_const(co, name);
                    self.globals.insert(name.inner().clone(), ct);
                } else {
                    let ci: Vec<CSort> = inp.iter().map(|s| s.to_cvc5(self)).collect::<Res<_>>()?;
                    let fs = self.tm.mk_fun_sort(&ci, co);
                    let ct = self.tm.mk_const(fs, name);
                    self.globals.insert(name.inner().clone(), ct);
                }
                Ok(())
            }
            AC::DeclareSort(name, arity) => {
                let cs = if *arity == 0 {
                    self.tm.mk_uninterpreted_sort(name)
                } else {
                    self.tm.mk_uninterpreted_sort_constructor_sort(*arity, name)
                };
                self.sort.insert(name.inner().clone(), cs);
                Ok(())
            }
            AC::DefineSort(..) => {
                // we don't need to do anything. typechecking will unfold all defined sorts
                Ok(())
            }
            AC::DefineConst(name, _sort, body) => {
                let cbody = body.to_cvc5(self)?;
                self.globals.insert(name.inner().clone(), cbody);
                Ok(())
            }
            AC::DefineFun(fd) => {
                self.translate_define_fun(solver, fd, false)?;
                Ok(())
            }
            AC::DefineFunRec(fd) => {
                self.translate_define_fun(solver, fd, true)?;
                Ok(())
            }
            AC::DefineFunsRec(fds) => {
                self.translate_define_funs_rec(solver, fds)?;
                Ok(())
            }
            AC::DeclareDatatype(name, dec) => {
                self.translate_declare_datatypes(&[alg::DatatypeDef {
                    name: name.clone(),
                    dec: dec.clone(),
                }])?;
                Ok(())
            }
            AC::DeclareDatatypes(defs) => {
                self.translate_declare_datatypes(defs)?;
                Ok(())
            }
            AC::Assert(t) => {
                let ct = t.to_cvc5(self)?;
                solver.assert_formula(CTerm::clone(&ct));
                Ok(())
            }
            AC::CheckSat => {
                let _ = solver.check_sat();
                Ok(())
            }
            AC::CheckSatAssuming(terms) => {
                let cts = self.translate_terms(terms)?;
                let _ = solver.check_sat_assuming(&cts);
                Ok(())
            }
            AC::GetValue(terms) => {
                let cts = self.translate_terms(terms)?;
                let _vals = solver.get_values(&cts);
                Ok(())
            }
            AC::GetModel => {
                // get_model requires sorts and consts; just call with empty for now
                let _ = solver.get_model(&[], &[]);
                Ok(())
            }
            AC::GetAssertions => {
                let _ = solver.get_assertions();
                Ok(())
            }
            AC::GetUnsatCore => {
                let _ = solver.get_unsat_core();
                Ok(())
            }
            AC::GetUnsatAssumptions => {
                let _ = solver.get_unsat_assumptions();
                Ok(())
            }
            AC::GetInfo(kw) => {
                let _ = solver.get_info(kw.symbol_of());
                Ok(())
            }
            AC::GetOption(kw) => {
                let _ = solver.get_option(kw.symbol_of());
                Ok(())
            }
            AC::Push(_) => {
                // push and pop are not supported because Context does not support push and pop,
                // so the symbol management is incorrect.

                // let n: u32 = n
                //     .try_into()
                //     .map_err(|_| "push level too large".to_string())?;
                // solver.push(n);
                // Ok(())
                Err("push is not supported".into())
            }
            AC::Pop(_) => {
                // let n: u32 = n
                //     .try_into()
                //     .map_err(|_| "pop level too large".to_string())?;
                // solver.pop(n);
                // Ok(())
                Err("pop is not supported".into())
            }
            AC::Reset => {
                // solver doesn't seem to support reset?
                Err("reset is not supported".into())
            }
            AC::ResetAssertions => {
                solver.reset_assertions();
                Ok(())
            }
            AC::Echo(_) | AC::Exit | AC::GetAssignment | AC::GetProof => Ok(()),
        }
    }

    fn translate_define_fun(
        &mut self,
        solver: &mut cvc5_rs::Solver,
        fd: &alg::FunctionDef<Str, Sort, Term>,
        recursive: bool,
    ) -> Res<()> {
        let out = fd.out_sort.to_cvc5(self)?;
        let mut vars = Vec::with_capacity(fd.vars.len());
        for v in &fd.vars {
            let vs = v.2.to_cvc5(self)?;
            let bv = self.tm.mk_var(vs, &v.0);
            self.locals.insert(v.1, bv.clone());
            vars.push(bv);
        }
        let body = fd.body.to_cvc5(self);
        for v in &fd.vars {
            self.locals.remove(&v.1);
        }
        let body = body?;
        let ct = if recursive {
            solver.define_fun_rec(&fd.name, &vars, out, body, true)
        } else {
            solver.define_fun(&fd.name, &vars, out, body, true)
        };
        self.globals.insert(fd.name.inner().clone(), ct);
        Ok(())
    }

    fn translate_define_funs_rec(
        &mut self,
        solver: &mut cvc5_rs::Solver,
        fds: &[alg::FunctionDef<Str, Sort, Term>],
    ) -> Res<()> {
        // First pass: declare all function constants so they can reference each other
        let mut funs = Vec::with_capacity(fds.len());
        let mut out_sorts = Vec::with_capacity(fds.len());
        for fd in fds {
            let mut inp = Vec::with_capacity(fd.vars.len());
            for v in &fd.vars {
                inp.push(v.2.to_cvc5(self)?);
            }
            let out = fd.out_sort.to_cvc5(self)?;
            out_sorts.push(out.clone());
            let fs = if inp.is_empty() {
                out.clone()
            } else {
                self.tm.mk_fun_sort(&inp, out)
            };
            let ct = self.tm.mk_const(fs, &fd.name);
            self.globals.insert(fd.name.inner().clone(), ct.clone());
            funs.push(ct);
        }
        // Second pass: translate bodies
        let mut all_vars = Vec::with_capacity(fds.len());
        let mut bodies = Vec::with_capacity(fds.len());
        for fd in fds {
            let mut vars = Vec::with_capacity(fd.vars.len());
            for v in &fd.vars {
                let vs = v.2.to_cvc5(self)?;
                let bv = self.tm.mk_var(vs, &v.0);
                self.locals.insert(v.1, bv.clone());
                vars.push(bv);
            }
            let body = fd.body.to_cvc5(self);
            for v in &fd.vars {
                self.locals.remove(&v.1);
            }
            all_vars.push(vars);
            bodies.push(body?);
        }
        let var_refs: Vec<&[CTerm]> = all_vars.iter().map(|v| v.as_slice()).collect();
        solver.define_funs_rec(&funs, &var_refs, &bodies, true);
        Ok(())
    }

    fn translate_declare_datatypes(&mut self, defs: &[alg::DatatypeDef<Str, Sort>]) -> Res<()> {
        let mut decls = Vec::with_capacity(defs.len());
        for def in defs {
            if !def.dec.params.is_empty() {
                return Err(format!(
                    "parametric datatypes not yet supported: {}",
                    def.name
                ));
            }
            let mut dt_decl = self.tm.mk_dt_decl(&def.name, false);
            for ctor in &def.dec.constructors {
                let mut ctor_decl = self.tm.mk_dt_cons_decl(&ctor.ctor);
                for sel in &ctor.args {
                    let ss = sel.2.to_cvc5(self)?;
                    ctor_decl.add_selector(&sel.0, ss);
                }
                dt_decl.add_constructor(&ctor_decl);
            }
            decls.push(dt_decl);
        }
        if decls.len() == 1 {
            let cs = self.tm.mk_dt_sort(&decls[0]);
            self.sort.insert(defs[0].name.inner().clone(), cs.clone());
            self.register_dt_functions(cs);
        } else {
            let sorts = self.tm.mk_dt_sorts(&decls);
            for (def, cs) in defs.iter().zip(sorts) {
                self.sort.insert(def.name.inner().clone(), cs.clone());
                self.register_dt_functions(cs);
            }
        }
        Ok(())
    }

    fn register_dt_functions(&mut self, sort: CSort) {
        let dt = sort.datatype();
        for i in 0..dt.num_constructors() {
            let ctor = dt.constructor(i);
            let ctor_term = ctor.term();
            let name = ctor.name();
            self.globals.insert(name.to_string(), ctor_term);
            let tester = ctor.tester_term();
            // Register both (_ is Ctor) and is-Ctor style testers
            self.globals.insert(format!("is-{name}"), tester.clone());
            for j in 0..ctor.num_selectors() {
                let sel = ctor.selector(j);
                let sel_term = sel.term();
                self.globals.insert(sel.name().to_string(), sel_term);
            }
        }
    }
}
