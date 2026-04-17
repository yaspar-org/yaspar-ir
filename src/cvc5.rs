// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Translation from yaspar-ir typed ASTs to cvc5 objects.
//!
//! This module provides the [`ConvertToCvc5`] trait and two environment types for translating
//! yaspar-ir typed ASTs into their cvc5 counterparts. It requires the `cvc5` feature.
//!
//! # Overview
//!
//! - [`ConvertToCvc5<Env>`] — the core trait, implemented for [`Sort`], [`Term`], and [`Command`].
//! - [`Cvc5Env`] — holds a [`cvc5::TermManager`] and caches for sort/term/symbol translation.
//!   Used as the environment for `Sort::to_cvc5` and `Term::to_cvc5`.
//! - [`Cvc5EnvSolver`] — wraps a [`Cvc5EnvInner`] and a [`Solver`]. Used as the environment
//!   for `Command::to_cvc5`, since commands may interact with the solver (e.g. `assert`,
//!   `check-sat`, `define-fun`).
//!
//! # Example
//!
//! ```rust
//! use cvc5::{Solver, TermManager};
//! use yaspar_ir::ast::{Context, Typecheck};
//! use yaspar_ir::cvc5::{ConvertToCvc5, Cvc5Env, Cvc5EnvSolver};
//! use yaspar_ir::untyped::UntypedAst;
//!
//! let mut ctx = Context::new();
//! let cmds = UntypedAst
//!     .parse_script_str("(set-logic QF_LIA) (declare-const x Int) (assert (> x 0)) (check-sat)")
//!     .unwrap()
//!     .type_check(&mut ctx)
//!     .unwrap();
//!
//! let tm = TermManager::new();
//! let mut solver = Solver::new(&tm);
//! let mut env = Cvc5Env::create(&tm);
//! let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
//! for cmd in &cmds {
//!     cmd.to_cvc5(&mut es).unwrap();
//! }
//! ```
//!
//! # Caching
//!
//! [`Cvc5Env`] caches translated sorts and terms so that repeated translations of the same
//! hashconsed object return the cached cvc5 object directly.
//!
//! # Annotations
//!
//! Quantifier `:pattern` annotations are translated to cvc5 `INST_PATTERN` / `INST_PATTERN_LIST`
//! terms, which guide quantifier instantiation. Other annotations are ignored.

use crate::ast::alg::VarBinding;
use crate::ast::*;
use crate::raw::alg;
use crate::raw::alg::CheckIdentifier;
use crate::traits::{Contains, Repr};
pub use cvc5::{Kind, ProofComponent, Solver, TermManager};
use std::collections::HashMap;
use yaspar::ast::Keyword;
use yaspar::{binary_to_string, hex_to_string};

pub type CSort<'tm> = cvc5::Sort<'tm>;
pub type CTerm<'tm> = cvc5::Term<'tm>;
pub type CResult<'tm> = cvc5::Result<'tm>;
pub type CProof<'tm> = cvc5::Proof<'tm>;
type Res<T> = std::result::Result<T, String>;

/// The result of translating and executing a single SMTLib command via cvc5.
#[derive(Debug)]
pub enum CommandResult<'tm> {
    /// No meaningful return value (declarations, definitions, `assert`, `set-logic`,
    /// `set-info`, `set-option`, `define-sort`, `reset-assertions`, `echo`, `exit`).
    None,
    /// Result of `check-sat` or `check-sat-assuming`.
    CheckSat(CResult<'tm>),
    /// Result of `get-value`: a list of terms.
    GetValue(Vec<CTerm<'tm>>),
    /// Result of `get-model`: the model as a string.
    GetModel(String),
    /// Result of `get-assertions`, `get-unsat-core`, or `get-unsat-assumptions`: a list of terms.
    Terms(Vec<CTerm<'tm>>),
    /// Result of `get-info` or `get-option`: a string response.
    Info(String),
    /// Result of `get-proof`: the full proof tree.
    GetProof(Vec<CProof<'tm>>),
}

/// Convert a yaspar-ir typed AST node to its cvc5 counterpart.
pub trait ConvertToCvc5<Env> {
    type Output;
    fn to_cvc5(&self, env: &mut Env) -> Res<Self::Output>;
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct WithPattern<'tm> {
    term: CTerm<'tm>,
    patterns: Vec<CTerm<'tm>>,
}

impl<'tm> From<WithPattern<'tm>> for CTerm<'tm> {
    fn from(value: WithPattern<'tm>) -> Self {
        value.term
    }
}

impl<'tm> From<CTerm<'tm>> for WithPattern<'tm> {
    fn from(value: CTerm<'tm>) -> Self {
        WithPattern {
            term: value,
            patterns: vec![],
        }
    }
}

type SortSubst<'tm> = Option<(Vec<CSort<'tm>>, Vec<CSort<'tm>>)>;

/// Environment for translating yaspar-ir ASTs to cvc5 objects.
pub struct Cvc5EnvInner<'tm> {
    tm: &'tm TermManager,
    sort: HashMap<String, CSort<'tm>>,
    globals: HashMap<String, CTerm<'tm>>,
    locals: HashMap<usize, WithPattern<'tm>>,
    sort_cache: HashMap<Sort, CSort<'tm>>,
    dt_sorts: HashMap<String, CSort<'tm>>,
    scope_stack: Vec<Vec<CTerm<'tm>>>,
    sort_subst_map: HashMap<Term, SortSubst<'tm>>,
}

impl<'tm> Cvc5EnvInner<'tm> {
    pub fn new(tm: &'tm TermManager) -> Self {
        Self {
            tm,
            sort: HashMap::new(),
            globals: HashMap::new(),
            locals: HashMap::new(),
            sort_cache: HashMap::new(),
            dt_sorts: HashMap::new(),
            scope_stack: vec![],
            sort_subst_map: Default::default(),
        }
    }
}
pub type Cvc5Env<'tm> = Memoize<Cvc5EnvInner<'tm>, HashMap<Term, WithPattern<'tm>>>;

impl<'tm> Cvc5Env<'tm> {
    pub fn create(tm: &'tm TermManager) -> Self {
        Self::new(Cvc5EnvInner::new(tm))
    }
}

/// Environment combining a [`Cvc5EnvInner`] with a [`Solver`] for translating commands.
pub struct Cvc5EnvSolver<'a, 'tm> {
    pub env: &'a mut Cvc5Env<'tm>,
    pub solver: &'a mut Solver<'tm>,
}

impl<'a, 'tm> Cvc5EnvSolver<'a, 'tm> {
    pub fn new(env: &'a mut Cvc5Env<'tm>, solver: &'a mut Solver<'tm>) -> Self {
        Self { env, solver }
    }
}

// ── Sort translation ─────────────────────────────────────────
impl<'tm> ConvertToCvc5<Cvc5EnvInner<'tm>> for Sort {
    type Output = CSort<'tm>;

    fn to_cvc5(&self, env: &mut Cvc5EnvInner<'tm>) -> Res<CSort<'tm>> {
        if let Some(cs) = env.sort_cache.get(self) {
            return Ok(cs.clone());
        }
        let cs = translate_sort_inner(self, env)?;
        env.sort_cache.insert(self.clone(), cs.clone());
        Ok(cs)
    }
}

fn translate_sort_inner<'tm>(sort: &Sort, env: &mut Cvc5EnvInner<'tm>) -> Res<CSort<'tm>> {
    let s = sort.repr();
    let name = &s.sort_name().to_string();
    if let Some(n) = s.is_bv() {
        let w: u32 = n
            .clone()
            .try_into()
            .map_err(|_| format!("bv width too large: {n}"))?;
        return Ok(env.tm.mk_bv_sort(w));
    }
    if !s.0.indices.is_empty() {
        return Err(format!("unknown sort with indices: {s}"));
    }
    // Check temporary datatype sorts (params and unresolved self-references)
    if let Some(cs) = env.dt_sorts.get(name).cloned() {
        if s.1.is_empty() {
            return Ok(cs);
        }
        let params: Vec<CSort> = s.1.to_cvc5(env)?;
        return Ok(cs.instantiate(&params));
    }
    if let Some(cs) = env.sort.get(name).cloned() {
        if s.1.is_empty() {
            return Ok(cs);
        }
        // Parametric sort: instantiate with translated parameters
        let params: Vec<CSort> = s.1.to_cvc5(env)?;
        return Ok(cs.instantiate(&params));
    }
    if sort.is_bool() {
        return Ok(env.tm.boolean_sort());
    }
    if sort.is_int() {
        return Ok(env.tm.integer_sort());
    }
    if sort.is_real() {
        return Ok(env.tm.real_sort());
    }
    if sort.is_string() {
        return Ok(env.tm.string_sort());
    }
    if sort.is_reglan() {
        return Ok(env.tm.regexp_sort());
    }
    if let Some((idx, elem)) = sort.is_array() {
        let ci = idx.to_cvc5(env)?;
        let ce = elem.to_cvc5(env)?;
        return Ok(env.tm.mk_array_sort(ci, ce));
    }

    Err(format!("unsupported sort: {sort}"))
}

impl<'tm> ConvertToCvc5<Cvc5Env<'tm>> for Sort {
    type Output = CSort<'tm>;

    #[inline]
    fn to_cvc5(&self, env: &mut Cvc5Env<'tm>) -> Res<Self::Output> {
        self.to_cvc5(&mut env.inner)
    }
}

// ── Identifier kind → cvc5 Kind mapping ─────────────────────
fn ident_kind_to_cvc5(k: &alg::IdentifierKind<Str>) -> Option<Kind> {
    use alg::IdentifierKind::*;
    Some(match k {
        Add => Kind::Add,
        Sub => Kind::Sub,
        Mul => Kind::Mult,
        Idiv => Kind::IntsDivision,
        Rdiv => Kind::Division,
        Mod => Kind::IntsModulus,
        Abs => Kind::Abs,
        Le => Kind::Leq,
        Lt => Kind::Lt,
        Ge => Kind::Geq,
        Gt => Kind::Gt,
        ToReal => Kind::ToReal,
        ToInt => Kind::ToInteger,
        IsInt => Kind::IsInteger,
        Select => Kind::Select,
        Store => Kind::Store,
        StrConcat => Kind::StringConcat,
        StrLen => Kind::StringLength,
        StrLt => Kind::StringLt,
        StrLe => Kind::StringLeq,
        StrAt => Kind::StringCharat,
        StrSubstr => Kind::StringSubstr,
        StrPrefixof => Kind::StringPrefix,
        StrSuffixof => Kind::StringSuffix,
        StrContains => Kind::StringContains,
        StrIndexof => Kind::StringIndexof,
        StrReplace => Kind::StringReplace,
        StrReplaceAll => Kind::StringReplaceAll,
        StrReplaceRe => Kind::StringReplaceRe,
        StrReplaceReAll => Kind::StringReplaceReAll,
        StrToRe => Kind::StringToRegexp,
        StrInRe => Kind::StringInRegexp,
        StrIsDigit => Kind::StringIsDigit,
        StrToCode => Kind::StringToCode,
        StrFromCode => Kind::StringFromCode,
        StrToInt => Kind::StringToInt,
        StrFromInt => Kind::StringFromInt,
        ReNone => Kind::RegexpNone,
        ReAll => Kind::RegexpAll,
        ReAllChar => Kind::RegexpAllchar,
        ReConcat => Kind::RegexpConcat,
        ReUnion => Kind::RegexpUnion,
        ReInter => Kind::RegexpInter,
        ReStar => Kind::RegexpStar,
        ReComp => Kind::RegexpComplement,
        ReDiff => Kind::RegexpDiff,
        ReAdd => Kind::RegexpPlus,
        ReOpt => Kind::RegexpOpt,
        ReRange => Kind::RegexpRange,
        Concat => Kind::BitvectorConcat,
        BvNot => Kind::BitvectorNot,
        BvNeg => Kind::BitvectorNeg,
        BvAnd => Kind::BitvectorAnd,
        BvOr => Kind::BitvectorOr,
        BvAdd => Kind::BitvectorAdd,
        BvMul => Kind::BitvectorMult,
        BvUdiv => Kind::BitvectorUdiv,
        BvUrem => Kind::BitvectorUrem,
        BvShl => Kind::BitvectorShl,
        BvLshr => Kind::BitvectorLshr,
        BvUlt => Kind::BitvectorUlt,
        BvNand => Kind::BitvectorNand,
        BvNor => Kind::BitvectorNor,
        BvXor => Kind::BitvectorXor,
        BvNxor => Kind::BitvectorXnor,
        BvComp => Kind::BitvectorComp,
        BvSub => Kind::BitvectorSub,
        BvSdiv => Kind::BitvectorSdiv,
        BvSrem => Kind::BitvectorSrem,
        BvSmod => Kind::BitvectorSmod,
        BvAShr => Kind::BitvectorAshr,
        BvUle => Kind::BitvectorUle,
        BvUgt => Kind::BitvectorUgt,
        BvUge => Kind::BitvectorUge,
        BvSlt => Kind::BitvectorSlt,
        BvSle => Kind::BitvectorSle,
        BvSgt => Kind::BitvectorSgt,
        BvSge => Kind::BitvectorSge,
        BvNego => Kind::BitvectorNego,
        BvUaddo => Kind::BitvectorUaddo,
        BvSaddo => Kind::BitvectorSaddo,
        BvUmulo => Kind::BitvectorUmulo,
        BvSmulo => Kind::BitvectorSmulo,
        UbvToInt => Kind::BitvectorUbvToInt,
        SbvToInt => Kind::BitvectorSbvToInt,
        Bv2Nat => Kind::BitvectorSbvToInt,
        Bv2Int => Kind::BitvectorSbvToInt,
        BvUsubo => Kind::BitvectorUsubo,
        BvSsubo => Kind::BitvectorSsubo,
        BvSdivo => Kind::BitvectorSdivo,
        _ => return None,
    })
}

// ── Term translation ─────────────────────────────────────────
impl<'tm> ConvertToCvc5<Cvc5Env<'tm>> for Term {
    type Output = CTerm<'tm>;

    fn to_cvc5(&self, env: &mut Cvc5Env<'tm>) -> Res<Self::Output> {
        env.recurse_on_term(self).map(|t| t.into())
    }
}

fn to_term_vec(terms: Vec<WithPattern>) -> Vec<CTerm> {
    terms.into_iter().map(|t| t.into()).collect()
}

impl<'tm> TermRecursor<Str, Sort, Term> for Cvc5EnvInner<'tm> {
    type Out = WithPattern<'tm>;
    type Attr = Vec<CTerm<'tm>>;
    type Binding = (usize, WithPattern<'tm>);
    type Pattern = ();
    type Arm = CTerm<'tm>;
    type Err = String;

    fn on_constant(
        &mut self,
        _current: &Term,
        constant: &Constant,
        sort: &Option<Sort>,
    ) -> Res<WithPattern<'tm>> {
        self.translate_constant(constant, sort.as_ref().unwrap())
    }

    fn on_global(
        &mut self,
        _current: &Term,
        id: &QualifiedIdentifier,
        sort: &Option<Sort>,
    ) -> Res<WithPattern<'tm>> {
        // it's fine due to typed invariant
        let sort = sort.as_ref().unwrap();
        self.translate_global(id, sort)
    }

    fn on_local(&mut self, _current: &Term, id: &Local) -> Res<WithPattern<'tm>> {
        self.locals
            .get(&id.id)
            .cloned()
            .ok_or_else(|| format!("unbound local: {}", id.symbol))
    }

    fn on_app(
        &mut self,
        _current: &Term,
        id: &QualifiedIdentifier,
        _ts: &[Term],
        s: &Option<Sort>,
        recs: Vec<WithPattern<'tm>>,
    ) -> Res<WithPattern<'tm>> {
        self.translate_app(
            id,
            recs.into_iter().map(|t| t.into()).collect(),
            s.as_ref().unwrap(),
        )
    }

    fn on_let_binding(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Term>],
        _body: &Term,
        binding_idx: usize,
        binding_rec: WithPattern<'tm>,
    ) -> Res<Self::Binding> {
        let idx = vs[binding_idx].1;
        Ok((idx, binding_rec))
    }
    fn setup_let_scope(
        &mut self,
        _current: &Term,
        _vs: &[VarBinding<Str, Term>],
        _body: &Term,
        vs_rec: &[Self::Binding],
    ) -> Res<()> {
        for (idx, t) in vs_rec {
            self.locals.insert(*idx, t.clone());
        }
        Ok(())
    }
    fn on_let(
        &mut self,
        _current: &Term,
        _vs: &[VarBinding<Str, Term>],
        _body: &Term,
        vs_rec: Vec<Self::Binding>,
        body_rec: WithPattern<'tm>,
    ) -> Res<WithPattern<'tm>> {
        for (idx, _) in vs_rec {
            self.locals.remove(&idx);
        }
        Ok(body_rec)
    }
    fn setup_quantifier_scope(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Sort>],
        _t: &Term,
        _is_forall: bool,
    ) -> Res<()> {
        self.bind_vars(vs)
    }
    fn on_exists(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Sort>],
        _t: &Term,
        t_rec: WithPattern<'tm>,
    ) -> Res<WithPattern<'tm>> {
        let bound = self.unbind_vars(vs, |v| &v.1)?;
        self.translate_quantifier_body(Kind::Exists, bound, t_rec)
    }
    fn on_forall(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Sort>],
        _t: &Term,
        t_rec: Self::Out,
    ) -> Res<WithPattern<'tm>> {
        let bound = self.unbind_vars(vs, |v| &v.1)?;
        self.translate_quantifier_body(Kind::Forall, bound, t_rec)
    }
    fn setup_match_case_scope(
        &mut self,
        _current: &Term,
        scrutinee: &Term,
        cases: &[PatternArm],
        scrutinee_rec: &Self::Out,
        case_idx: usize,
    ) -> Res<Self::Pattern> {
        let scr_sort = scrutinee_rec.term.sort();
        let dt = scr_sort.datatype();
        if !self.sort_subst_map.contains_key(scrutinee) {
            // For parametric datatypes, selector codomain sorts are uninstantiated (e.g. X).
            // We need to substitute the sort parameters with the actual instantiated parameters.
            let subst: SortSubst<'tm> = if dt.is_parametric() {
                let params = dt.parameters();
                let inst_params = scr_sort.instantiated_parameters();
                Some((params, inst_params))
            } else {
                None
            };
            self.sort_subst_map.insert(scrutinee.clone(), subst);
        }
        let subst = self.sort_subst_map.get(scrutinee).unwrap();
        match &cases[case_idx].pattern {
            Pattern::Wildcard(v) => {
                let pv = match v {
                    None => self.tm.mk_anonymous_var(scr_sort.clone()),
                    Some((name, id)) => {
                        let v = self.tm.mk_var(scr_sort.clone(), name);
                        self.locals.insert(*id, v.clone().into());
                        v
                    }
                };
                self.scope_stack.push(vec![pv]);
            }
            Pattern::Ctor(_) => {
                self.bind_vars(&[])?;
            }
            Pattern::Applied { ctor, arguments } => {
                let ctor = dt.constructor_by_name(ctor);
                let mut pattern_args = Vec::new();
                for (i, arg) in arguments.iter().enumerate() {
                    let mut sel_sort = ctor.selector(i).codomain_sort();
                    if let Some((params, inst)) = subst {
                        sel_sort = sel_sort.substitute_sorts(params, inst);
                    }
                    let pv = match arg {
                        Some((name, id)) => {
                            let bv = self.tm.mk_var(sel_sort, name);
                            self.locals.insert(*id, bv.clone().into());
                            bv
                        }
                        None => self.tm.mk_anonymous_var(sel_sort),
                    };
                    pattern_args.push(pv);
                }
                self.scope_stack.push(pattern_args);
            }
        }

        Ok(())
    }
    fn on_match_arm(
        &mut self,
        _current: &Term,
        _scrutinee: &Term,
        cases: &[PatternArm],
        scrutinee_rec: &Self::Out,
        case_idx: usize,
        _current_pattern: Self::Pattern,
        arm: Self::Out,
    ) -> Res<Self::Arm> {
        let scr_sort = scrutinee_rec.term.sort();
        let dt = scr_sort.datatype();
        let mut args = self.unbind_vars(&cases[case_idx].pattern.variables_and_ids(), |v| &v.1)?;
        match &cases[case_idx].pattern {
            Pattern::Wildcard(_) => {
                // we know there is only one variable
                let pv = args.remove(0);
                let vlist = self
                    .tm
                    .mk_term(Kind::VariableList, std::slice::from_ref(&pv));
                Ok(self
                    .tm
                    .mk_term(Kind::MatchBindCase, &[vlist, pv, arm.into()]))
            }
            Pattern::Ctor(name) => {
                let ctor = dt.constructor_by_name(name);
                let ctor_term = if dt.is_parametric() {
                    ctor.instantiated_term(scr_sort.clone())
                } else {
                    ctor.term()
                };
                let ctor_app = self.tm.mk_term(Kind::ApplyConstructor, &[ctor_term]);
                Ok(self.tm.mk_term(Kind::MatchCase, &[ctor_app, arm.into()]))
            }
            Pattern::Applied { ctor, .. } => {
                let ctor = dt.constructor_by_name(ctor);
                let mut pat_children = vec![ctor.term()];
                pat_children.extend(args.clone());
                let pattern = self.tm.mk_term(Kind::ApplyConstructor, &pat_children);
                let vlist = self.tm.mk_term(Kind::VariableList, &args);
                Ok(self
                    .tm
                    .mk_term(Kind::MatchBindCase, &[vlist, pattern, arm.into()]))
            }
        }
    }
    fn on_match(
        &mut self,
        _current: &Term,
        _scrutinee: &Term,
        _cases: &[PatternArm],
        scrutinee_rec: Self::Out,
        cases_rec: Vec<Self::Arm>,
    ) -> Res<WithPattern<'tm>> {
        let mut match_children = vec![scrutinee_rec.into()];
        match_children.extend(cases_rec);
        Ok(self.tm.mk_term(Kind::Match, &match_children).into())
    }

    fn on_annotated(
        &mut self,
        _current: &Term,
        _t: &Term,
        _anns: &[Attribute],
        t_rec: WithPattern<'tm>,
        anns_rec: Vec<Vec<CTerm<'tm>>>,
    ) -> Res<WithPattern<'tm>> {
        // do not handle other annotations
        let mut pats = t_rec.patterns;
        anns_rec.into_iter().for_each(|ps| pats.extend(ps));
        Ok(WithPattern {
            term: t_rec.term,
            patterns: pats,
        })
    }
    fn on_attribute_keyword(&mut self, _keyword: &Keyword) -> Res<Vec<CTerm<'tm>>> {
        Ok(vec![])
    }
    fn on_attribute_constant(
        &mut self,
        _keyword: &Keyword,
        _constant: &Constant,
    ) -> Res<Vec<CTerm<'tm>>> {
        Ok(vec![])
    }
    fn on_attribute_symbol(&mut self, _keyword: &Keyword, _symbol: &Str) -> Res<Vec<CTerm<'tm>>> {
        Ok(vec![])
    }
    fn on_attribute_named(&mut self, _name: &Str) -> Res<Vec<CTerm<'tm>>> {
        Ok(vec![])
    }

    fn on_attribute_pattern(
        &mut self,
        _patterns: &[Term],
        patterns_rec: Vec<WithPattern<'tm>>,
    ) -> Res<Vec<CTerm<'tm>>> {
        Ok(to_term_vec(patterns_rec))
    }

    fn on_eq(
        &mut self,
        _current: &Term,
        _a: &Term,
        _b: &Term,
        a_rec: WithPattern<'tm>,
        b_rec: WithPattern<'tm>,
    ) -> Res<WithPattern<'tm>> {
        Ok(self
            .tm
            .mk_term(Kind::Equal, &[a_rec.into(), b_rec.into()])
            .into())
    }

    fn on_distinct(
        &mut self,
        _current: &Term,
        _ts: &[Term],
        ts_rec: Vec<WithPattern<'tm>>,
    ) -> Res<WithPattern<'tm>> {
        Ok(self.tm.mk_term(Kind::Distinct, &to_term_vec(ts_rec)).into())
    }

    fn on_and(
        &mut self,
        _current: &Term,
        _ts: &[Term],
        ts_rec: Vec<WithPattern<'tm>>,
    ) -> Res<WithPattern<'tm>> {
        Ok(self.tm.mk_term(Kind::And, &to_term_vec(ts_rec)).into())
    }

    fn on_or(
        &mut self,
        _current: &Term,
        _ts: &[Term],
        ts_rec: Vec<WithPattern<'tm>>,
    ) -> Res<WithPattern<'tm>> {
        Ok(self.tm.mk_term(Kind::Or, &to_term_vec(ts_rec)).into())
    }

    fn on_xor(
        &mut self,
        _current: &Term,
        _ts: &[Term],
        ts_rec: Vec<WithPattern<'tm>>,
    ) -> Res<WithPattern<'tm>> {
        Ok(self.tm.mk_term(Kind::Xor, &to_term_vec(ts_rec)).into())
    }

    fn on_not(
        &mut self,
        _current: &Term,
        _t: &Term,
        t_rec: WithPattern<'tm>,
    ) -> Res<WithPattern<'tm>> {
        Ok(self.tm.mk_term(Kind::Not, &[t_rec.into()]).into())
    }

    fn on_implies(
        &mut self,
        _current: &Term,
        _ts: &[Term],
        _t: &Term,
        ts_rec: Vec<WithPattern<'tm>>,
        t_rec: WithPattern<'tm>,
    ) -> Res<WithPattern<'tm>> {
        let mut all = ts_rec;
        all.push(t_rec);
        Ok(self.tm.mk_term(Kind::Implies, &to_term_vec(all)).into())
    }

    fn on_ite(
        &mut self,
        _current: &Term,
        _b: &Term,
        _t: &Term,
        _e: &Term,
        b_rec: WithPattern<'tm>,
        t_rec: WithPattern<'tm>,
        e_rec: WithPattern<'tm>,
    ) -> Res<WithPattern<'tm>> {
        Ok(self
            .tm
            .mk_term(Kind::Ite, &[b_rec.into(), t_rec.into(), e_rec.into()])
            .into())
    }
}

impl<'tm> TypedTermRecursor for Cvc5EnvInner<'tm> {}

impl<T, Env, E> ConvertToCvc5<Env> for [T]
where
    T: ConvertToCvc5<Env, Output = E>,
{
    type Output = Vec<E>;

    fn to_cvc5(&self, env: &mut Env) -> Res<Self::Output> {
        self.iter().map(|t| t.to_cvc5(env)).collect()
    }
}

impl<'tm> Cvc5EnvInner<'tm> {
    fn translate_constant(&self, c: &Constant, s: &Sort) -> Res<WithPattern<'tm>> {
        use alg::Constant::*;
        match c {
            Bool(true) => Ok(self.tm.mk_true().into()),
            Bool(false) => Ok(self.tm.mk_false().into()),
            Numeral(n) => {
                if s.is_real() {
                    Ok(self.tm.mk_real_from_str(&n.to_string()).into())
                } else {
                    Ok(self.tm.mk_integer_from_str(&n.to_string()).into())
                }
            }
            Decimal(d) => Ok(self.tm.mk_real_from_str(&d.to_string()).into()),
            String(s) => Ok(self.tm.mk_string(s, false).into()),
            Binary(bytes, len) => {
                let bits = binary_to_string(bytes, *len);
                let w: u32 = (*len)
                    .try_into()
                    .map_err(|_| format!("binary literal width too large: {len}"))?;
                Ok(self.tm.mk_bv_from_str(w, &bits, 2).into())
            }
            Hexadecimal(bytes, len) => {
                let hex = hex_to_string(bytes, *len);
                let w: u32 = len
                    .checked_mul(4)
                    .and_then(|n| n.try_into().ok())
                    .ok_or_else(|| format!("hex literal width too large: {len}"))?;
                Ok(self.tm.mk_bv_from_str(w, &hex, 16).into())
            }
        }
    }

    /// Build `(kind head args...)`.
    fn mk_applied(
        &self,
        kind: Kind,
        head: CTerm<'tm>,
        mut args: Vec<CTerm<'tm>>,
    ) -> WithPattern<'tm> {
        args.insert(0, head);
        self.tm.mk_term(kind, &args).into()
    }

    /// Look up a constructor by name in the datatype behind `sort`, returning its
    /// instantiated term if the datatype is parametric. Returns `None` when the sort
    /// is not in the sort table, the datatype is not parametric, or no constructor matches.
    fn resolve_parametric_ctor(&mut self, name: &str, sort: &Sort) -> Res<Option<CTerm<'tm>>> {
        let sort_name = &sort.sort_name().to_string();
        if let Some(base_sort) = self.sort.get(sort_name).cloned() {
            let dt = base_sort.datatype();
            if dt.is_parametric() {
                let crs = sort.to_cvc5(self)?;
                for i in 0..dt.num_constructors() {
                    let ctor = dt.constructor(i);
                    if ctor.name() == name {
                        return Ok(Some(ctor.instantiated_term(crs)));
                    }
                }
            }
        }
        Ok(None)
    }

    fn translate_global(
        &mut self,
        qid: &QualifiedIdentifier,
        sort: &Sort,
    ) -> Res<WithPattern<'tm>> {
        use alg::IdentifierKind::*;
        let name = &qid.id_str().to_string();
        match qid.get_kind() {
            Some(Char(hex, _)) => Ok(self
                .tm
                .mk_string(
                    &String::from_utf8(hex).map_err(|err| {
                        format!("symbol {qid} cannot be converted to a String: {err}")
                    })?,
                    false,
                )
                .into()),
            _ => {
                // For sort-ascribed parametric constructors like (as nil (List Int)),
                // resolve via the instantiated sort using instantiated_term
                let t = self
                    .globals
                    .get(name)
                    .cloned()
                    .ok_or_else(|| format!("unknown global symbol: {name}"))?;
                let is_ctor = t.sort().is_dt_constructor();
                if is_ctor {
                    if let Some(ct) = self.resolve_parametric_ctor(name, sort)? {
                        Ok(self.tm.mk_term(Kind::ApplyConstructor, &[ct]).into())
                    } else {
                        Ok(self.tm.mk_term(Kind::ApplyConstructor, &[t]).into())
                    }
                } else {
                    Ok(t.into())
                }
            }
        }
    }

    /// Translate sorted variable bindings into cvc5 bound variables, inserting them into `locals`.
    fn bind_vars(&mut self, vars: &[VarBinding<Str, Sort>]) -> Res<()> {
        let mut bound = Vec::with_capacity(vars.len());
        for v in vars {
            let cs = v.2.to_cvc5(self)?;
            let bv = self.tm.mk_var(cs, &v.0);
            self.locals.insert(v.1, bv.clone().into());
            bound.push(bv);
        }
        self.scope_stack.push(bound);
        Ok(())
    }

    /// Remove variable bindings from `locals`.
    fn unbind_vars<T, F>(&mut self, vars: &[T], f: F) -> Res<Vec<CTerm<'tm>>>
    where
        F: Fn(&T) -> &usize,
    {
        for v in vars {
            self.locals.remove(f(v));
        }
        self.scope_stack
            .pop()
            .ok_or_else(|| "invariance violation: scope management failure".into())
    }

    fn translate_quantifier_body(
        &mut self,
        kind: Kind,
        bound: Vec<CTerm<'tm>>,
        t_rec: WithPattern<'tm>,
    ) -> Res<WithPattern<'tm>> {
        let bvl = self.tm.mk_term(Kind::VariableList, &bound);

        // Peel off annotations from the body to extract :pattern triggers
        let cbody = t_rec.term;

        // Build INST_PATTERN_LIST from :pattern annotations
        if !t_rec.patterns.is_empty() {
            let pats = self.tm.mk_term(Kind::InstPattern, &t_rec.patterns);
            let plist = self
                .tm
                .mk_term(Kind::InstPatternList, std::slice::from_ref(&pats));
            return Ok(self.tm.mk_term(kind, &[bvl, cbody, plist]).into());
        }
        Ok(self.tm.mk_term(kind, &[bvl, cbody]).into())
    }

    fn translate_app(
        &mut self,
        qid: &QualifiedIdentifier,
        cargs: Vec<CTerm<'tm>>,
        rs: &Sort,
    ) -> Res<WithPattern<'tm>> {
        let id = &qid.0;
        let kind = id.get_kind();
        // Handle unary minus: (- x) → NEG
        if let Some(IdentifierKind::Sub) = kind
            && cargs.len() == 1
        {
            return Ok(self.tm.mk_term(Kind::Neg, &cargs).into());
        }
        if let Some(kind) = kind.as_ref().and_then(ident_kind_to_cvc5) {
            return Ok(self.tm.mk_term(kind, &cargs).into());
        }
        if let Some(ref ik) = kind {
            return self.translate_indexed_app(ik, cargs);
        }
        let name = &id.symbol.to_string();
        if let Some(f) = self.globals.get(name).cloned() {
            let fs = f.sort();
            if fs.is_dt_constructor() {
                if let Some(ct) = self.resolve_parametric_ctor(name, rs)? {
                    Ok(self.mk_applied(Kind::ApplyConstructor, ct, cargs))
                } else {
                    Ok(self.mk_applied(Kind::ApplyConstructor, f, cargs))
                }
            } else if fs.is_dt_selector() {
                Ok(self.mk_applied(Kind::ApplySelector, f, cargs))
            } else if fs.is_dt_tester() {
                Ok(self.mk_applied(Kind::ApplyTester, f, cargs))
            } else {
                Ok(self.mk_applied(Kind::ApplyUf, f, cargs))
            }
        } else {
            Err(format!("unknown function: {name}"))
        }
    }

    fn translate_indexed_app(
        &self,
        ik: &IdentifierKind,
        cargs: Vec<CTerm<'tm>>,
    ) -> Res<WithPattern<'tm>> {
        use alg::IdentifierKind::*;
        let mk = |kind, indices: &[u32]| {
            let op = self.tm.mk_op(kind, indices);
            Ok(self.tm.mk_term_from_op(op, &cargs).into())
        };
        let to_u32 = |n: &dashu::integer::UBig| -> Res<u32> {
            n.try_into().map_err(|_| format!("index too large: {n}"))
        };
        match ik {
            Extract(hi, lo) => mk(Kind::BitvectorExtract, &[to_u32(hi)?, to_u32(lo)?]),
            Repeat(n) => mk(Kind::BitvectorRepeat, &[to_u32(n)?]),
            ZeroExtend(n) => mk(Kind::BitvectorZeroExtend, &[to_u32(n)?]),
            SignExtend(n) => mk(Kind::BitvectorSignExtend, &[to_u32(n)?]),
            RotateLeft(n) => mk(Kind::BitvectorRotateLeft, &[to_u32(n)?]),
            RotateRight(n) => mk(Kind::BitvectorRotateRight, &[to_u32(n)?]),
            IntToBv(n) | Int2Bv(n) | Nat2Bv(n) => mk(Kind::IntToBitvector, &[to_u32(n)?]),
            RePower(n) => mk(Kind::RegexpRepeat, &[to_u32(n)?]),
            ReLoop(lo, hi) => mk(Kind::RegexpLoop, &[to_u32(lo)?, to_u32(hi)?]),
            Is(cname) => {
                // Resolve tester via the argument's sort (works for both mono and parametric)
                if let Some(arg) = cargs.first() {
                    let dt = arg.sort().datatype();
                    for i in 0..dt.num_constructors() {
                        let ctor = dt.constructor(i);
                        if ctor.name() == cname.inner().as_str() {
                            return Ok(self.mk_applied(
                                Kind::ApplyTester,
                                ctor.tester_term(),
                                cargs,
                            ));
                        }
                    }
                }
                Err(format!("unknown tester: (_ is {})", cname.inner()))
            }
            _ => Err(format!("unsupported indexed operator: {:?}", ik)),
        }
    }
}

// ── Command translation ──────────────────────────────────────
impl<'tm> ConvertToCvc5<Cvc5EnvSolver<'_, 'tm>> for Command {
    type Output = CommandResult<'tm>;

    fn to_cvc5(&self, es: &mut Cvc5EnvSolver<'_, 'tm>) -> Res<Self::Output> {
        use alg::Command as AC;
        let env = &mut *es.env;
        let solver = &mut *es.solver;
        match self.inner().repr() {
            AC::SetLogic(l) => {
                solver.set_logic(l);
                Ok(CommandResult::None)
            }
            AC::SetInfo(attr) => {
                if let Attribute::Symbol(kw, val) = attr {
                    solver.set_info(kw.symbol_of(), val);
                } else if let Attribute::Constant(kw, Constant::String(s)) = attr {
                    solver.set_info(kw.symbol_of(), s);
                }
                Ok(CommandResult::None)
            }
            AC::SetOption(attr) => {
                if let Attribute::Symbol(kw, val) = attr {
                    solver.set_option(kw.symbol_of(), val);
                } else if let Attribute::Constant(kw, Constant::String(s)) = attr {
                    solver.set_option(kw.symbol_of(), s);
                }
                Ok(CommandResult::None)
            }
            AC::DeclareConst(name, sort) => {
                let cs = sort.to_cvc5(env)?;
                let ct = env.tm.mk_const(cs, name);
                env.globals.insert(name.to_string(), ct);
                Ok(CommandResult::None)
            }
            AC::DeclareFun(name, inp, out) => {
                let co = out.to_cvc5(env)?;
                if inp.is_empty() {
                    let ct = env.tm.mk_const(co, name);
                    env.globals.insert(name.to_string(), ct);
                } else {
                    let ci = inp.to_cvc5(env)?;
                    let fs = env.tm.mk_fun_sort(&ci, co);
                    let ct = env.tm.mk_const(fs, name);
                    env.globals.insert(name.to_string(), ct);
                }
                Ok(CommandResult::None)
            }
            AC::DeclareSort(name, arity) => {
                let cs = if *arity == 0 {
                    env.tm.mk_uninterpreted_sort(name)
                } else {
                    env.tm.mk_uninterpreted_sort_constructor_sort(*arity, name)
                };
                env.sort.insert(name.to_string(), cs);
                Ok(CommandResult::None)
            }
            AC::DefineSort(..) => {
                // we don't need to do anything. typechecking will unfold all defined sorts
                Ok(CommandResult::None)
            }
            AC::DefineConst(name, _sort, body) => {
                let cbody = body.to_cvc5(env)?;
                env.globals.insert(name.to_string(), cbody);
                Ok(CommandResult::None)
            }
            AC::DefineFun(fd) => es.translate_define_fun(fd, false),
            AC::DefineFunRec(fd) => es.translate_define_fun(fd, true),
            AC::DefineFunsRec(fds) => es.translate_define_funs_rec(fds),
            AC::DeclareDatatype(name, dec) => es.translate_declare_datatypes(&[alg::DatatypeDef {
                name: name.clone(),
                dec: dec.clone(),
            }]),
            AC::DeclareDatatypes(defs) => es.translate_declare_datatypes(defs),
            AC::Assert(t) => {
                // Peel outermost :named annotations
                let mut names = Vec::new();
                let mut cur = t;
                while let ATerm::Annotated(inner, attrs) = cur.repr() {
                    for attr in attrs {
                        if let Attribute::Named(name) = attr {
                            names.push(name.clone());
                        }
                    }
                    cur = inner;
                }
                let ct = cur.to_cvc5(env)?;
                for name in names {
                    env.globals.insert(name.to_string(), ct.clone());
                }
                solver.assert_formula(CTerm::clone(&ct));
                Ok(CommandResult::None)
            }
            AC::CheckSat => {
                let r = solver.check_sat();
                Ok(CommandResult::CheckSat(r))
            }
            AC::CheckSatAssuming(terms) => {
                let cts = terms.to_cvc5(env)?;
                let r = solver.check_sat_assuming(&cts);
                Ok(CommandResult::CheckSat(r))
            }
            AC::GetValue(terms) => {
                let cts = terms.to_cvc5(env)?;
                let vals = solver.get_values(&cts);
                Ok(CommandResult::GetValue(vals))
            }
            AC::GetModel => {
                // get_model requires sorts and consts; just call with empty for now
                let m = solver.get_model(&[], &[]);
                Ok(CommandResult::GetModel(m))
            }
            AC::GetAssertions => {
                let ts = solver.get_assertions();
                Ok(CommandResult::Terms(ts))
            }
            AC::GetUnsatCore => {
                let ts = solver.get_unsat_core();
                Ok(CommandResult::Terms(ts))
            }
            AC::GetUnsatAssumptions => {
                let ts = solver.get_unsat_assumptions();
                Ok(CommandResult::Terms(ts))
            }
            AC::GetInfo(kw) => {
                let s = solver.get_info(kw.symbol_of());
                Ok(CommandResult::Info(s))
            }
            AC::GetOption(kw) => {
                let s = solver.get_option(kw.symbol_of());
                Ok(CommandResult::Info(s))
            }
            AC::Push(_) => {
                // push and pop are not supported because Context does not support push and pop,
                // so the symbol management is incorrect.
                Err("push is not supported".into())
            }
            AC::Pop(_) => Err("pop is not supported".into()),
            AC::Reset => Err("reset is not supported".into()),
            AC::ResetAssertions => {
                solver.reset_assertions();
                Ok(CommandResult::None)
            }
            AC::Echo(_) | AC::Exit | AC::GetAssignment => Ok(CommandResult::None),
            AC::GetProof => {
                let proofs = solver.get_proof(ProofComponent::Full);
                Ok(CommandResult::GetProof(proofs))
            }
        }
    }
}

// ── Command helper methods ───────────────────────────────────
impl<'tm> Cvc5EnvSolver<'_, 'tm> {
    fn translate_define_fun(
        &mut self,
        fd: &alg::FunctionDef<Str, Sort, Term>,
        recursive: bool,
    ) -> Res<CommandResult<'tm>> {
        let env = &mut *self.env;
        let out = fd.out_sort.to_cvc5(env)?;
        env.bind_vars(&fd.vars)?;
        let body = fd.body.to_cvc5(env);
        let vars = env.unbind_vars(&fd.vars, |v| &v.1)?;
        let body = body?;
        let ct = if recursive {
            self.solver.define_fun_rec(&fd.name, &vars, out, body, true)
        } else {
            self.solver.define_fun(&fd.name, &vars, out, body, true)
        };
        self.env.globals.insert(fd.name.to_string(), ct);
        Ok(CommandResult::None)
    }

    fn translate_define_funs_rec(
        &mut self,
        fds: &[alg::FunctionDef<Str, Sort, Term>],
    ) -> Res<CommandResult<'tm>> {
        let env = &mut *self.env;
        // First pass: declare all function constants so they can reference each other
        let mut funs = Vec::with_capacity(fds.len());
        let mut out_sorts = Vec::with_capacity(fds.len());
        for fd in fds {
            let mut inp = Vec::with_capacity(fd.vars.len());
            for v in &fd.vars {
                inp.push(v.2.to_cvc5(env)?);
            }
            let out = fd.out_sort.to_cvc5(env)?;
            out_sorts.push(out.clone());
            let fs = if inp.is_empty() {
                out.clone()
            } else {
                env.tm.mk_fun_sort(&inp, out)
            };
            let ct = env.tm.mk_const(fs, &fd.name);
            env.globals.insert(fd.name.to_string(), ct.clone());
            funs.push(ct);
        }
        // Second pass: translate bodies
        let mut all_vars = Vec::with_capacity(fds.len());
        let mut bodies = Vec::with_capacity(fds.len());
        for fd in fds {
            env.bind_vars(&fd.vars)?;
            let body = fd.body.to_cvc5(env);
            let vars = env.unbind_vars(&fd.vars, |v| &v.1)?;
            all_vars.push(vars);
            bodies.push(body?);
        }
        let var_refs: Vec<&[CTerm<'tm>]> = all_vars.iter().map(|v| v.as_slice()).collect();
        self.solver.define_funs_rec(&funs, &var_refs, &bodies, true);
        Ok(CommandResult::None)
    }

    fn translate_declare_datatypes(
        &mut self,
        defs: &[alg::DatatypeDef<Str, Sort>],
    ) -> Res<CommandResult<'tm>> {
        let env = &mut *self.env;
        // Pre-register unresolved sorts so self/mutual references resolve
        for def in defs {
            let arity = def.dec.params.len();
            let us = env.tm.mk_unresolved_dt_sort(&def.name, arity);
            env.dt_sorts.insert(def.name.to_string(), us);
        }
        let result = Self::build_dt_decls(env, defs);
        env.dt_sorts.clear();
        let decls = result?;
        if decls.len() == 1 {
            let cs = env.tm.mk_dt_sort(&decls[0]);
            env.sort.insert(defs[0].name.to_string(), cs.clone());
            Self::register_dt_functions(env, cs, &defs[0].dec);
        } else {
            let sorts = env.tm.mk_dt_sorts(&decls);
            for (def, cs) in defs.iter().zip(sorts) {
                env.sort.insert(def.name.to_string(), cs.clone());
                Self::register_dt_functions(env, cs, &def.dec);
            }
        }
        Ok(CommandResult::None)
    }

    fn build_dt_decls(
        env: &mut Cvc5EnvInner<'tm>,
        defs: &[alg::DatatypeDef<Str, Sort>],
    ) -> Res<Vec<cvc5::DatatypeDecl<'tm>>> {
        let mut decls = Vec::with_capacity(defs.len());
        for def in defs {
            let params = &def.dec.params;
            let cvc5_params: Vec<CSort<'tm>> =
                params.iter().map(|p| env.tm.mk_param_sort(p)).collect();
            for (p, cs) in params.iter().zip(&cvc5_params) {
                env.dt_sorts.insert(p.to_string(), cs.clone());
            }
            let mut dt_decl = if cvc5_params.is_empty() {
                env.tm.mk_dt_decl(&def.name, false)
            } else {
                env.tm
                    .mk_dt_decl_with_params(&def.name, &cvc5_params, false)
            };
            for ctor in &def.dec.constructors {
                let mut ctor_decl = env.tm.mk_dt_cons_decl(&ctor.ctor);
                for sel in &ctor.args {
                    let ss = sel.2.to_cvc5(env)?;
                    ctor_decl.add_selector(&sel.0, ss);
                }
                dt_decl.add_constructor(&ctor_decl);
            }
            for p in params {
                env.dt_sorts.remove(p.as_str());
            }
            decls.push(dt_decl);
        }
        Ok(decls)
    }

    fn register_dt_functions(env: &mut Cvc5EnvInner<'tm>, sort: CSort<'tm>, dec: &DatatypeDec) {
        let dt = sort.datatype();
        for (i, ctor_dec) in dec.constructors.iter().enumerate() {
            let ctor = dt.constructor(i);
            env.globals.insert(ctor_dec.ctor.to_string(), ctor.term());
            let tester = ctor.tester_term();
            env.globals.insert(format!("is-{}", ctor.name()), tester);
            for (j, sel_dec) in ctor_dec.args.iter().enumerate() {
                let sel = ctor.selector(j);
                env.globals.insert(sel_dec.0.to_string(), sel.term());
            }
        }
    }
}
