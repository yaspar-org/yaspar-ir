// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Translation between yaspar-ir typed ASTs and cvc5 objects.
//!
//! This module provides bidirectional translation between yaspar-ir and cvc5:
//!
//! - **Forward** ([`ConvertToCvc5`]): translates yaspar-ir [`Sort`], [`Term`], and [`Command`]
//!   into their cvc5 counterparts.
//! - **Backward** ([`ConvertFromCvc5`]): translates cvc5 sorts and terms back into yaspar-ir
//!   typed ASTs.
//!
//! # Forward translation
//!
//! - [`ConvertToCvc5<Env>`] — the core trait, implemented for [`Sort`], [`Term`], and [`Command`].
//! - [`Cvc5Env<'tm, Ctx>`] — holds a [`cvc5::TermManager`], a [`Context`] handle (any
//!   `Ctx: HasMutRef<Context>` — e.g. `&mut Context`, `Rc<RefCell<Context>>`), and caches
//!   for sort/term/symbol translation in both directions. Used as the environment for
//!   `Sort::to_cvc5`, `Term::to_cvc5`, `CSort::conv_from_cvc5`, and `CTerm::conv_from_cvc5`.
//! - [`Cvc5EnvSolver`] — wraps a [`Cvc5Env`] and a [`Solver`]. Used as the environment
//!   for `Command::to_cvc5`, since commands may interact with the solver (e.g. `assert`,
//!   `check-sat`, `define-fun`).
//!
//! # Backward translation
//!
//! - [`ConvertFromCvc5<Env>`] — the core trait, implemented for [`CSort`] and [`CTerm`].
//! - [`Cvc5Env`] — also serves as the environment for backward translation, sharing the
//!   sort/term caches with the forward direction, and additionally holding scoped variable
//!   bindings and a record of uninterpreted sort values encountered.
//!
//! The backward translation handles constants, logical connectives, quantifiers (including
//! `:pattern` annotations), arithmetic/bitvector/string operators, indexed operators,
//! datatype constructors/selectors/testers, match expressions, and uninterpreted sort values.
//!
//! Command results that carry terms ([`CommandResult::GetValue`] and [`CommandResult::Terms`])
//! are backward-translated into yaspar-ir [`Term`] values before being returned, so callers
//! never see raw [`CTerm`] handles.
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
//! let mut env = Cvc5Env::new(&tm, &mut ctx);
//! let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
//! for cmd in &cmds {
//!     cmd.to_cvc5(&mut es).unwrap();
//! }
//! ```
//!
//! # Caching
//!
//! [`Cvc5Env`] keeps a single [`BiHashMap`] for sorts and a single one for terms, shared by
//! both directions: a forward translation that produces a `(yaspar, cvc5)` pair populates
//! the cache, and a subsequent reverse translation of the same cvc5 object hits it without
//! recomputing.
//!
//! # Annotations
//!
//! Quantifier `:pattern` annotations are preserved in both directions: translated to cvc5
//! `INST_PATTERN` / `INST_PATTERN_LIST` terms in the forward direction, and reconstructed as
//! `Attribute::Pattern` annotations in the backward direction.
//!
//! `:named` annotations on `assert` are recorded in a `CTerm → name` table during forward
//! translation. When cvc5 returns terms that match a named assertion (e.g. via
//! `get-unsat-core`, `get-assertions`, or `get-unsat-assumptions`), the recorded name is
//! returned as a yaspar-ir global identifier rather than the assertion body — recovering
//! the SMT-LIB label that cvc5's solver-level API would otherwise drop.

use crate::ast::alg::VarBinding;
use crate::ast::*;
use crate::containers::{InsertableMapping, Mapping};
use crate::raw::alg;
use crate::raw::alg::CheckIdentifier;
use crate::raw::alg::rec::TermRecursionScheme;
use crate::raw::alg::rec_memo::{MemoizedRecursion, MemoizedScheme, Memoizing};
use crate::statics::*;
use crate::traits::{AllocatableString, Contains, HasMutRef, Repr};
use crate::untyped::UntypedAst;
use bimap::BiHashMap;
pub use cvc5::{Kind, ProofComponent, Solver, TermManager};
use dashu::integer::UBig;
use std::collections::{HashMap, HashSet};
use yaspar::ast::Keyword;
use yaspar::{binary_to_string, hex_to_string};

/// A cvc5 sort, tied to the lifetime of the [`TermManager`] that created it.
pub type CSort<'tm> = cvc5::Sort<'tm>;
/// A cvc5 term, tied to the lifetime of the [`TermManager`] that created it.
pub type CTerm<'tm> = cvc5::Term<'tm>;
/// A cvc5 satisfiability result, tied to the lifetime of the [`TermManager`].
pub type CResult<'tm> = cvc5::Result<'tm>;
/// A cvc5 proof object, tied to the lifetime of the [`TermManager`].
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
    /// Result of `get-value`: a list of yaspar-ir terms (each cvc5-returned value
    /// is backward-translated into [`Term`]).
    GetValue(Vec<Term>),
    /// Result of `get-model`: the model as a string.
    GetModel(String),
    /// Result of `get-assertions`, `get-unsat-core`, or `get-unsat-assumptions`: a list
    /// of yaspar-ir terms. For each cvc5-returned formula, if its `CTerm` was registered
    /// via an `(assert (! ... :named X))` form, `X` is returned as a global identifier;
    /// otherwise the formula is backward-translated into a [`Term`].
    Terms(Vec<Term>),
    /// Result of `get-info` or `get-option`: a string response.
    Info(String),
    /// Result of `get-proof`: the full proof tree.
    GetProof(Vec<CProof<'tm>>),
}

/// Convert a yaspar-ir typed AST node to its cvc5 counterpart.
///
/// This trait is implemented for [`Sort`], [`Term`], and [`Command`], each with a
/// different environment type:
///
/// | AST node    | Environment          | Output             |
/// |-------------|----------------------|--------------------|
/// | [`Sort`]    | [`Cvc5Env`]          | [`CSort`]          |
/// | [`Term`]    | [`Cvc5Env`]          | [`CTerm`]          |
/// | [`Command`] | [`Cvc5EnvSolver`]    | [`CommandResult`]  |
///
/// Translation may fail if the AST references symbols or sorts not yet registered
/// in the environment (e.g. an undeclared global variable).
pub trait ConvertToCvc5<Env> {
    /// The cvc5 type produced by the translation.
    type Output;
    /// Translate `self` into a cvc5 object, using `env` for symbol/sort lookup and caching.
    fn to_cvc5(&self, env: &mut Env) -> Res<Self::Output>;
}

/// Convert a cvc5 object back to its yaspar-ir typed AST counterpart.
///
/// This trait is implemented for [`CSort`] and [`CTerm`], both using
/// [`Cvc5Env`] as the environment:
///
/// | cvc5 type   | Environment   | Output   |
/// |-------------|---------------|----------|
/// | [`CSort`]   | [`Cvc5Env`]   | [`Sort`] |
/// | [`CTerm`]   | [`Cvc5Env`]   | [`Term`] |
///
/// Translation may fail if the cvc5 object uses features not supported by yaspar-ir
/// (e.g. floating-point sorts, set operations).
pub trait ConvertFromCvc5<Env> {
    /// The yaspar-ir type produced by the translation.
    type Output;
    /// Translate `self` into a yaspar-ir object, using `env` for allocation and scope tracking.
    fn conv_from_cvc5(&self, env: &mut Env) -> Res<Self::Output>;
}

/// A translated cvc5 term together with any `:pattern` annotations collected during traversal.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct WithPattern<'tm> {
    /// The translated cvc5 term.
    term: CTerm<'tm>,
    /// Pattern terms collected from `:pattern` annotations (empty when none are present).
    ///
    /// Multiple `:pattern`s are maintained.
    patterns: Vec<Vec<CTerm<'tm>>>,
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

/// Cached sort-parameter substitution for parametric datatypes.
///
/// When translating `match` expressions over parametric datatypes, selector codomain sorts
/// are uninstantiated (e.g. the sort parameter `X`). This substitution maps sort parameters
/// to their concrete instantiations so that bound variables receive the correct sorts.
/// `None` for monomorphic datatypes.
type SortSubst<'tm> = Option<(Vec<CSort<'tm>>, Vec<CSort<'tm>>)>;

/// The unified environment for bidirectional translation between yaspar-ir and cvc5.
///
/// This struct holds the [`TermManager`] reference, a [`Context`] handle (any
/// `Ctx: HasMutRef<Context>`, e.g. `&mut Context` or `Rc<RefCell<Context>>`), and all
/// translation state for both directions:
///
/// - **Shared**: bidirectional [`BiHashMap`] caches for sorts and terms, plus a `CTerm →
///   :named` table for recovering SMT-LIB labels in command results.
/// - **Forward (yaspar-ir → cvc5)**: global and local symbol tables, datatype
///   bookkeeping, scope stacks, and parametric-match substitutions.
/// - **Backward (cvc5 → yaspar-ir)**: scoped variable bindings keyed by cvc5 ids and
///   tracking of uninterpreted sort values.
///
/// # Construction
///
/// ```rust
/// use cvc5::TermManager;
/// use yaspar_ir::ast::Context;
/// use yaspar_ir::cvc5::Cvc5Env;
///
/// let tm = TermManager::new();
/// let mut ctx = Context::new();
/// let mut env = Cvc5Env::new(&tm, &mut ctx);
/// ```
pub struct Cvc5Env<'tm, Ctx> {
    // ── Shared (used by both forward and reverse translation) ────────────
    /// The cvc5 term manager that owns all created sorts and terms.
    tm: &'tm TermManager,
    /// The backing yaspar-ir context, used during reverse translation for arena
    /// allocation and theory-aware constant construction.
    ctx: Ctx,
    /// Bidirectional cache between yaspar-ir [`Sort`] and translated [`CSort`].
    /// Used for both forward and reverse sort translation.
    sort_cache: BiHashMap<Sort, CSort<'tm>>,
    /// Bidirectional cache between yaspar-ir [`Term`] and translated [`WithPattern`].
    /// Used for forward memoization and reverse term lookup.
    term_cache: BiHashMap<Term, WithPattern<'tm>>,
    /// Reverse map from a translated assertion's [`CTerm`] back to the SMT-LIB `:named`
    /// label(s) declared on its enclosing `(assert (! ... :named X))` form. Populated
    /// during forward translation of `assert` commands and consulted during reverse
    /// translation of cvc5-returned terms (e.g. `get-unsat-core`).
    named_assertions: HashMap<CTerm<'tm>, Str>,

    // ── Forward direction (yaspar-ir → cvc5) ─────────────────────────────
    /// Named sorts registered by `declare-sort` or datatype declarations.
    sort: HashMap<Str, CSort<'tm>>,
    /// Global symbols (constants, functions, constructors, selectors, testers).
    globals: HashMap<Str, CTerm<'tm>>,
    /// Datatype sorts mapping from names to their corresponding potentially polymorphic representations.
    dt_sorts: HashMap<Str, CSort<'tm>>,
    /// Forward-direction local (bound) variables, keyed by their yaspar-ir local id.
    locals: HashMap<usize, WithPattern<'tm>>,
    /// Stack of bound-variable lists for scope management in quantifiers and match arms (forward direction).
    scope_stack: Vec<Vec<CTerm<'tm>>>,
    /// Cached sort-parameter substitutions for parametric datatype match translation.
    sort_subst_map: HashMap<Term, SortSubst<'tm>>,

    // ── Reverse direction (cvc5 → yaspar-ir) ─────────────────────────────
    /// Backward-direction bound variable map: cvc5 term id → VarBinding.
    locals_from: HashMap<u64, VarBinding<Str, Sort>>,
    /// Stack of bound variable cvc5 ids for scope cleanup (backward direction).
    scope_stack_from: Vec<Vec<u64>>,
    /// Allocated symbols for uninterpreted sort values encountered during reverse translation.
    uninterpreted_values: HashSet<Str>,
}

impl<'tm, Ctx> Cvc5Env<'tm, Ctx>
where
    Ctx: HasMutRef<Context>,
{
    /// Create a new translation environment backed by the given [`TermManager`] and [`Context`].
    pub fn new(tm: &'tm TermManager, ctx: Ctx) -> Self {
        Self {
            tm,
            ctx,
            sort_cache: BiHashMap::new(),
            term_cache: BiHashMap::new(),
            named_assertions: HashMap::new(),
            sort: HashMap::new(),
            globals: HashMap::new(),
            dt_sorts: HashMap::new(),
            locals: HashMap::new(),
            scope_stack: vec![],
            sort_subst_map: Default::default(),
            locals_from: HashMap::new(),
            scope_stack_from: Vec::new(),
            uninterpreted_values: HashSet::new(),
        }
    }

    /// Returns whether the given symbol is an uninterpreted sort value.
    pub fn check_uninterpreted_value<S: AllocatableString<Arena>>(&mut self, name: S) -> bool {
        let sym = name.allocate(self.ctx.ref_mut().arena());
        self.uninterpreted_values.contains(&sym)
    }

    /// Backward-translate a list of cvc5 terms, substituting any `:named` label
    /// recorded for an asserted formula in place of that formula's translation.
    fn conv_terms_with_names(&mut self, cts: &[CTerm<'tm>]) -> Res<Vec<Term>> {
        cts.iter()
            .map(|ct| {
                if let Some(name) = self.named_assertions.get(ct).cloned() {
                    let mut rf = self.ctx.ref_mut();
                    let bool_sort = rf.bool_sort();
                    let qid = QualifiedIdentifier::simple(name);
                    Ok(rf.global(qid, Some(bool_sort)))
                } else {
                    ct.conv_from_cvc5(self)
                }
            })
            .collect()
    }
}

impl<'tm, Ctx> Cvc5Env<'tm, Ctx> {
    /// Returns the set of uninterpreted sort value names encountered.
    pub fn uninterpreted_values(&self) -> &HashSet<Str> {
        &self.uninterpreted_values
    }

    /// Push a new scope with the given cvc5 variable IDs (backward direction).
    fn push_scope_from(&mut self, ids: Vec<u64>) {
        self.scope_stack_from.push(ids);
    }

    /// Pop the current scope and remove all its bindings from `locals_from` (backward direction).
    fn pop_scope_from(&mut self) -> Vec<VarBinding<Str, Sort>> {
        let scope_ids = self
            .scope_stack_from
            .pop()
            .expect("fatal error: unbalanced scope stack!");
        scope_ids
            .iter()
            .filter_map(|id| self.locals_from.remove(id))
            .collect()
    }
}

// `BiHashMap` is treated as a left-keyed mapping for memoization purposes:
// `lookup` finds the right value by left key, and `insert` populates the bijection
// in both directions.
impl<L, R> Mapping for BiHashMap<L, R>
where
    L: Eq + std::hash::Hash,
    R: Eq + std::hash::Hash + Clone,
{
    type Key = L;
    type Value = R;

    fn lookup(&self, key: &Self::Key) -> Option<Self::Value> {
        self.get_by_left(key).cloned()
    }
}

impl<L, R> InsertableMapping for BiHashMap<L, R>
where
    L: Eq + std::hash::Hash,
    R: Eq + std::hash::Hash + Clone,
{
    fn insert(&mut self, key: Self::Key, value: Self::Value) {
        BiHashMap::insert(self, key, value);
    }
}

impl<'tm, Ctx> Memoizing<Term, WithPattern<'tm>> for Cvc5Env<'tm, Ctx> {
    type Cache<'a>
        = &'a mut BiHashMap<Term, WithPattern<'tm>>
    where
        Self: 'a;

    fn cache_mut(&mut self) -> Self::Cache<'_> {
        &mut self.term_cache
    }
}

/// Environment combining a [`Cvc5Env`] with a [`Solver`] for translating commands.
///
/// Commands like `assert`, `check-sat`, `define-fun`, and `declare-datatypes` need
/// access to both the translation environment (for sort/term translation) and the
/// solver (for issuing solver calls). This struct bundles the two together.
///
/// # Example
///
/// ```rust
/// use cvc5::{Solver, TermManager};
/// use yaspar_ir::ast::Context;
/// use yaspar_ir::cvc5::{Cvc5Env, Cvc5EnvSolver};
///
/// let tm = TermManager::new();
/// let mut ctx = Context::new();
/// let mut solver = Solver::new(&tm);
/// let mut env = Cvc5Env::new(&tm, &mut ctx);
/// let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
/// // now use es.to_cvc5() on Command values
/// ```
pub struct Cvc5EnvSolver<'a, 'tm, Ctx> {
    /// The translation environment for sorts and terms.
    pub env: &'a mut Cvc5Env<'tm, Ctx>,
    /// The cvc5 solver instance.
    pub solver: &'a mut Solver<'tm>,
}

impl<'a, 'tm, Ctx> Cvc5EnvSolver<'a, 'tm, Ctx> {
    /// Create a new command-translation environment from a [`Cvc5Env`] and a [`Solver`].
    pub fn new(env: &'a mut Cvc5Env<'tm, Ctx>, solver: &'a mut Solver<'tm>) -> Self {
        Self { env, solver }
    }
}

// ── Sort translation ─────────────────────────────────────────
impl<'tm, Ctx> ConvertToCvc5<Cvc5Env<'tm, Ctx>> for Sort {
    type Output = CSort<'tm>;

    fn to_cvc5(&self, env: &mut Cvc5Env<'tm, Ctx>) -> Res<CSort<'tm>> {
        if let Some(cs) = env.sort_cache.get_by_left(self) {
            return Ok(cs.clone());
        }
        let cs = translate_sort_inner(self, env)?;
        env.sort_cache.insert(self.clone(), cs.clone());
        Ok(cs)
    }
}

fn translate_sort_inner<'tm, Ctx>(sort: &Sort, env: &mut Cvc5Env<'tm, Ctx>) -> Res<CSort<'tm>> {
    let s = sort.repr();
    let name = s.sort_name();
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

// ── Reverse sort translation (CSort → Sort) ─────────────────

impl<'tm, Ctx> ConvertFromCvc5<Cvc5Env<'tm, Ctx>> for CSort<'tm>
where
    Ctx: HasMutRef<Context>,
{
    type Output = Sort;

    fn conv_from_cvc5(&self, fenv: &mut Cvc5Env<'tm, Ctx>) -> Res<Sort> {
        if let Some(s) = fenv.sort_cache.get_by_right(self) {
            return Ok(s.clone());
        }
        let s = translate_sort_from_cvc5(self, fenv)?;
        fenv.sort_cache.insert(s.clone(), self.clone());
        Ok(s)
    }
}

fn translate_sort_from_cvc5<'tm, Ctx>(cs: &CSort<'tm>, fenv: &mut Cvc5Env<'tm, Ctx>) -> Res<Sort>
where
    Ctx: HasMutRef<Context>,
{
    if cs.is_boolean() {
        return Ok(fenv.ctx.ref_mut().bool_sort());
    }
    if cs.is_integer() {
        return Ok(fenv.ctx.ref_mut().int_sort());
    }
    if cs.is_real() {
        return Ok(fenv.ctx.ref_mut().real_sort());
    }
    if cs.is_string() {
        return Ok(fenv.ctx.ref_mut().string_sort());
    }
    if cs.is_regexp() {
        return Ok(fenv.ctx.ref_mut().reglan_sort());
    }
    if cs.is_bv() {
        return Ok(fenv.ctx.ref_mut().bv_sort(cs.bv_size().into()));
    }
    if cs.is_array() {
        let idx = cs.array_index_sort().conv_from_cvc5(fenv)?;
        let elem = cs.array_element_sort().conv_from_cvc5(fenv)?;
        return Ok(fenv.ctx.ref_mut().array_sort(idx, elem));
    }
    // Instantiated parametric datatype (e.g. (List Int))
    if cs.is_dt() && cs.is_instantiated() {
        let dt = cs.datatype();
        let name = dt.name();
        let params = cs.instantiated_parameters();
        let ir_params: Vec<Sort> = params.conv_from_cvc5(fenv)?;
        let mut rf = fenv.ctx.ref_mut();
        let sym = rf.allocate_symbol(name);
        return Ok(rf.sort_n(sym, ir_params));
    }
    // Monomorphic datatype sort
    if cs.is_dt() {
        let dt = cs.datatype();
        let name = dt.name();
        return Ok(fenv.ctx.ref_mut().simple_sort(name));
    }
    // Instantiated parametric uninterpreted sort (e.g. (Pair A B))
    if cs.is_instantiated() {
        let base = cs.uninterpreted_sort_constructor();
        let name = base.symbol();
        let params = cs.instantiated_parameters();
        let ir_params: Vec<Sort> = params
            .iter()
            .map(|p| p.conv_from_cvc5(fenv))
            .collect::<Res<_>>()?;
        let mut rf = fenv.ctx.ref_mut();
        let sym = rf.allocate_symbol(name);
        return Ok(rf.sort_n(sym, ir_params));
    }
    // Uninterpreted sort
    if cs.is_uninterpreted_sort() {
        let name = cs.symbol();
        return Ok(fenv.ctx.ref_mut().simple_sort(name));
    }
    Err(format!("unsupported cvc5 sort: {cs}"))
}

// ── Term: cvc5 → yaspar-ir ───────────────────────────────────

impl<'tm, Ctx, T> ConvertFromCvc5<Cvc5Env<'tm, Ctx>> for [T]
where
    T: ConvertFromCvc5<Cvc5Env<'tm, Ctx>>,
{
    type Output = Vec<T::Output>;

    fn conv_from_cvc5(&self, env: &mut Cvc5Env<'tm, Ctx>) -> Res<Self::Output> {
        self.iter().map(|s| s.conv_from_cvc5(env)).collect()
    }
}

impl<'tm, Ctx> ConvertFromCvc5<Cvc5Env<'tm, Ctx>> for CTerm<'tm>
where
    Ctx: HasMutRef<Context>,
{
    type Output = Term;

    fn conv_from_cvc5(&self, fenv: &mut Cvc5Env<'tm, Ctx>) -> Res<Term> {
        // Reverse lookup: a plain CTerm corresponds to a `WithPattern` with empty
        // patterns (the quantifier case never reaches us as a standalone CTerm).
        let key = WithPattern::from(self.clone());
        if let Some(t) = fenv.term_cache.get_by_right(&key) {
            return Ok(t.clone());
        }
        let t = translate_term_from_cvc5(self, fenv)?;
        fenv.term_cache.insert(t.clone(), key);
        Ok(t)
    }
}

fn translate_term_from_cvc5<'tm, Ctx>(ct: &CTerm<'tm>, fenv: &mut Cvc5Env<'tm, Ctx>) -> Res<Term>
where
    Ctx: HasMutRef<Context>,
{
    let kind = ct.kind();

    // ── Constants ────────────────────────────────────────────
    if ct.is_boolean_value() {
        let mut rf = fenv.ctx.ref_mut();
        let sort = Some(rf.bool_sort());
        return Ok(rf.allocate_term(ATerm::Constant(Constant::Bool(ct.boolean_value()), sort)));
    }
    if ct.is_integer_value() {
        let sort = ct.sort().conv_from_cvc5(fenv)?;
        let n: UBig = ct
            .integer_value()
            .parse()
            .map_err(|e| format!("Big integer parse error: {e}"))?;
        return Ok(fenv
            .ctx
            .ref_mut()
            .allocate_term(ATerm::Constant(Constant::Numeral(n), Some(sort))));
    }
    if ct.is_real_value() {
        let sort = ct.sort().conv_from_cvc5(fenv)?;
        let s = ct.real_value();
        let mut rf = fenv.ctx.ref_mut();
        let has_ints = rf.get_theories().iter().any(|t| t.has_int());
        // cvc5 returns rationals as "num/den" or just "num"
        if let Some((num_s, den_s)) = s.split_once('/') {
            let (numer, denom) = if has_ints {
                // In RealInts, numerals are Int; use Decimal constants for Real division
                let n = Constant::Decimal(format!("{num_s}.0").parse().unwrap());
                let d = Constant::Decimal(format!("{den_s}.0").parse().unwrap());
                let numer = rf.allocate_term(ATerm::Constant(n, Some(sort.clone())));
                let denom = rf.allocate_term(ATerm::Constant(d, Some(sort.clone())));
                (numer, denom)
            } else {
                let num: UBig = num_s.parse().map_err(|e| format!("{e}"))?;
                let den: UBig = den_s.parse().map_err(|e| format!("{e}"))?;
                let int = rf.int_sort();
                let numer =
                    rf.allocate_term(ATerm::Constant(Constant::Numeral(num), Some(int.clone())));
                let denom = rf.allocate_term(ATerm::Constant(Constant::Numeral(den), Some(int)));
                (numer, denom)
            };
            let sym = rf.allocate_symbol(RDIV);
            let qid = QualifiedIdentifier::simple(sym);
            return Ok(rf.app(qid, vec![numer, denom], Some(sort)));
        }
        // No division — parse as a single decimal
        let n: dashu::float::DBig = format!("{s}.0").parse().map_err(|e| format!("{e}"))?;
        return Ok(rf.allocate_term(ATerm::Constant(Constant::Decimal(n), Some(sort))));
    }
    if ct.is_string_value() {
        let sort = ct.sort().conv_from_cvc5(fenv)?;
        let chars = ct.u32string_value();
        let s: String = chars
            .iter()
            .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
            .collect();

        let mut rf = fenv.ctx.ref_mut();
        let str_val = rf.allocate_str(&s);
        return Ok(rf.allocate_term(ATerm::Constant(Constant::String(str_val), Some(sort))));
    }
    if ct.is_bv_value() {
        let sort = ct.sort().conv_from_cvc5(fenv)?;
        let bits = ct.bv_value(2);
        let (bytes, len) = match UntypedAst
            .parse_term_str(&format!("#b{bits}"))
            .map_err(|e| format!("{e}"))?
            .repr()
        {
            ATerm::Constant(alg::Constant::Binary(bytes, len), _) => (bytes.clone(), *len),
            _ => return Err(format!("bit vector literal {bits} cannot be parsed!")),
        };

        return Ok(fenv
            .ctx
            .ref_mut()
            .allocate_term(ATerm::Constant(Constant::Binary(bytes, len), Some(sort))));
    }

    // ── Logical connectives ─────────────────────────────────
    match kind {
        Kind::And => {
            let children = translate_children(ct, fenv)?;
            return Ok(fenv.ctx.ref_mut().and(children));
        }
        Kind::Or => {
            let children = translate_children(ct, fenv)?;
            return Ok(fenv.ctx.ref_mut().or(children));
        }
        Kind::Xor => {
            let children = translate_children(ct, fenv)?;
            return Ok(fenv.ctx.ref_mut().xor(children));
        }
        Kind::Not => {
            let child = ct.child(0).conv_from_cvc5(fenv)?;
            return Ok(fenv.ctx.ref_mut().not(child));
        }
        Kind::Implies => {
            let n = ct.num_children();
            let mut premises = Vec::with_capacity(n - 1);
            for i in 0..n - 1 {
                premises.push(ct.child(i).conv_from_cvc5(fenv)?);
            }
            let concl = ct.child(n - 1).conv_from_cvc5(fenv)?;

            return Ok(fenv.ctx.ref_mut().implies(premises, concl));
        }
        Kind::Equal => {
            let children = translate_children(ct, fenv)?;
            let mut rf = fenv.ctx.ref_mut();

            if children.len() == 2 {
                return Ok(rf.eq(children[0].clone(), children[1].clone()));
            }
            // Chain: (= a b c) → (and (= a b) (= b c))
            let mut eqs = Vec::with_capacity(children.len() - 1);
            for i in 0..children.len() - 1 {
                eqs.push(rf.eq(children[i].clone(), children[i + 1].clone()));
            }
            return Ok(rf.and(eqs));
        }
        Kind::Distinct => {
            let children = translate_children(ct, fenv)?;

            return Ok(fenv.ctx.ref_mut().distinct(children));
        }
        Kind::Ite => {
            let b = ct.child(0).conv_from_cvc5(fenv)?;
            let t = ct.child(1).conv_from_cvc5(fenv)?;
            let e = ct.child(2).conv_from_cvc5(fenv)?;

            return Ok(fenv.ctx.ref_mut().ite(b, t, e));
        }
        // ── Quantifiers ─────────────────────────────────────────
        Kind::Forall | Kind::Exists => {
            let vlist = ct.child(0);
            let body_ct = ct.child(1);
            let mut scope_ids = Vec::new();
            for i in 0..vlist.num_children() {
                let v = vlist.child(i);
                let cvc5_id = v.id();
                let name = v.symbol().to_string();
                let vs = v.sort().conv_from_cvc5(fenv)?;

                let mut rf = fenv.ctx.ref_mut();
                let id = rf.new_local();
                let sym = rf.allocate_symbol(&name);
                fenv.locals_from.insert(cvc5_id, VarBinding(sym, id, vs));
                scope_ids.push(cvc5_id);
            }
            fenv.push_scope_from(scope_ids);

            // Collect cvc5 patterns first (without translating to ir Terms yet).
            // This lets us probe the bimap with `WithPattern { body_ct, cvc5_patterns }`
            // on the right side and short-circuit body translation on a hit.
            let cvc5_patterns: Vec<Vec<CTerm<'tm>>> = if ct.num_children() > 2 {
                let plist = ct.child(2);
                let mut pats = Vec::with_capacity(plist.num_children());
                for i in 0..plist.num_children() {
                    let pat = plist.child(i);
                    if pat.kind() == Kind::InstPattern {
                        let mut pat_cterms = Vec::with_capacity(pat.num_children());
                        for j in 0..pat.num_children() {
                            pat_cterms.push(pat.child(j));
                        }
                        pats.push(pat_cterms);
                    }
                }
                pats
            } else {
                vec![]
            };

            let result = 'inner: {
                let probe = WithPattern {
                    term: body_ct.clone(),
                    patterns: cvc5_patterns.clone(),
                };
                if let Some(cached) = fenv.term_cache.get_by_right(&probe) {
                    break 'inner Ok(cached.clone());
                }
                body_ct.conv_from_cvc5(fenv).and_then(|body| {
                    if cvc5_patterns.is_empty() {
                        return Ok(body);
                    }
                    let attrs = cvc5_patterns
                        .iter()
                        .map(|pats| {
                            Ok(Attribute::Pattern(
                                pats.iter()
                                    .map(|t| t.conv_from_cvc5(fenv))
                                    .collect::<Res<Vec<_>>>()?,
                            ))
                        })
                        .collect::<Res<Vec<_>>>()?;
                    let annotated = fenv.ctx.ref_mut().annotated(body, attrs);
                    // Mirror the forward-direction shape: `Annotated(body, [:pattern …])`
                    // maps to a `WithPattern` whose `term` is the body's CTerm and whose
                    // `patterns` carry the pattern triggers (later absorbed into
                    // `INST_PATTERN_LIST`).
                    fenv.term_cache.insert(annotated.clone(), probe);
                    Ok(annotated)
                })
            };

            let bindings = fenv.pop_scope_from();
            let body = result?;

            return if kind == Kind::Forall {
                Ok(fenv.ctx.ref_mut().forall(bindings, body))
            } else {
                Ok(fenv.ctx.ref_mut().exists(bindings, body))
            };
        }
        // ── Negation (unary minus) ──────────────────────────────
        Kind::Neg => {
            let child = ct.child(0).conv_from_cvc5(fenv)?;
            let sort = ct.sort().conv_from_cvc5(fenv)?;

            let mut rf = fenv.ctx.ref_mut();
            let sym = rf.allocate_symbol(SUB);
            let qid = QualifiedIdentifier::simple(sym);
            return Ok(rf.app(qid, vec![child], Some(sort)));
        }

        // ── Function application (UF, constructors, selectors, testers) ──
        Kind::Constant => {
            // Uninterpreted constant (declared symbol)
            let name = ct.symbol().to_string();
            let sort = ct.sort().conv_from_cvc5(fenv)?;

            let mut rf = fenv.ctx.ref_mut();
            let sym = rf.allocate_symbol(&name);
            let qid = QualifiedIdentifier::simple(sym);
            return Ok(rf.global(qid, Some(sort)));
        }
        Kind::ApplyUf => {
            let head = ct.child(0);
            let name = head.symbol().to_string();
            let mut args = Vec::with_capacity(ct.num_children() - 1);
            for i in 1..ct.num_children() {
                args.push(ct.child(i).conv_from_cvc5(fenv)?);
            }
            let sort = ct.sort().conv_from_cvc5(fenv)?;

            let mut rf = fenv.ctx.ref_mut();
            let sym = rf.allocate_symbol(&name);
            let qid = QualifiedIdentifier::simple(sym);
            return Ok(rf.app(qid, args, Some(sort)));
        }
        Kind::ApplyConstructor => {
            let head = ct.child(0);
            let name = if head.has_symbol() {
                head.symbol().to_string()
            } else {
                // Parametric constructor: get name from the sort's datatype
                let dt = ct.sort().datatype();
                let mut found = false;
                let mut name = String::new();
                for i in 0..dt.num_constructors() {
                    let ctor = dt.constructor(i);
                    if ctor.term() == head || ctor.num_selectors() == ct.num_children() - 1 {
                        name = ctor.name().to_string();
                        found = true;
                        break;
                    }
                }
                if !found {
                    return Err(format!(
                        "fatal error: term {head} cannot find a case for its datatype {dt}!"
                    ));
                }
                name
            };
            let n = ct.num_children();
            if n == 1 {
                // Nullary constructor → global
                let sort = ct.sort().conv_from_cvc5(fenv)?;

                let mut rf = fenv.ctx.ref_mut();
                let sym = rf.allocate_symbol(&name);
                let qid = if ct.sort().is_dt() && ct.sort().datatype().is_parametric() {
                    QualifiedIdentifier::simple_sorted(sym, sort.clone())
                } else {
                    QualifiedIdentifier::simple(sym)
                };
                return Ok(rf.global(qid, Some(sort)));
            }
            let mut args = Vec::with_capacity(n - 1);
            for i in 1..n {
                args.push(ct.child(i).conv_from_cvc5(fenv)?);
            }
            let sort = ct.sort().conv_from_cvc5(fenv)?;

            let mut rf = fenv.ctx.ref_mut();
            let sym = rf.allocate_symbol(&name);
            let qid = QualifiedIdentifier::simple(sym);
            return Ok(rf.app(qid, args, Some(sort)));
        }
        Kind::ApplySelector => {
            let head = ct.child(0);
            let name = if head.has_symbol() {
                head.symbol().to_string()
            } else {
                format!("{head}")
            };
            let arg = ct.child(1).conv_from_cvc5(fenv)?;
            let sort = ct.sort().conv_from_cvc5(fenv)?;

            let mut rf = fenv.ctx.ref_mut();
            let sym = rf.allocate_symbol(&name);
            let qid = QualifiedIdentifier::simple(sym);
            return Ok(rf.app(qid, vec![arg], Some(sort)));
        }
        Kind::ApplyTester => {
            let head = ct.child(0);
            let tester_name = if head.has_symbol() {
                head.symbol().to_string()
            } else {
                format!("{head}")
            };
            // cvc5 tester names are "is_<ctor>"; extract the constructor name
            let ctor_name = tester_name.strip_prefix("is_").unwrap_or(&tester_name);
            let arg = ct.child(1).conv_from_cvc5(fenv)?;
            let sort = ct.sort().conv_from_cvc5(fenv)?;

            let mut rf = fenv.ctx.ref_mut();
            let is_sym = rf.allocate_symbol(IS);
            let ctor_sym = rf.allocate_symbol(ctor_name);
            let id = alg::Identifier {
                symbol: is_sym,
                indices: vec![Index::Symbol(ctor_sym)],
            };
            let qid = QualifiedIdentifier::from(id);
            return Ok(rf.app(qid, vec![arg], Some(sort)));
        }

        // ── Variable (bound) ────────────────────────────────────
        Kind::Variable => {
            let cvc5_id = ct.id();
            if let Some(vb) = fenv.locals_from.get(&cvc5_id) {
                return Ok(fenv.ctx.ref_mut().local(alg::Local {
                    id: vb.1,
                    symbol: vb.0.clone(),
                    sort: vb.2.clone(),
                }));
            }
            return Err(format!(
                "unexpected and fatal scope management error: local variable {ct} is not bound!"
            ));
        }
        // ── Nullary regexp constants ───────────────────────────────
        Kind::RegexpNone | Kind::RegexpAll | Kind::RegexpAllchar => {
            let ik = cvc5_kind_to_ident_kind(kind).unwrap();
            let sort = ct.sort().conv_from_cvc5(fenv)?;

            let mut rf = fenv.ctx.ref_mut();
            let sym = rf.allocate_symbol(ik.name());
            let qid = QualifiedIdentifier::simple(sym);
            return Ok(rf.global(qid, Some(sort)));
        }

        // ── BitvectorToNat ──────────────────────────────────────
        Kind::BitvectorToNat => {
            let child = ct.child(0).conv_from_cvc5(fenv)?;
            let sort = ct.sort().conv_from_cvc5(fenv)?;

            let mut rf = fenv.ctx.ref_mut();
            let sym = rf.allocate_symbol(BV2NAT);
            let qid = QualifiedIdentifier::simple(sym);
            return Ok(rf.app(qid, vec![child], Some(sort)));
        }

        // ── Match expressions ───────────────────────────────────
        Kind::Match => {
            let scrutinee = ct.child(0).conv_from_cvc5(fenv)?;
            let n = ct.num_children();
            let mut arms = Vec::with_capacity(n - 1);
            for i in 1..n {
                let case = ct.child(i);
                let arm = translate_match_case_from_cvc5(&case, fenv)?;
                arms.push(arm);
            }

            return Ok(fenv.ctx.ref_mut().matching(scrutinee, arms));
        }
        // ── Const array ──────────────────────────────────────────
        Kind::ConstArray => {
            let value = ct.const_array_base().conv_from_cvc5(fenv)?;
            let arr_sort = ct.sort().conv_from_cvc5(fenv)?;
            let mut rf = fenv.ctx.ref_mut();
            let sym = rf.allocate_symbol(CONST);
            let qid = QualifiedIdentifier::simple_sorted(sym, arr_sort.clone());
            return Ok(rf.app(qid, vec![value], Some(arr_sort)));
        }

        // ── Uninterpreted sort value (from models) ──────────────
        Kind::UninterpretedSortValue => {
            let name = ct.uninterpreted_sort_value();
            let sort = ct.sort().conv_from_cvc5(fenv)?;
            let mut rf = fenv.ctx.ref_mut();
            let sym = rf.allocate_symbol(&name);
            fenv.uninterpreted_values.insert(sym.clone());
            let qid = QualifiedIdentifier::simple(sym);
            return Ok(rf.global(qid, Some(sort)));
        }

        // ── Lambda ──────────────────────────────────────────────
        Kind::Lambda => return Err("higher order functions are not supported!".into()),

        // ── Sequences ───────────────────────────────────────────
        Kind::ConstSequence => return Err("sequence operations are not supported!".into()),

        // ── Sets ────────────────────────────────────────────────
        Kind::SetEmpty
        | Kind::SetUniverse
        | Kind::SetSingleton
        | Kind::SetUnion
        | Kind::SetInter
        | Kind::SetMinus
        | Kind::SetMember
        | Kind::SetSubset
        | Kind::SetComplement
        | Kind::SetInsert
        | Kind::SetCard => {
            return Err("set operations are not supported!".into());
        }

        // ── Floating point ──────────────────────────────────────
        Kind::ConstFloatingpoint | Kind::ConstRoundingmode | Kind::FloatingpointFp => {
            return Err("floating point operations are not supported!".into());
        }

        _ => {}
    }

    // ── Known operator kinds ────────────────────────────────
    if let Some(ik) = cvc5_kind_to_ident_kind(kind) {
        let children = translate_children(ct, fenv)?;
        let sort = ct.sort().conv_from_cvc5(fenv)?;

        let name = ik.name();
        let mut rf = fenv.ctx.ref_mut();
        let sym = rf.allocate_symbol(name);
        let qid = QualifiedIdentifier::simple(sym);
        return Ok(rf.app(qid, children, Some(sort)));
    }

    // ── Indexed operators ───────────────────────────────────
    if ct.has_op() {
        let op = ct.op();
        if let Some(term) = translate_indexed_from_cvc5(ct, &op, fenv)? {
            return Ok(term);
        }
    }

    Err(format!("unsupported cvc5 term kind: {:?}", kind))
}

fn translate_children<'tm, Ctx>(ct: &CTerm<'tm>, fenv: &mut Cvc5Env<'tm, Ctx>) -> Res<Vec<Term>>
where
    Ctx: HasMutRef<Context>,
{
    let n = ct.num_children();
    let mut children = Vec::with_capacity(n);
    for i in 0..n {
        children.push(ct.child(i).conv_from_cvc5(fenv)?);
    }
    Ok(children)
}

fn translate_match_case_from_cvc5<'tm, Ctx>(
    case: &CTerm<'tm>,
    fenv: &mut Cvc5Env<'tm, Ctx>,
) -> Res<alg::PatternArm<Str, Term>>
where
    Ctx: HasMutRef<Context>,
{
    let case_kind = case.kind();
    match case_kind {
        Kind::MatchCase => {
            // Children: [pattern (ApplyConstructor), body]
            let pattern_ct = case.child(0);
            // Nullary constructor: ApplyConstructor with just the ctor term
            let ctor_term = pattern_ct.child(0);
            let ctor_name = if ctor_term.has_symbol() {
                ctor_term.symbol().to_string()
            } else {
                // Parametric constructor: the ctor_term is sort-qualified (e.g. `(as nil (List Int))`).
                // Compare against instantiated constructor terms from the datatype.
                let dt = pattern_ct.sort().datatype();
                let sort = pattern_ct.sort();
                let mut found = false;
                let mut name = String::new();
                for i in 0..dt.num_constructors() {
                    let c = dt.constructor(i);
                    if c.instantiated_term(sort.clone()) == ctor_term {
                        name = c.name().to_string();
                        found = true;
                        break;
                    }
                }
                if !found {
                    return Err(format!(
                        "fatal error: term {ctor_term} cannot find a case for its datatype {dt}!"
                    ));
                }
                name
            };
            let body = case.child(1).conv_from_cvc5(fenv)?;

            let sym = fenv.ctx.ref_mut().allocate_symbol(&ctor_name);
            Ok(alg::PatternArm {
                pattern: Pattern::Ctor(sym),
                body,
            })
        }
        Kind::MatchBindCase => {
            // Children: [variable_list, pattern, body]
            let vlist = case.child(0);
            let pattern_ct = case.child(1);
            let body_ct = case.child(2);

            // Determine if this is a wildcard or an applied constructor pattern
            let pat_kind = pattern_ct.kind();
            if pat_kind == Kind::Variable {
                // Wildcard pattern: pattern is the same variable as in vlist
                let v = vlist.child(0);
                let cvc5_id = v.id();
                let vs = v.sort().conv_from_cvc5(fenv)?;

                if v.has_symbol() {
                    let name = v.symbol().to_string();
                    let mut rf = fenv.ctx.ref_mut();
                    let id = rf.new_local();
                    let sym = rf.allocate_symbol(&name);
                    drop(rf);
                    let vb = VarBinding(sym.clone(), id, vs);
                    fenv.locals_from.insert(cvc5_id, vb);
                    fenv.push_scope_from(vec![cvc5_id]);

                    let result = body_ct.conv_from_cvc5(fenv);
                    fenv.pop_scope_from();
                    let body = result?;
                    Ok(alg::PatternArm {
                        pattern: Pattern::Wildcard(Some((sym, id))),
                        body,
                    })
                } else {
                    // Anonymous wildcard — no variable binding
                    let body = body_ct.conv_from_cvc5(fenv)?;
                    Ok(alg::PatternArm {
                        pattern: Pattern::Wildcard(None),
                        body,
                    })
                }
            } else {
                // Applied constructor pattern: pattern is ApplyConstructor
                let ctor_term = pattern_ct.child(0);
                let ctor_name = if ctor_term.has_symbol() {
                    ctor_term.symbol().to_string()
                } else {
                    format!("{ctor_term}")
                };
                let num_args = pattern_ct.num_children() - 1;

                let mut scope_ids = Vec::new();
                let mut arguments = Vec::with_capacity(num_args);

                for i in 0..num_args {
                    let arg = pattern_ct.child(i + 1);
                    let cvc5_id = arg.id();
                    scope_ids.push(cvc5_id);
                    if arg.has_symbol() {
                        let name = arg.symbol().to_string();
                        let vs = arg.sort().conv_from_cvc5(fenv)?;
                        let mut rf = fenv.ctx.ref_mut();
                        let id = rf.new_local();
                        let sym = rf.allocate_symbol(&name);
                        fenv.locals_from
                            .insert(cvc5_id, VarBinding(sym.clone(), id, vs));
                        arguments.push(Some((sym, id)));
                    } else {
                        arguments.push(None);
                    }
                }
                fenv.push_scope_from(scope_ids);

                let result = body_ct.conv_from_cvc5(fenv);
                fenv.pop_scope_from();
                let body = result?;

                let ctor_sym = fenv.ctx.ref_mut().allocate_symbol(&ctor_name);
                Ok(alg::PatternArm {
                    pattern: Pattern::Applied {
                        ctor: ctor_sym,
                        arguments,
                    },
                    body,
                })
            }
        }
        _ => Err(format!("unsupported match case kind: {:?}", case_kind)),
    }
}

fn translate_indexed_from_cvc5<'tm, Ctx>(
    ct: &CTerm<'tm>,
    op: &cvc5::Op<'tm>,
    fenv: &mut Cvc5Env<'tm, Ctx>,
) -> Res<Option<Term>>
where
    Ctx: HasMutRef<Context>,
{
    let op_kind = op.kind();
    let children = translate_children(ct, fenv)?;
    let sort = ct.sort().conv_from_cvc5(fenv)?;

    let idx_ubig = |i: usize| -> Res<UBig> {
        let idx_term = op.index(i);
        idx_term
            .integer_value()
            .parse::<UBig>()
            .map_err(|e| format!("Big integer parse error: {e}"))
    };

    let (name, indices) = match op_kind {
        Kind::BitvectorExtract => (
            BV_EXTRACT,
            vec![Index::Numeral(idx_ubig(0)?), Index::Numeral(idx_ubig(1)?)],
        ),
        Kind::BitvectorRepeat => (BV_REPEAT, vec![Index::Numeral(idx_ubig(0)?)]),
        Kind::BitvectorZeroExtend => (BV_ZERO_EXTEND, vec![Index::Numeral(idx_ubig(0)?)]),
        Kind::BitvectorSignExtend => (BV_SIGN_EXTEND, vec![Index::Numeral(idx_ubig(0)?)]),
        Kind::BitvectorRotateLeft => (BV_ROTATE_LEFT, vec![Index::Numeral(idx_ubig(0)?)]),
        Kind::BitvectorRotateRight => (BV_ROTATE_RIGHT, vec![Index::Numeral(idx_ubig(0)?)]),
        Kind::IntToBitvector => (INT2BV, vec![Index::Numeral(idx_ubig(0)?)]),
        Kind::RegexpRepeat => (RE_POWER, vec![Index::Numeral(idx_ubig(0)?)]),
        Kind::RegexpLoop => (
            RE_LOOP,
            vec![Index::Numeral(idx_ubig(0)?), Index::Numeral(idx_ubig(1)?)],
        ),
        _ => return Ok(None),
    };

    let mut rf = fenv.ctx.ref_mut();
    let sym = rf.allocate_symbol(name);
    let id = alg::Identifier {
        symbol: sym,
        indices,
    };
    let qid = QualifiedIdentifier::from(id);
    Ok(Some(rf.app(qid, children, Some(sort))))
}

/// Reverse mapping from cvc5 Kind to yaspar-ir IdentifierKind.
fn cvc5_kind_to_ident_kind(kind: Kind) -> Option<IdentifierKind> {
    use alg::IdentifierKind::*;
    Some(match kind {
        Kind::Add => Add,
        Kind::Sub => Sub,
        Kind::Mult => Mul,
        Kind::IntsDivision => Idiv,
        Kind::Division => Rdiv,
        Kind::IntsModulus => Mod,
        Kind::Abs => Abs,
        Kind::Leq => Le,
        Kind::Lt => Lt,
        Kind::Geq => Ge,
        Kind::Gt => Gt,
        Kind::ToReal => ToReal,
        Kind::ToInteger => ToInt,
        Kind::IsInteger => IsInt,
        Kind::Select => Select,
        Kind::Store => Store,
        Kind::StringConcat => StrConcat,
        Kind::StringLength => StrLen,
        Kind::StringLt => StrLt,
        Kind::StringLeq => StrLe,
        Kind::StringCharat => StrAt,
        Kind::StringSubstr => StrSubstr,
        Kind::StringPrefix => StrPrefixof,
        Kind::StringSuffix => StrSuffixof,
        Kind::StringContains => StrContains,
        Kind::StringIndexof => StrIndexof,
        Kind::StringReplace => StrReplace,
        Kind::StringReplaceAll => StrReplaceAll,
        Kind::StringReplaceRe => StrReplaceRe,
        Kind::StringReplaceReAll => StrReplaceReAll,
        Kind::StringToRegexp => StrToRe,
        Kind::StringInRegexp => StrInRe,
        Kind::StringIsDigit => StrIsDigit,
        Kind::StringToCode => StrToCode,
        Kind::StringFromCode => StrFromCode,
        Kind::StringToInt => StrToInt,
        Kind::StringFromInt => StrFromInt,
        Kind::RegexpNone => ReNone,
        Kind::RegexpAll => ReAll,
        Kind::RegexpAllchar => ReAllChar,
        Kind::RegexpConcat => ReConcat,
        Kind::RegexpUnion => ReUnion,
        Kind::RegexpInter => ReInter,
        Kind::RegexpStar => ReStar,
        Kind::RegexpComplement => ReComp,
        Kind::RegexpDiff => ReDiff,
        Kind::RegexpPlus => ReAdd,
        Kind::RegexpOpt => ReOpt,
        Kind::RegexpRange => ReRange,
        Kind::BitvectorConcat => Concat,
        Kind::BitvectorNot => BvNot,
        Kind::BitvectorNeg => BvNeg,
        Kind::BitvectorAnd => BvAnd,
        Kind::BitvectorOr => BvOr,
        Kind::BitvectorAdd => BvAdd,
        Kind::BitvectorMult => BvMul,
        Kind::BitvectorUdiv => BvUdiv,
        Kind::BitvectorUrem => BvUrem,
        Kind::BitvectorShl => BvShl,
        Kind::BitvectorLshr => BvLshr,
        Kind::BitvectorUlt => BvUlt,
        Kind::BitvectorNand => BvNand,
        Kind::BitvectorNor => BvNor,
        Kind::BitvectorXor => BvXor,
        Kind::BitvectorXnor => BvNxor,
        Kind::BitvectorComp => BvComp,
        Kind::BitvectorSub => BvSub,
        Kind::BitvectorSdiv => BvSdiv,
        Kind::BitvectorSrem => BvSrem,
        Kind::BitvectorSmod => BvSmod,
        Kind::BitvectorAshr => BvAShr,
        Kind::BitvectorUle => BvUle,
        Kind::BitvectorUgt => BvUgt,
        Kind::BitvectorUge => BvUge,
        Kind::BitvectorSlt => BvSlt,
        Kind::BitvectorSle => BvSle,
        Kind::BitvectorSgt => BvSgt,
        Kind::BitvectorSge => BvSge,
        Kind::BitvectorNego => BvNego,
        Kind::BitvectorUaddo => BvUaddo,
        Kind::BitvectorSaddo => BvSaddo,
        Kind::BitvectorUmulo => BvUmulo,
        Kind::BitvectorSmulo => BvSmulo,
        Kind::BitvectorUbvToInt => UbvToInt,
        Kind::BitvectorSbvToInt => SbvToInt,
        Kind::BitvectorUsubo => BvUsubo,
        Kind::BitvectorSsubo => BvSsubo,
        Kind::BitvectorSdivo => BvSdivo,
        _ => return None,
    })
}

// ── Identifier kind → cvc5 Kind mapping ─────────────────────
fn ident_kind_to_cvc5(k: &IdentifierKind) -> Option<Kind> {
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
impl<'tm, Ctx> ConvertToCvc5<Cvc5Env<'tm, Ctx>> for Term {
    type Output = CTerm<'tm>;

    fn to_cvc5(&self, env: &mut Cvc5Env<'tm, Ctx>) -> Res<Self::Output> {
        let mut wrapped = MemoizedRecursion(env);
        MemoizedScheme::term_recursion(&mut wrapped, self).map(|t| t.into())
    }
}

fn to_term_vec(terms: Vec<WithPattern>) -> Vec<CTerm> {
    terms.into_iter().map(|t| t.into()).collect()
}

impl<'tm, Ctx> TermRecursor<Str, Sort, Term> for Cvc5Env<'tm, Ctx> {
    type Out = WithPattern<'tm>;
    type Attr = Vec<Vec<CTerm<'tm>>>;
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
    fn cleanup_let_scope_on_error(
        &mut self,
        _current: &Term,
        _vs: &[VarBinding<Str, Term>],
        _body: &Term,
        vs_rec: Vec<Self::Binding>,
    ) {
        for (idx, _) in vs_rec {
            self.locals.remove(&idx);
        }
    }

    fn on_let(
        &mut self,
        current: &Term,
        vs: &[VarBinding<Str, Term>],
        body: &Term,
        vs_rec: Vec<Self::Binding>,
        body_rec: WithPattern<'tm>,
    ) -> Res<WithPattern<'tm>> {
        self.cleanup_let_scope_on_error(current, vs, body, vs_rec);
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
    fn cleanup_quantifier_scope_on_error(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Sort>],
        _t: &Term,
        _is_forall: bool,
    ) {
        let _ = self.unbind_vars(vs, |v| &v.1);
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
    fn cleanup_match_case_scope_on_error(
        &mut self,
        _current: &Term,
        _scrutinee: &Term,
        cases: &[alg::PatternArm<Str, Term>],
        _scrutinee_rec: Self::Out,
        case_idx: usize,
    ) {
        let _ = self.unbind_vars(&cases[case_idx].pattern.variables_and_ids(), |v| &v.1);
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
        anns_rec: Vec<Vec<Vec<CTerm<'tm>>>>,
    ) -> Res<WithPattern<'tm>> {
        // do not handle other annotations
        let mut pats = t_rec.patterns;
        anns_rec.into_iter().for_each(|ps| pats.extend(ps));
        Ok(WithPattern {
            term: t_rec.term,
            patterns: pats,
        })
    }
    fn on_attribute_keyword(&mut self, _keyword: &Keyword) -> Res<Vec<Vec<CTerm<'tm>>>> {
        Ok(vec![])
    }
    fn on_attribute_constant(
        &mut self,
        _keyword: &Keyword,
        _constant: &Constant,
    ) -> Res<Vec<Vec<CTerm<'tm>>>> {
        Ok(vec![])
    }
    fn on_attribute_symbol(
        &mut self,
        _keyword: &Keyword,
        _symbol: &Str,
    ) -> Res<Vec<Vec<CTerm<'tm>>>> {
        Ok(vec![])
    }
    fn on_attribute_named(&mut self, _name: &Str) -> Res<Vec<Vec<CTerm<'tm>>>> {
        Ok(vec![])
    }

    fn on_attribute_pattern(
        &mut self,
        _patterns: &[Term],
        patterns_rec: Vec<WithPattern<'tm>>,
    ) -> Res<Vec<Vec<CTerm<'tm>>>> {
        Ok(vec![to_term_vec(patterns_rec)])
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

impl<'tm, Ctx> TypedTermRecursor for Cvc5Env<'tm, Ctx> {}

impl<T, Env, E> ConvertToCvc5<Env> for [T]
where
    T: ConvertToCvc5<Env, Output = E>,
{
    type Output = Vec<E>;

    fn to_cvc5(&self, env: &mut Env) -> Res<Self::Output> {
        self.iter().map(|t| t.to_cvc5(env)).collect()
    }
}

/// Test whether a cvc5 term is a constant
fn is_const(t: &CTerm) -> bool {
    // Built-in value types
    t.is_boolean_value()
        || t.is_integer_value()
        || t.is_real_value()
        || t.is_string_value()
        || t.is_bv_value()
        || t.is_const_array()
        || t.is_ff_value()
        || t.is_uninterpreted_sort_value()
        || t.is_fp_value()
        || t.is_tuple_value()
        || t.is_sequence_value()
        // Datatype constructor with all-const args
        || (t.kind() == Kind::ApplyConstructor
        && (0..t.num_children()).all(|i| is_const(&t.child(i))))
}

impl<'tm, Ctx> Cvc5Env<'tm, Ctx> {
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
        let sort_name = sort.sort_name();
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
        let name = qid.id_str();
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
            Some(ref ik) if let Some(k) = ident_kind_to_cvc5(ik) => {
                Ok(self.tm.mk_term(k, &[]).into())
            }
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
                    if let Some(ct) = self.resolve_parametric_ctor(name.as_str(), sort)? {
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
            let pats = t_rec
                .patterns
                .iter()
                .filter_map(|ts| {
                    if ts.is_empty() {
                        None
                    } else {
                        Some(self.tm.mk_term(Kind::InstPattern, ts))
                    }
                })
                .collect::<Vec<_>>();
            let plist = self.tm.mk_term(Kind::InstPatternList, &pats);
            return Ok(self.tm.mk_term(kind, &[bvl, cbody, plist]).into());
        }
        Ok(self.tm.mk_term(kind, &[bvl, cbody]).into())
    }

    fn translate_app(
        &mut self,
        qid: &QualifiedIdentifier,
        mut cargs: Vec<CTerm<'tm>>,
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
        // Handle const array: ((as const (Array X Y)) v) → ConstArray
        if let Some(IdentifierKind::Const) = kind
            && cargs.len() == 1
        {
            let arr_sort = rs.to_cvc5(self)?;
            let arg = cargs.remove(0);
            //
            if is_const(&arg) {
                return Ok(self.tm.mk_const_array(arr_sort, arg).into());
            } else {
                return Err(format!(
                    "cvc5 kind ConstArray only accepts a constant value but {arg} is given!"
                ));
            }
        }
        if let Some(kind) = kind.as_ref().and_then(ident_kind_to_cvc5) {
            return Ok(self.tm.mk_term(kind, &cargs).into());
        }
        if let Some(ref ik) = kind {
            return self.translate_indexed_app(ik, cargs);
        }
        let name = &id.symbol;
        if let Some(f) = self.globals.get(name).cloned() {
            let fs = f.sort();
            if fs.is_dt_constructor() {
                if let Some(ct) = self.resolve_parametric_ctor(name.as_str(), rs)? {
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
impl<'tm, Ctx> ConvertToCvc5<Cvc5EnvSolver<'_, 'tm, Ctx>> for Command
where
    Ctx: HasMutRef<Context>,
{
    type Output = CommandResult<'tm>;

    fn to_cvc5(&self, es: &mut Cvc5EnvSolver<'_, 'tm, Ctx>) -> Res<Self::Output> {
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
                } else if let Attribute::Constant(kw, c) = attr {
                    solver.set_option(kw.symbol_of(), &c.to_string());
                }
                Ok(CommandResult::None)
            }
            AC::DeclareConst(name, sort) => {
                let cs = sort.to_cvc5(env)?;
                let ct = env.tm.mk_const(cs, name);
                env.globals.insert(name.clone(), ct);
                Ok(CommandResult::None)
            }
            AC::DeclareFun(name, inp, out) => {
                let co = out.to_cvc5(env)?;
                if inp.is_empty() {
                    let ct = env.tm.mk_const(co, name);
                    env.globals.insert(name.clone(), ct);
                } else {
                    let ci = inp.to_cvc5(env)?;
                    let fs = env.tm.mk_fun_sort(&ci, co);
                    let ct = env.tm.mk_const(fs, name);
                    env.globals.insert(name.clone(), ct);
                }
                Ok(CommandResult::None)
            }
            AC::DeclareSort(name, arity) => {
                let cs = if *arity == 0 {
                    env.tm.mk_uninterpreted_sort(name)
                } else {
                    env.tm.mk_uninterpreted_sort_constructor_sort(*arity, name)
                };
                env.sort.insert(name.clone(), cs);
                Ok(CommandResult::None)
            }
            AC::DefineSort(..) => {
                // we don't need to do anything. typechecking will unfold all defined sorts
                Ok(CommandResult::None)
            }
            AC::DefineConst(name, _sort, body) => {
                let cbody = body.to_cvc5(env)?;
                env.globals.insert(name.clone(), cbody);
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
                    env.globals.insert(name.clone(), ct.clone());
                    env.named_assertions.insert(ct.clone(), name);
                }
                solver.assert_formula(ct);
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
                let ts: Vec<Term> = vals.as_slice().conv_from_cvc5(env)?;
                Ok(CommandResult::GetValue(ts))
            }
            AC::GetModel => {
                let sorts = env
                    .sort
                    .values()
                    .filter(|s| s.is_uninterpreted_sort())
                    .cloned()
                    .chain(
                        env.sort_cache
                            .right_values()
                            .filter(|s| s.is_uninterpreted_sort())
                            .cloned(),
                    )
                    .collect::<Vec<CSort>>();
                let consts = env
                    .globals
                    .values()
                    .filter(|t| t.kind() == Kind::Constant)
                    .cloned()
                    .collect::<Vec<CTerm>>();

                let m = solver.get_model(&sorts, &consts);
                Ok(CommandResult::GetModel(m))
            }
            AC::GetAssertions => {
                let cts = solver.get_assertions();
                let ts = env.conv_terms_with_names(&cts)?;
                Ok(CommandResult::Terms(ts))
            }
            AC::GetUnsatCore => {
                let cts = solver.get_unsat_core();
                let ts = env.conv_terms_with_names(&cts)?;
                Ok(CommandResult::Terms(ts))
            }
            AC::GetUnsatAssumptions => {
                let cts = solver.get_unsat_assumptions();
                let ts = env.conv_terms_with_names(&cts)?;
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
impl<'tm, Ctx> Cvc5EnvSolver<'_, 'tm, Ctx>
where
    Ctx: HasMutRef<Context>,
{
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
        self.env.globals.insert(fd.name.clone(), ct);
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
            env.globals.insert(fd.name.clone(), ct.clone());
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
            env.dt_sorts.insert(def.name.clone(), us);
        }
        let result = Self::build_dt_decls(env, defs);
        env.dt_sorts.clear();
        let decls = result?;
        if decls.len() == 1 {
            let cs = env.tm.mk_dt_sort(&decls[0]);
            env.sort.insert(defs[0].name.clone(), cs.clone());
            Self::register_dt_functions(env, cs, &defs[0].dec);
        } else {
            let sorts = env.tm.mk_dt_sorts(&decls);
            for (def, cs) in defs.iter().zip(sorts) {
                env.sort.insert(def.name.clone(), cs.clone());
                Self::register_dt_functions(env, cs, &def.dec);
            }
        }
        Ok(CommandResult::None)
    }

    fn build_dt_decls(
        env: &mut Cvc5Env<'tm, Ctx>,
        defs: &[alg::DatatypeDef<Str, Sort>],
    ) -> Res<Vec<cvc5::DatatypeDecl<'tm>>> {
        let mut decls = Vec::with_capacity(defs.len());
        for def in defs {
            let params = &def.dec.params;
            let cvc5_params: Vec<CSort<'tm>> =
                params.iter().map(|p| env.tm.mk_param_sort(p)).collect();
            for (p, cs) in params.iter().zip(&cvc5_params) {
                env.dt_sorts.insert(p.clone(), cs.clone());
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
                env.dt_sorts.remove(p);
            }
            decls.push(dt_decl);
        }
        Ok(decls)
    }

    fn register_dt_functions(env: &mut Cvc5Env<'tm, Ctx>, sort: CSort<'tm>, dec: &DatatypeDec) {
        let dt = sort.datatype();
        let mut rf = env.ctx.ref_mut();
        for (i, ctor_dec) in dec.constructors.iter().enumerate() {
            let ctor = dt.constructor(i);
            env.globals.insert(ctor_dec.ctor.clone(), ctor.term());
            let tester = ctor.tester_term();
            let sym = rf.allocate_symbol(&format!("is-{}", ctor.name()));
            env.globals.insert(sym, tester);
            for (j, sel_dec) in ctor_dec.args.iter().enumerate() {
                let sel = ctor.selector(j);
                env.globals.insert(sel_dec.0.clone(), sel.term());
            }
        }
    }
}
