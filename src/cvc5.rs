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
use dashu::integer::UBig;
use std::collections::HashMap;
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

pub trait ConvertFromCvc5<Env> {
    type Output;
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

/// Inner environment for translating yaspar-ir ASTs to cvc5 objects.
///
/// This struct holds the [`TermManager`] reference and all translation state: sort/term
/// caches, global and local symbol tables, and datatype bookkeeping. It implements
/// [`TermRecursor`] for stack-safe, memoized term translation.
///
/// Users should not construct this directly — use [`Cvc5Env::create`] instead, which
/// wraps this in a [`Memoize`] layer for automatic term-level caching.
pub struct Cvc5EnvInner<'tm> {
    /// The cvc5 term manager that owns all created sorts and terms.
    tm: &'tm TermManager,
    /// Named sorts registered by `declare-sort` or datatype declarations.
    sort: HashMap<String, CSort<'tm>>,
    /// Global symbols (constants, functions, constructors, selectors, testers).
    globals: HashMap<String, CTerm<'tm>>,
    /// Local (bound) variables, keyed by their uniquely assigned id.
    locals: HashMap<usize, WithPattern<'tm>>,
    /// Cache from yaspar-ir [`Sort`] to translated [`CSort`], avoiding redundant work.
    sort_cache: HashMap<Sort, CSort<'tm>>,
    /// datatype sorts mapping from names to their corresponding potentially polymorphic representations.
    dt_sorts: HashMap<String, CSort<'tm>>,
    /// Stack of bound-variable lists for scope management in quantifiers and match arms.
    scope_stack: Vec<Vec<CTerm<'tm>>>,
    /// Cached sort-parameter substitutions for parametric datatype match translation.
    sort_subst_map: HashMap<Term, SortSubst<'tm>>,
}

impl<'tm> Cvc5EnvInner<'tm> {
    /// Create a new inner environment backed by the given [`TermManager`].
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
/// The main translation environment for sorts and terms.
///
/// This is a [`Memoize`]-wrapped [`Cvc5EnvInner`] that automatically caches translated
/// terms by their hashconsed identity. Because yaspar-ir terms are hashconsed,
/// structurally identical sub-terms share the same pointer — the memoization layer
/// ensures each unique sub-term is translated at most once.
///
/// # Construction
///
/// ```rust
/// use cvc5::TermManager;
/// use yaspar_ir::cvc5::Cvc5Env;
///
/// let tm = TermManager::new();
/// let mut env = Cvc5Env::create(&tm);
/// ```
pub type Cvc5Env<'tm> = Memoize<Cvc5EnvInner<'tm>, HashMap<Term, WithPattern<'tm>>>;

impl<'tm> Cvc5Env<'tm> {
    /// Create a new translation environment backed by the given [`TermManager`].
    pub fn create(tm: &'tm TermManager) -> Self {
        Self::new(Cvc5EnvInner::new(tm))
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
/// use yaspar_ir::cvc5::{Cvc5Env, Cvc5EnvSolver};
///
/// let tm = TermManager::new();
/// let mut solver = Solver::new(&tm);
/// let mut env = Cvc5Env::create(&tm);
/// let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
/// // now use es.to_cvc5() on Command values
/// ```
pub struct Cvc5EnvSolver<'a, 'tm> {
    /// The translation environment for sorts and terms.
    pub env: &'a mut Cvc5Env<'tm>,
    /// The cvc5 solver instance.
    pub solver: &'a mut Solver<'tm>,
}

impl<'a, 'tm> Cvc5EnvSolver<'a, 'tm> {
    /// Create a new command-translation environment from a [`Cvc5Env`] and a [`Solver`].
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

// ── Reverse sort translation (CSort → Sort) ─────────────────

/// Environment for translating cvc5 objects back to yaspar-ir typed ASTs.
///
/// This is independent of [`Cvc5Env`] / [`Cvc5EnvInner`] — the forward and reverse
/// translations have no shared mutable state.
///
/// The type parameter `Env` must implement [`HasArena`], providing the [`Arena`] used
/// to allocate yaspar-ir objects. This lets callers reuse an existing [`Context`] (or
/// any other `HasArena` implementor) instead of creating a throwaway arena.
///
/// # Example
///
/// ```rust
/// use yaspar_ir::ast::Context;
/// use yaspar_ir::cvc5::FromCvc5Env;
///
/// let mut ctx = Context::new();
/// let mut from_env = FromCvc5Env::new(&mut ctx);
/// // use from_env with ConvertFromCvc5::conv_from_cvc5
/// ```
pub struct FromCvc5Env<'tm, 'env, Env> {
    /// Cache from [`CSort`] to yaspar-ir [`Sort`], avoiding redundant work.
    sort_cache: HashMap<CSort<'tm>, Sort>,
    /// Bound variable map: cvc5 term id → VarBinding.
    locals: HashMap<u64, VarBinding<Str, Sort>>,
    /// Stack of bound variable ids for scope cleanup.
    scope_stack: Vec<Vec<u64>>,
    /// The backing environment that provides the [`Arena`].
    pub env: &'env mut Env,
}

impl<'tm, 'env, Env: HasArena> FromCvc5Env<'tm, 'env, Env> {
    /// Create a new reverse-translation environment backed by `env`.
    pub fn new(env: &'env mut Env) -> Self {
        Self {
            sort_cache: HashMap::new(),
            locals: HashMap::new(),
            scope_stack: Vec::new(),
            env,
        }
    }
}

impl<'tm, 'env, Env: HasArena> ConvertFromCvc5<FromCvc5Env<'tm, 'env, Env>> for CSort<'tm> {
    type Output = Sort;

    fn conv_from_cvc5(&self, fenv: &mut FromCvc5Env<'tm, 'env, Env>) -> Res<Sort> {
        if let Some(s) = fenv.sort_cache.get(self) {
            return Ok(s.clone());
        }
        let s = translate_sort_from_cvc5(self, fenv.env.arena())?;
        fenv.sort_cache.insert(self.clone(), s.clone());
        Ok(s)
    }
}

fn translate_sort_from_cvc5<'tm>(cs: &CSort<'tm>, arena: &mut Arena) -> Res<Sort> {
    if cs.is_boolean() {
        return Ok(arena.bool_sort());
    }
    if cs.is_integer() {
        return Ok(arena.int_sort());
    }
    if cs.is_real() {
        return Ok(arena.real_sort());
    }
    if cs.is_string() {
        return Ok(arena.string_sort());
    }
    if cs.is_regexp() {
        return Ok(arena.reglan_sort());
    }
    if cs.is_bv() {
        return Ok(arena.bv_sort(cs.bv_size().into()));
    }
    if cs.is_array() {
        let idx = translate_sort_from_cvc5(&cs.array_index_sort(), arena)?;
        let elem = translate_sort_from_cvc5(&cs.array_element_sort(), arena)?;
        return Ok(arena.array_sort(idx, elem));
    }
    // Instantiated parametric datatype (e.g. (List Int))
    if cs.is_dt() && cs.is_instantiated() {
        let dt = cs.datatype();
        let name = dt.name();
        let params = cs.instantiated_parameters();
        let ir_params: Vec<Sort> = params
            .iter()
            .map(|p| translate_sort_from_cvc5(p, arena))
            .collect::<Res<_>>()?;
        let sym = arena.allocate_symbol(name);
        return Ok(arena.sort_n(sym, ir_params));
    }
    // Monomorphic datatype sort
    if cs.is_dt() {
        let dt = cs.datatype();
        let name = dt.name();
        return Ok(arena.simple_sort(name));
    }
    // Instantiated parametric uninterpreted sort (e.g. (Pair A B))
    if cs.is_instantiated() {
        let base = cs.uninterpreted_sort_constructor();
        let name = base.symbol();
        let params = cs.instantiated_parameters();
        let ir_params: Vec<Sort> = params
            .iter()
            .map(|p| translate_sort_from_cvc5(p, arena))
            .collect::<Res<_>>()?;
        let sym = arena.allocate_symbol(name);
        return Ok(arena.sort_n(sym, ir_params));
    }
    // Uninterpreted sort
    if cs.is_uninterpreted_sort() {
        let name = cs.symbol();
        return Ok(arena.simple_sort(name));
    }
    Err(format!("unsupported cvc5 sort: {cs}"))
}

// ── Term: cvc5 → yaspar-ir ───────────────────────────────────

impl<'tm, 'env, Env: HasArena> ConvertFromCvc5<FromCvc5Env<'tm, 'env, Env>> for CTerm<'tm> {
    type Output = Term;

    fn conv_from_cvc5(&self, fenv: &mut FromCvc5Env<'tm, 'env, Env>) -> Res<Term> {
        translate_term_from_cvc5(self, fenv)
    }
}

fn translate_term_from_cvc5<'tm, 'env, Env: HasArena>(
    ct: &CTerm<'tm>,
    fenv: &mut FromCvc5Env<'tm, 'env, Env>,
) -> Res<Term> {
    let arena = fenv.env.arena();
    let kind = ct.kind();

    // ── Constants ────────────────────────────────────────────
    if ct.is_boolean_value() {
        let sort = Some(arena.bool_sort());
        return Ok(arena.allocate_term(ATerm::Constant(Constant::Bool(ct.boolean_value()), sort)));
    }
    if ct.is_integer_value() {
        let sort = ct.sort().conv_from_cvc5(fenv)?;
        let n: UBig = ct
            .integer_value()
            .parse()
            .map_err(|e| format!("Big integer parse error: {e}"))?;
        let arena = fenv.env.arena();
        return Ok(arena.allocate_term(ATerm::Constant(Constant::Numeral(n), Some(sort))));
    }
    if ct.is_real_value() {
        let sort = ct.sort().conv_from_cvc5(fenv)?;
        let s = ct.real_value();
        let arena = fenv.env.arena();
        // cvc5 returns rationals as "num/den" or just "num"
        if let Some((num, den)) = s.split_once('/') {
            let n: dashu::float::DBig =
                format!("{num}/{den}").parse().map_err(|e| format!("{e}"))?;
            return Ok(arena.allocate_term(ATerm::Constant(Constant::Decimal(n), Some(sort))));
        }
        let n: dashu::float::DBig = format!("{s}/1").parse().map_err(|e| format!("{e}"))?;
        return Ok(arena.allocate_term(ATerm::Constant(Constant::Decimal(n), Some(sort))));
    }
    if ct.is_string_value() {
        let sort = ct.sort().conv_from_cvc5(fenv)?;
        let chars = ct.u32string_value();
        let s: String = chars
            .iter()
            .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
            .collect();
        let arena = fenv.env.arena();
        let str_val = arena.allocate_str(&s);
        return Ok(arena.allocate_term(ATerm::Constant(Constant::String(str_val), Some(sort))));
    }
    if ct.is_bv_value() {
        let sort = ct.sort().conv_from_cvc5(fenv)?;
        let bits = ct.bv_value(2);
        let (bytes, len) = parse_binary_str_to_bytes(&bits);
        let arena = fenv.env.arena();
        return Ok(arena.allocate_term(ATerm::Constant(Constant::Binary(bytes, len), Some(sort))));
    }

    // ── Logical connectives ─────────────────────────────────
    match kind {
        Kind::And => {
            let children = translate_children(ct, fenv)?;
            let arena = fenv.env.arena();
            return Ok(arena.and(children));
        }
        Kind::Or => {
            let children = translate_children(ct, fenv)?;
            let arena = fenv.env.arena();
            return Ok(arena.or(children));
        }
        Kind::Xor => {
            let children = translate_children(ct, fenv)?;
            let arena = fenv.env.arena();
            return Ok(arena.xor(children));
        }
        Kind::Not => {
            let child = translate_term_from_cvc5(&ct.child(0), fenv)?;
            let arena = fenv.env.arena();
            return Ok(arena.not(child));
        }
        Kind::Implies => {
            let n = ct.num_children();
            let mut premises = Vec::with_capacity(n - 1);
            for i in 0..n - 1 {
                premises.push(translate_term_from_cvc5(&ct.child(i), fenv)?);
            }
            let concl = translate_term_from_cvc5(&ct.child(n - 1), fenv)?;
            let arena = fenv.env.arena();
            return Ok(arena.implies(premises, concl));
        }
        Kind::Equal => {
            let children = translate_children(ct, fenv)?;
            let arena = fenv.env.arena();
            if children.len() == 2 {
                return Ok(arena.eq(children[0].clone(), children[1].clone()));
            }
            // Chain: (= a b c) → (and (= a b) (= b c))
            let mut eqs = Vec::with_capacity(children.len() - 1);
            for i in 0..children.len() - 1 {
                eqs.push(arena.eq(children[i].clone(), children[i + 1].clone()));
            }
            return Ok(arena.and(eqs));
        }
        Kind::Distinct => {
            let children = translate_children(ct, fenv)?;
            let arena = fenv.env.arena();
            return Ok(arena.distinct(children));
        }
        Kind::Ite => {
            let b = translate_term_from_cvc5(&ct.child(0), fenv)?;
            let t = translate_term_from_cvc5(&ct.child(1), fenv)?;
            let e = translate_term_from_cvc5(&ct.child(2), fenv)?;
            let arena = fenv.env.arena();
            return Ok(arena.ite(b, t, e));
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
                let arena = fenv.env.arena();
                let id = arena.new_local();
                let sym = arena.allocate_symbol(&name);
                fenv.locals.insert(cvc5_id, VarBinding(sym, id, vs));
                scope_ids.push(cvc5_id);
            }
            fenv.scope_stack.push(scope_ids);
            let body = translate_term_from_cvc5(&body_ct, fenv)?;
            let scope_ids = fenv.scope_stack.pop().unwrap();
            let bindings: Vec<_> = scope_ids
                .iter()
                .map(|id| fenv.locals.remove(id).unwrap())
                .collect();
            let arena = fenv.env.arena();
            return if kind == Kind::Forall {
                Ok(arena.forall(bindings, body))
            } else {
                Ok(arena.exists(bindings, body))
            };
        }
        // ── Negation (unary minus) ──────────────────────────────
        Kind::Neg => {
            let child = translate_term_from_cvc5(&ct.child(0), fenv)?;
            let sort = ct.sort().conv_from_cvc5(fenv)?;
            let arena = fenv.env.arena();
            let sym = arena.allocate_symbol("-");
            let qid = QualifiedIdentifier::simple(sym);
            return Ok(arena.app(qid, vec![child], Some(sort)));
        }

        // ── Function application (UF, constructors, selectors, testers) ──
        Kind::Constant => {
            // Uninterpreted constant (declared symbol)
            let name = ct.symbol().to_string();
            let sort = ct.sort().conv_from_cvc5(fenv)?;
            let arena = fenv.env.arena();
            let sym = arena.allocate_symbol(&name);
            let qid = QualifiedIdentifier::simple(sym);
            return Ok(arena.global(qid, Some(sort)));
        }
        Kind::ApplyUf => {
            let head = ct.child(0);
            let name = head.symbol().to_string();
            let mut args = Vec::with_capacity(ct.num_children() - 1);
            for i in 1..ct.num_children() {
                args.push(translate_term_from_cvc5(&ct.child(i), fenv)?);
            }
            let sort = ct.sort().conv_from_cvc5(fenv)?;
            let arena = fenv.env.arena();
            let sym = arena.allocate_symbol(&name);
            let qid = QualifiedIdentifier::simple(sym);
            return Ok(arena.app(qid, args, Some(sort)));
        }
        Kind::ApplyConstructor => {
            let head = ct.child(0);
            let name = head.symbol().to_string();
            let n = ct.num_children();
            if n == 1 {
                // Nullary constructor → global
                let sort = ct.sort().conv_from_cvc5(fenv)?;
                let arena = fenv.env.arena();
                let sym = arena.allocate_symbol(&name);
                let qid = QualifiedIdentifier::simple(sym);
                return Ok(arena.global(qid, Some(sort)));
            }
            let mut args = Vec::with_capacity(n - 1);
            for i in 1..n {
                args.push(translate_term_from_cvc5(&ct.child(i), fenv)?);
            }
            let sort = ct.sort().conv_from_cvc5(fenv)?;
            let arena = fenv.env.arena();
            let sym = arena.allocate_symbol(&name);
            let qid = QualifiedIdentifier::simple(sym);
            return Ok(arena.app(qid, args, Some(sort)));
        }
        Kind::ApplySelector => {
            let head = ct.child(0);
            let name = head.symbol().to_string();
            let arg = translate_term_from_cvc5(&ct.child(1), fenv)?;
            let sort = ct.sort().conv_from_cvc5(fenv)?;
            let arena = fenv.env.arena();
            let sym = arena.allocate_symbol(&name);
            let qid = QualifiedIdentifier::simple(sym);
            return Ok(arena.app(qid, vec![arg], Some(sort)));
        }
        Kind::ApplyTester => {
            let head = ct.child(0);
            let ctor_name = head.symbol().to_string();
            let arg = translate_term_from_cvc5(&ct.child(1), fenv)?;
            let sort = ct.sort().conv_from_cvc5(fenv)?;
            let arena = fenv.env.arena();
            let is_sym = arena.allocate_symbol("is");
            let ctor_sym = arena.allocate_symbol(&ctor_name);
            let id = alg::Identifier {
                symbol: is_sym,
                indices: vec![Index::Symbol(ctor_sym)],
            };
            let qid = QualifiedIdentifier::from(id);
            return Ok(arena.app(qid, vec![arg], Some(sort)));
        }

        // ── Variable (bound) ────────────────────────────────────
        Kind::Variable => {
            let cvc5_id = ct.id();
            if let Some(vb) = fenv.locals.get(&cvc5_id) {
                let arena = fenv.env.arena();
                return Ok(arena.local(alg::Local {
                    id: vb.1,
                    symbol: vb.0.clone(),
                    sort: vb.2.clone(),
                }));
            }
            // Fallback: unregistered variable (shouldn't happen in well-formed terms)
            let name = ct.symbol().to_string();
            let sort = ct.sort().conv_from_cvc5(fenv)?;
            let arena = fenv.env.arena();
            let id = arena.new_local();
            let sym = arena.allocate_symbol(&name);
            return Ok(arena.local(alg::Local {
                id,
                symbol: sym,
                sort,
            }));
        }
        // ── Nullary regexp constants ───────────────────────────────
        Kind::RegexpNone | Kind::RegexpAll | Kind::RegexpAllchar => {
            let ik = cvc5_kind_to_ident_kind(kind).unwrap();
            let sort = ct.sort().conv_from_cvc5(fenv)?;
            let arena = fenv.env.arena();
            let sym = arena.allocate_symbol(ik.name());
            let qid = QualifiedIdentifier::simple(sym);
            return Ok(arena.global(qid, Some(sort)));
        }

        // ── BitvectorToNat ──────────────────────────────────────
        Kind::BitvectorToNat => {
            let child = translate_term_from_cvc5(&ct.child(0), fenv)?;
            let sort = ct.sort().conv_from_cvc5(fenv)?;
            let arena = fenv.env.arena();
            let sym = arena.allocate_symbol("bv2nat");
            let qid = QualifiedIdentifier::simple(sym);
            return Ok(arena.app(qid, vec![child], Some(sort)));
        }

        // ── Match expressions ───────────────────────────────────
        Kind::Match => {
            let scrutinee = translate_term_from_cvc5(&ct.child(0), fenv)?;
            let n = ct.num_children();
            let mut arms = Vec::with_capacity(n - 1);
            for i in 1..n {
                let case = ct.child(i);
                let arm = translate_match_case_from_cvc5(&case, fenv)?;
                arms.push(arm);
            }
            let arena = fenv.env.arena();
            return Ok(arena.matching(scrutinee, arms));
        }
        _ => {}
    }

    // ── Known operator kinds ────────────────────────────────
    if let Some(ik) = cvc5_kind_to_ident_kind(kind) {
        let children = translate_children(ct, fenv)?;
        let sort = ct.sort().conv_from_cvc5(fenv)?;
        let arena = fenv.env.arena();
        let name = ik.name();
        let sym = arena.allocate_symbol(name);
        let qid = QualifiedIdentifier::simple(sym);
        return Ok(arena.app(qid, children, Some(sort)));
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

/// Parse a binary string (e.g. "10110") into packed bytes and length.
/// Mirrors the logic of `yaspar::parse_binary_str`.
fn parse_binary_str_to_bytes(s: &str) -> (Vec<u8>, usize) {
    let mut ret = Vec::new();
    let mut r: u8 = 0;
    let mut i: usize = 1;
    for c in s.chars().rev() {
        if c == '1' {
            r |= i as u8;
        }
        i *= 2;
        if i == 256 {
            i = 1;
            ret.push(r);
            r = 0;
        }
    }
    if i > 1 {
        ret.push(r);
    }
    (ret, s.len())
}

fn translate_children<'tm, 'env, Env: HasArena>(
    ct: &CTerm<'tm>,
    fenv: &mut FromCvc5Env<'tm, 'env, Env>,
) -> Res<Vec<Term>> {
    let n = ct.num_children();
    let mut children = Vec::with_capacity(n);
    for i in 0..n {
        children.push(translate_term_from_cvc5(&ct.child(i), fenv)?);
    }
    Ok(children)
}

fn translate_match_case_from_cvc5<'tm, 'env, Env: HasArena>(
    case: &CTerm<'tm>,
    fenv: &mut FromCvc5Env<'tm, 'env, Env>,
) -> Res<alg::PatternArm<Str, Term>> {
    let case_kind = case.kind();
    match case_kind {
        Kind::MatchCase => {
            // Children: [pattern (ApplyConstructor), body]
            let pattern_ct = case.child(0);
            // Nullary constructor: ApplyConstructor with just the ctor term
            let ctor_term = pattern_ct.child(0);
            let ctor_name = ctor_term.symbol().to_string();
            let body = translate_term_from_cvc5(&case.child(1), fenv)?;
            let arena = fenv.env.arena();
            let sym = arena.allocate_symbol(&ctor_name);
            Ok(alg::PatternArm {
                pattern: alg::Pattern::Ctor(sym),
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
                let name = v.symbol().to_string();
                let vs = v.sort().conv_from_cvc5(fenv)?;
                let arena = fenv.env.arena();
                let id = arena.new_local();
                let sym = arena.allocate_symbol(&name);
                let vb = VarBinding(sym.clone(), id, vs);
                fenv.locals.insert(cvc5_id, vb);
                fenv.scope_stack.push(vec![cvc5_id]);

                let body = translate_term_from_cvc5(&body_ct, fenv)?;

                let scope_ids = fenv.scope_stack.pop().unwrap();
                for sid in &scope_ids {
                    fenv.locals.remove(sid);
                }
                Ok(alg::PatternArm {
                    pattern: alg::Pattern::Wildcard(Some((sym, id))),
                    body,
                })
            } else {
                // Applied constructor pattern: pattern is ApplyConstructor
                let ctor_term = pattern_ct.child(0);
                let ctor_name = ctor_term.symbol().to_string();
                let num_args = pattern_ct.num_children() - 1;

                // Bind variables from the variable list
                let mut scope_ids = Vec::new();
                let mut arguments = Vec::with_capacity(num_args);

                // Build a set of variable ids from the vlist for lookup
                let mut vlist_vars: HashMap<u64, usize> = HashMap::new();
                for i in 0..vlist.num_children() {
                    let v = vlist.child(i);
                    let cvc5_id = v.id();
                    let name = v.symbol().to_string();
                    let vs = v.sort().conv_from_cvc5(fenv)?;
                    let arena = fenv.env.arena();
                    let id = arena.new_local();
                    let sym = arena.allocate_symbol(&name);
                    fenv.locals.insert(cvc5_id, VarBinding(sym, id, vs));
                    scope_ids.push(cvc5_id);
                    vlist_vars.insert(cvc5_id, i);
                }
                fenv.scope_stack.push(scope_ids.clone());

                // Map pattern arguments to Option<(Str, usize)>
                for i in 0..num_args {
                    let arg = pattern_ct.child(i + 1);
                    let arg_id = arg.id();
                    if let Some(vb) = fenv.locals.get(&arg_id) {
                        if arg.has_symbol() {
                            arguments.push(Some((vb.0.clone(), vb.1)));
                        } else {
                            arguments.push(None);
                        }
                    } else {
                        arguments.push(None);
                    }
                }

                let body = translate_term_from_cvc5(&body_ct, fenv)?;

                let scope_ids = fenv.scope_stack.pop().unwrap();
                for sid in &scope_ids {
                    fenv.locals.remove(sid);
                }

                let arena = fenv.env.arena();
                let ctor_sym = arena.allocate_symbol(&ctor_name);
                Ok(alg::PatternArm {
                    pattern: alg::Pattern::Applied {
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

fn translate_indexed_from_cvc5<'tm, 'env, Env: HasArena>(
    ct: &CTerm<'tm>,
    op: &cvc5::Op<'tm>,
    fenv: &mut FromCvc5Env<'tm, 'env, Env>,
) -> Res<Option<Term>> {
    let op_kind = op.kind();
    let children = translate_children(ct, fenv)?;
    let sort = ct.sort().conv_from_cvc5(fenv)?;
    let arena = fenv.env.arena();

    let mk_indexed = |arena: &mut Arena, name: &str, indices: Vec<Index>| -> Term {
        let sym = arena.allocate_symbol(name);
        let id = alg::Identifier {
            symbol: sym,
            indices,
        };
        let qid = QualifiedIdentifier::from(id);
        arena.app(qid, children.clone(), Some(sort.clone()))
    };

    let idx_u32 = |i: usize| -> Res<UBig> {
        let idx_term = op.index(i);
        let val: u32 = idx_term.uint32_value();
        Ok(UBig::from(val))
    };

    let term = match op_kind {
        Kind::BitvectorExtract => {
            let hi = idx_u32(0)?;
            let lo = idx_u32(1)?;
            mk_indexed(
                arena,
                "extract",
                vec![Index::Numeral(hi), Index::Numeral(lo)],
            )
        }
        Kind::BitvectorRepeat => {
            let n = idx_u32(0)?;
            mk_indexed(arena, "repeat", vec![Index::Numeral(n)])
        }
        Kind::BitvectorZeroExtend => {
            let n = idx_u32(0)?;
            mk_indexed(arena, "zero_extend", vec![Index::Numeral(n)])
        }
        Kind::BitvectorSignExtend => {
            let n = idx_u32(0)?;
            mk_indexed(arena, "sign_extend", vec![Index::Numeral(n)])
        }
        Kind::BitvectorRotateLeft => {
            let n = idx_u32(0)?;
            mk_indexed(arena, "rotate_left", vec![Index::Numeral(n)])
        }
        Kind::BitvectorRotateRight => {
            let n = idx_u32(0)?;
            mk_indexed(arena, "rotate_right", vec![Index::Numeral(n)])
        }
        Kind::IntToBitvector => {
            let n = idx_u32(0)?;
            mk_indexed(arena, "int2bv", vec![Index::Numeral(n)])
        }
        Kind::RegexpRepeat => {
            let n = idx_u32(0)?;
            mk_indexed(arena, "re.^", vec![Index::Numeral(n)])
        }
        Kind::RegexpLoop => {
            let lo = idx_u32(0)?;
            let hi = idx_u32(1)?;
            mk_indexed(
                arena,
                "re.loop",
                vec![Index::Numeral(lo), Index::Numeral(hi)],
            )
        }
        _ => return Ok(None),
    };
    Ok(Some(term))
}

/// Reverse mapping from cvc5 Kind to yaspar-ir IdentifierKind.
fn cvc5_kind_to_ident_kind(kind: Kind) -> Option<alg::IdentifierKind<Str>> {
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
            Some(ref ik) if ident_kind_to_cvc5(ik).is_some() => {
                Ok(self.tm.mk_term(ident_kind_to_cvc5(ik).unwrap(), &[]).into())
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
                } else if let Attribute::Constant(kw, c) = attr {
                    solver.set_option(kw.symbol_of(), &c.to_string());
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
                let sorts = env
                    .sort
                    .values()
                    .filter(|s| s.is_uninterpreted_sort())
                    .cloned()
                    .chain(
                        env.sort_cache
                            .values()
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
