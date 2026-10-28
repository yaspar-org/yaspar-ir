// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Type-checking algorithm for SMTLib ASTs.
//!
//! This module checks an AST object and returns its corresponding typed representation, or an
//! error message if the object is malformed. The algorithm is organized as constraint programming
//! over the parametric algebraic ASTs in [`crate::raw::alg`], which allows it to work with
//! multiple AST instantiations:
//!
//! - **Untyped → Typed**: the primary use case, converting parsed untyped ASTs into well-formed
//!   typed representations.
//! - **Typed → Typed**: re-checking a typed AST built via unchecked APIs, serving as a golden
//!   standard for invariant validation during development.
//!
//! The core types are:
//!
//! - [`TC<T>`] — alias for `Result<T, String>`, the type-checking monad.
//! - [`TCEnvGen`] — the generic type-checking environment, parameterized over the local
//!   scope representation. Carries borrowed references to the arena, context metadata,
//!   and context frame (sorts + symbol table).
//! - [`TCEnv`] — the concrete type-checking environment used during traversal, which
//!   specializes [`TCEnvGen`] with [`TCLocal`] as the local scope.
//! - [`TCLocal`] — the local scope state during type-checking, holding the local variable
//!   environment, incremental scope extensions, and a scrutinee map for match expressions.
//! - [`Typecheck`] — the trait implemented by all AST nodes; call `.type_check(&mut env)` to
//!   perform type-checking.

use super::alg;
use super::alg::{LocalId, VarBinding};
use super::instance::{
    Arena, Attribute, Constant, DatatypeDec, Identifier, Index, Pattern, PatternArm,
    QualifiedIdentifier, Sort, SortDef, Str, Term,
};
use crate::allocator::*;
use crate::ast::utils::is_term_bool_alt;
use crate::ast::{
    Context, ContextMeta, ContextStack, FetchSort, HasArenaAlt, Monomorphization, SymbolQuote,
    Theory,
};
use crate::containers::{LocEnv, Mapping, sanitize_bindings};
use crate::meta::WithMeta;
use crate::statics::{BITVEC, BOOL, INT, REAL, STRING};
use crate::traits::{AllocatableString, Contains};
use crate::traits::{MetaData, Repr};
pub(crate) use app::{
    typed_app, typed_app_sig, typed_qualified_identifier, typed_qualified_identifier_sig,
};
use dashu::integer::UBig;
use num_traits::cast::ToPrimitive;
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use unif::SortSubst;
use yaspar_macros::stack_safe;

mod app;
pub(crate) mod unif;

/// Type-checking monad
pub type TC<T> = Result<T, String>;

/// The trait for type-checking
pub trait Typecheck<Env> {
    type Out;

    fn type_check(&self, env: &mut Env) -> TC<Self::Out>;
}

/// The generic type-checking environment.
///
/// Holds borrowed references to the [`Arena`], [`ContextMeta`] (logic and theories),
/// and [`ContextStack`] (sorts and symbol table), plus a generic `Local` scope.
/// The `Local` parameter is [`TCLocal`] during normal type-checking, but can be
/// any type implementing [`Mapping`] for reuse in helper functions.
pub struct TCEnvGen<'a, Local> {
    pub(crate) arena: &'a mut Arena,
    pub(crate) meta: &'a ContextMeta,
    pub(crate) stack: &'a ContextStack,
    pub(crate) local: Local,
}

impl<'a, Local> TCEnvGen<'a, Local> {
    /// Create a new environment from a [`Context`] and a local scope.
    pub(crate) fn new(context: &'a mut Context, local: Local) -> Self {
        Self {
            arena: &mut context.arena,
            meta: &context.meta,
            stack: &context.stack,
            local,
        }
    }

    /// Look up a sort definition by name, allocating the symbol in the arena.
    fn get_sort_def(&mut self, s: &str) -> TC<&'a SortDef> {
        let symbol = self.arena.allocate_symbol(s);
        match self.stack.get_sort(&symbol) {
            None => Err(format!("TC: unknown sort: {}!", s)),
            Some(d) => Ok(d),
        }
    }

    /// Get the sort of `s` if it's a ground sort, i.e. a sort with no parametricity.
    fn get_ground_sort(&mut self, s: &str) -> TC<Sort> {
        match self.get_sort_def(s)? {
            SortDef::Opaque(n) | SortDef::OpaqueDeclared(n) => {
                if *n == 0 {
                    Ok(self.arena.simple_sort(s))
                } else {
                    Err(format!("TC: sort {} is not ground!", s))
                }
            }
            SortDef::Transparent { params, sort } => {
                if params.is_empty() {
                    Ok(sort.clone())
                } else {
                    Err(format!("TC: sort {} is not ground!", s))
                }
            }
            SortDef::Datatype(dt) => {
                if dt.params.is_empty() {
                    Ok(self.arena.simple_sort(s))
                } else {
                    Err(format!("TC: sort {} is not ground!", s))
                }
            }
        }
    }

    /// Obtain a [DatatypeDec] if a sort is a datatype declaration.
    pub(crate) fn get_datatype_dec(&mut self, s: &Str) -> TC<&'a DatatypeDec> {
        match self.get_sort_def(s)? {
            SortDef::Datatype(d) => Ok(d),
            _ => Err(format!("TC: sort {} is not datatype!", s)),
        }
    }
}

#[allow(private_bounds)]
impl<'a, Local> TCEnvGen<'a, Local>
where
    Local: Mapping,
{
    pub(crate) fn with_empty_local<L: Default>(&mut self) -> TCEnvGen<'_, L> {
        TCEnvGen {
            arena: self.arena,
            meta: self.meta,
            stack: self.stack,
            local: L::default(),
        }
    }

    pub(crate) fn convert_to_empty_local<L: Default>(self) -> TCEnvGen<'a, L> {
        TCEnvGen {
            arena: self.arena,
            meta: self.meta,
            stack: self.stack,
            local: L::default(),
        }
    }
}

/// The concrete type-checking environment used by [`Typecheck`] impls.
///
/// This specializes the generic environment with a concrete local scope, providing
/// the full environment needed for type-checking terms, sorts, and commands.
pub type TCEnv<'a, 'b, T> = TCEnvGen<'a, TCLocal<'b, T>>;

impl<'a, 'b, S> TCEnv<'a, 'b, S> {
    /// Replace the local scope with a new one built from the given [`LocEnv`].
    pub(crate) fn convert_to_new_local<'c, T>(self, local: LocEnv<'c, Str, T>) -> TCEnv<'a, 'c, T> {
        TCEnv {
            arena: self.arena,
            meta: self.meta,
            stack: self.stack,
            local: TCLocal {
                loc: local,
                loc_inc: vec![],
                scrutinee_map: Default::default(),
            },
        }
    }
}

impl<T> HasArenaAlt for TCEnvGen<'_, T> {
    #[inline]
    fn arena_alt(&mut self) -> &mut Arena {
        self.arena
    }
}

/// Convert from untyped constant to typed constant
fn constant_conv<Str, T>(c: &alg::Constant<Str>, arena: &mut T) -> Constant
where
    Str: Contains<T = String>,
    T: HasArenaAlt,
{
    match c {
        alg::Constant::Numeral(n) => Constant::Numeral(n.clone()),
        alg::Constant::Decimal(d) => Constant::Decimal(d.clone()),
        alg::Constant::String(s) => Constant::String(arena.arena_alt().allocate_str(s.inner())),
        alg::Constant::Binary(bs, n) => Constant::Binary(bs.clone(), *n),
        alg::Constant::Hexadecimal(bs, n) => Constant::Hexadecimal(bs.clone(), *n),
        alg::Constant::Bool(b) => Constant::Bool(*b),
    }
}

/// Check and return a valid bit vector sort
fn valid_bv_sort<T>(env: &mut T, sz: UBig) -> TC<Sort>
where
    T: HasArenaAlt,
{
    match sz.to_usize() {
        None | Some(0) => Err(format!(
            "TC: BitVec has size {sz} but it should be > 0 and small enough to fit in the memory (<= {})!",
            usize::MAX
        )),
        Some(_) => Ok(env.arena_alt().bv_sort(sz)),
    }
}

impl<Str, L> Typecheck<TCEnvGen<'_, L>> for alg::Constant<Str> {
    type Out = Sort;

    fn type_check(&self, env: &mut TCEnvGen<'_, L>) -> TC<Sort> {
        match self {
            alg::Constant::Numeral(_) => {
                if env.meta.theories.contains(&Theory::Reals) {
                    env.get_ground_sort(REAL)
                } else {
                    env.get_ground_sort(INT)
                }
            }
            alg::Constant::Decimal(_) => env.get_ground_sort(REAL),
            alg::Constant::String(_) => env.get_ground_sort(STRING),
            alg::Constant::Binary(_, n) => {
                if env.meta.theories.contains(&Theory::Bitvectors) {
                    valid_bv_sort(env, UBig::from(*n))
                } else {
                    Err("TC: the current logic does not support bit vectors!".into())
                }
            }
            alg::Constant::Hexadecimal(_, n) => {
                if env.meta.theories.contains(&Theory::Bitvectors) {
                    valid_bv_sort(env, UBig::from(4u8) * UBig::from(*n))
                } else {
                    Err("TC: the current logic does not support bit vectors!".into())
                }
            }
            alg::Constant::Bool(_) => env.get_ground_sort(BOOL),
        }
    }
}

/// Return an error indicating that the given identifier does not exist.
fn identifier_not_found<T>(symbol: &Str, meta_string: &str) -> TC<T> {
    Err(format!(
        "TC: identifier {}{meta_string} does not exist!",
        symbol.sym_quote()
    ))
}

/// Return a sort-mismatch error: `expected` was required but `given` was found for term `t`.
pub(crate) fn sort_mismatch<T>(
    expected: &Sort,
    given: &Sort,
    t: impl Display,
    meta_string: &str,
) -> TC<T> {
    Err(format!(
        "TC: {expected} is expected for {t}{meta_string} but {given} is given!",
    ))
}

/// Check that all sort variables in `subst` have been instantiated; error otherwise.
pub(crate) fn check_subst_instantiation(subst: &SortSubst, t: impl Display) -> TC<()> {
    let vs = unif::subst_missed_vars(subst);
    if !vs.is_empty() {
        Err(format!(
            "TC: term {} does not have enough information to determine all sort variable(s): {}!",
            t,
            vs.iter()
                .map(|s| s.as_str().into())
                .collect::<Vec<String>>()
                .join(", ")
        ))
    } else {
        Ok(())
    }
}

/// Ensure that symbol `s` is NOT bound in the local scope (i.e. it is a global symbol).
fn check_global_var_locally<L, S>(env: &mut TCEnvGen<L>, s: S) -> TC<Str>
where
    L: Mapping<Key = Str>,
    S: AllocatableString<Arena>,
{
    let sym = s.allocate(env.arena_alt());
    match env.local.lookup(&sym) {
        None => Ok(sym),
        Some(_) => Err(format!(
            "TC: identifier {}{} has been bound locally!",
            sym.sym_quote(),
            s.display_meta_data()
        )),
    }
}

impl<Str, L> Typecheck<TCEnvGen<'_, L>> for alg::Index<Str>
where
    Str: AllocatableString<Arena>,
{
    type Out = Index;

    fn type_check(&self, env: &mut TCEnvGen<'_, L>) -> TC<Self::Out> {
        match self {
            alg::Index::Numeral(n) => Ok(Index::Numeral(n.clone())),
            alg::Index::Symbol(s) => Ok(Index::Symbol(s.allocate(env.arena_alt()))),
            alg::Index::Hexadecimal(bs, n) => Ok(Index::Hexadecimal(bs.clone(), *n)),
        }
    }
}

impl<Str, L> Typecheck<TCEnvGen<'_, L>> for alg::Identifier<Str>
where
    Str: AllocatableString<Arena>,
{
    type Out = Identifier;

    fn type_check(&self, env: &mut TCEnvGen<'_, L>) -> TC<Self::Out> {
        Ok(Identifier {
            symbol: self.symbol.allocate(env.arena_alt()),
            indices: self
                .indices
                .iter()
                .map(|ind| ind.type_check(env))
                .collect::<TC<Vec<_>>>()?,
        })
    }
}

/// Type-checking a sort also normalizes it
pub(crate) fn tc_sort<S, L>(
    env: &mut TCEnvGen<L>,
    id: &alg::Identifier<S>,
    sorts: impl IntoIterator<Item = Sort>,
) -> TC<Sort>
where
    L: Mapping<Key = Str>,
    S: AllocatableString<Arena>,
{
    let meta = id.symbol.display_meta_data();
    let id = id.type_check(env)?;
    if env.local.lookup(&id.symbol).is_some() {
        // local sort variable
        if sorts.into_iter().next().is_some() {
            Err(format!(
                "TC: {id}{meta} is shadowed by a local sort variable, which cannot be parameterized!"
            ))
        } else if !id.indices.is_empty() {
            Err(format!(
                "TC: local sort {id}{meta} does not support indices!"
            ))
        } else {
            Ok(env.arena.sort0(id.symbol))
        }
    } else if let Some(d) = env.stack.get_sort(&id.symbol) {
        // a global sort
        if !id.indices.is_empty() {
            return Err(format!("TC: sort {id}{meta} should not contain indices!"));
        }
        let arity = d.arity();
        let sorts = sorts.into_iter().collect::<Vec<_>>();
        if sorts.len() != arity {
            let sort = env.arena_alt().sort(id, sorts);
            Err(format!(
                "TC: sort {sort} is declared to have arity {arity}!"
            ))
        } else {
            match d {
                SortDef::Opaque(_) | SortDef::OpaqueDeclared(_) | SortDef::Datatype(_) => {
                    Ok(env.arena.sort_n(id.symbol, sorts))
                }
                SortDef::Transparent { params, sort } => {
                    // when there sort is transparent, we substitute its definition
                    let subst: SortSubst = params
                        .iter()
                        .cloned()
                        .zip(sorts)
                        .map(|(k, v)| (k, Some(v)))
                        .collect();
                    let s = unif::apply_subst(env.arena, &subst, sort);
                    Ok(s)
                }
            }
        }
    } else if env.meta.theories.contains(&Theory::Bitvectors) && id.symbol.inner() == BITVEC {
        // this is a special case; admit (_ BitVec X) where X is a numeral
        let sorts = sorts.into_iter().collect::<Vec<_>>();
        match id.indices.as_slice() {
            [alg::Index::Numeral(sz)] if sorts.is_empty() => valid_bv_sort(env, sz.clone()),
            _ => {
                let sort = env.arena_alt().sort(id, sorts);
                Err(format!(
                    "TC: sort {sort} is malformed! only `(_ {BITVEC} X)` is admissible!"
                ))
            }
        }
    } else {
        Err(format!("TC: sort {id}{meta} is not declared!"))
    }
}

impl<St, So, L> Typecheck<TCEnvGen<'_, L>> for So
where
    St: AllocatableString<Arena>,
    So: Contains<T: Repr<T = alg::Sort<St, So>>> + Display,
    L: Mapping<Key = Str, Value = (LocalId, ())>,
{
    type Out = Sort;

    fn type_check(&self, env: &mut TCEnvGen<L>) -> TC<Self::Out> {
        tc_sort_rec(self, env)
    }
}

/// The body of [`Typecheck::type_check`] for a sort, which recurses over a sort of unbounded
/// nesting. It lives out here because `#[stack_safe]` writes the rewritten body beside the member,
/// and a trait impl may hold nothing but the trait's own members. The impl above forwards to it, and
/// the recursion below stays out of trait dispatch so a nested sort re-enters this driver rather
/// than starting a new one.
#[stack_safe]
fn tc_sort_rec<St, So, L>(this: &So, env: &mut TCEnvGen<L>) -> TC<Sort>
where
    St: AllocatableString<Arena>,
    So: Contains<T: Repr<T = alg::Sort<St, So>>> + Display,
    L: Mapping<Key = Str, Value = (LocalId, ())>,
{
    let args = &this.inner().repr().1;
    let mut sorts: Vec<Sort> = Vec::with_capacity(args.len());
    let mut i = 0usize;
    while i < args.len() {
        sorts.push(tc_sort_rec(&args[i], env)?);
        i += 1;
    }
    tc_sort(env, &this.inner().repr().0, sorts)
}

/// Build a typed [`Term`] from a [`Constant`], inferring its sort.
pub(crate) fn typed_constant<L>(env: &mut TCEnvGen<L>, c: Constant) -> TC<Term> {
    let s = c.type_check(env)?;
    Ok(env.arena.constant(c, Some(s)))
}

/// Build a typed equality term `(= a b)`. Both arguments must have the same sort.
pub(crate) fn typed_eq<L>(env: &mut TCEnvGen<L>, at: Term, bt: Term, bt_meta: &str) -> TC<Term> {
    let sa = at.get_sort(env);
    let sb = bt.get_sort(env);
    if sa == sb {
        Ok(env.arena.eq(at, bt))
    } else {
        sort_mismatch(&sa, &sb, bt, bt_meta)
    }
}

/// Build a typed `(distinct ...)` term. At least two arguments of the same sort required.
pub(crate) fn typed_distinct<L>(
    env: &mut TCEnvGen<L>,
    ts: Vec<WithMeta<Term, String>>,
) -> TC<Term> {
    if ts.len() < 2 {
        return Err("TC: distinct requires at least two terms!".into());
    }
    let s = ts[0].data.get_sort(env);
    let mut terms = vec![];
    for WithMeta { data: t, meta } in ts {
        let ts = t.get_sort(env);
        if s != ts {
            return sort_mismatch(&s, &ts, t, &meta);
        }
        terms.push(t);
    }
    Ok(env.arena.distinct(terms))
}

/// Build a typed `(not t)` term. The argument must be `Bool`-sorted.
pub(crate) fn typed_not<L>(env: &mut TCEnvGen<L>, t: Term, meta: &str) -> TC<Term> {
    is_term_bool_alt(env, &t, meta)?;
    Ok(env.arena.not(t))
}

/// This function, given `t` a term of some datatype, determines a map from its constructors to
/// the sorts of arguments.
pub(crate) fn tc_determine_datatype_sort_map<L>(
    env: &mut TCEnvGen<L>,
    t: &Term,
    meta: &str,
) -> TC<HashMap<Str, Vec<Sort>>> {
    let so = t.get_sort(env);
    let dt = env.get_datatype_dec(so.sort_name()).map_err(|_| {
        format!(
            "TC: sort {} of the given term{meta} is not a datatype!",
            so.sort_name()
        )
    })?;
    // monomorphization instantiates the sort variables, if exist.
    let dt = dt.monomorphize(&so, env).map_err(|e| format!("TC: {e}"))?;

    Ok(dt
        .constructors
        .iter()
        .map(|ctor| {
            (
                ctor.ctor.clone(),
                ctor.args.iter().map(|arg| arg.2.clone()).collect(),
            )
        })
        .collect())
}

/// Local scope state carried during type-checking.
///
/// - `loc`: the linked-list local variable environment (bindings from `let`, quantifiers, etc.)
/// - `loc_inc`: incremental scope extensions accumulated during traversal
/// - `scrutinee_map`: tracks datatype sort information for match scrutinees, used to
///   resolve constructor patterns
pub struct TCLocal<'b, T> {
    pub(crate) loc: LocEnv<'b, Str, T>,
    pub(crate) loc_inc: Vec<Vec<VarBinding<Str, T>>>,
    pub(crate) scrutinee_map: HashMap<Term, HashMap<Str, Vec<Sort>>>,
}

impl<T> Default for TCLocal<'_, T> {
    fn default() -> Self {
        Self {
            loc: LocEnv::Nil,
            loc_inc: vec![],
            scrutinee_map: Default::default(),
        }
    }
}

impl<T> TCLocal<'_, T> {
    /// Pop off the top of the scope stack; return an error if the stack is empty.
    fn scope_pop(&mut self, visiting: impl Display) -> TC<Vec<VarBinding<Str, T>>> {
        self.loc_inc
            .pop()
            .ok_or_else(|| format!("TC: scoping error, failed to manage scope for {visiting}"))
    }
}

impl<T> Mapping for TCLocal<'_, T>
where
    T: Clone,
{
    type Key = Str;
    type Value = (LocalId, T);

    fn lookup(&self, key: &Self::Key) -> Option<Self::Value> {
        self.loc_inc.lookup(key).or_else(|| self.loc.lookup(key))
    }
}

/// Check that all terms in the iterator are `Bool`-sorted.
fn check_all_bool_terms<'a, E>(
    terms: impl Iterator<Item = WithMeta<&'a Term, String>>,
    e: &mut E,
) -> TC<()>
where
    E: HasArenaAlt,
{
    for t in terms {
        is_term_bool_alt(e, t.data, &t.meta)?;
    }
    Ok(())
}

impl<Str, So, L> Typecheck<TCEnvGen<'_, L>> for alg::QualifiedIdentifier<Str, So>
where
    Str: AllocatableString<Arena>,
    So: for<'a, 'b> Typecheck<TCEnv<'a, 'b, ()>, Out = Sort>,
    L: Mapping,
{
    type Out = QualifiedIdentifier;

    fn type_check(&self, env: &mut TCEnvGen<'_, L>) -> TC<Self::Out> {
        let i = self.0.type_check(env)?;
        let s = match &self.1 {
            None => None,
            Some(s) => Some(s.type_check(&mut env.with_empty_local())?),
        };
        Ok(alg::QualifiedIdentifier(i, s))
    }
}

impl<St, So, T> Typecheck<TCEnv<'_, '_, Sort>> for T
where
    St: AllocatableString<Arena> + Contains<T = String>,
    So: for<'a, 'b> Typecheck<TCEnv<'a, 'b, ()>, Out = Sort>,
    T: Contains<T: Repr<T = alg::Term<St, So, T>>> + Display + MetaData,
{
    type Out = Term;

    fn type_check(&self, env: &mut TCEnvGen<'_, TCLocal<Sort>>) -> TC<Self::Out> {
        tc_term_rec(self, false, env)
    }
}

/// The body of [`Typecheck::type_check`] for a term, which recurses over a term of unbounded
/// nesting. Like [`tc_sort_rec`], it lives out here so that `#[stack_safe]` can rewrite it, and a
/// nested term re-enters this driver rather than starting a new one.
///
/// Every loop over a term's children is a member of its own, so the slices it walks are typed by
/// its signature. Every scope pushed onto `env.local` before descending into a body is popped once
/// that body returns, whether it succeeded or not, so an error leaves the local environment as it
/// was found.
#[stack_safe]
mod term_rec {
    use super::*;

    /// `pattern_ok` says whether `this` is the body of a quantifier, the only place where
    /// `:pattern` and `:no-pattern` may annotate a term (§3.6.5).
    pub(super) fn tc_term_rec<St, So, T>(
        this: &T,
        pattern_ok: bool,
        env: &mut TCEnv<'_, '_, Sort>,
    ) -> TC<Term>
    where
        St: AllocatableString<Arena> + Contains<T = String>,
        So: for<'a, 'b> Typecheck<TCEnv<'a, 'b, ()>, Out = Sort>,
        T: Contains<T: Repr<T = alg::Term<St, So, T>>> + Display + MetaData,
    {
        match this.inner().repr() {
            alg::Term::Constant(constant, sort) => tc_constant(env, this, constant, sort),
            alg::Term::Global(id, sort) => tc_global(env, this, id, sort),
            alg::Term::Local(id) => tc_local(env, this, id),
            alg::Term::App(id, ts, sort) => {
                let recs = tc_terms_rec(ts, env)?;
                tc_app(env, this, id, ts, sort, recs)
            }
            alg::Term::Let(vs, body) => {
                let bindings = tc_let_bindings_rec(vs, env)?;
                tc_let_scope(env, &bindings)?;
                let body_res = tc_term_rec(body, false, env);
                let popped = env.local.scope_pop(this);
                let body_rec = body_res?;
                popped?;
                Ok(env.arena.let_term(bindings, body_rec))
            }
            alg::Term::Exists(vs, body) | alg::Term::Forall(vs, body) => {
                tc_quantifier_scope(env, vs)?;
                let body_res = tc_term_rec(body, true, env);
                let popped = env.local.scope_pop(this);
                let body_rec = body_res?;
                let sorts = popped?;
                is_term_bool_alt(env, &body_rec, &body.display_meta_data())?;
                if matches!(this.inner().repr(), alg::Term::Forall(..)) {
                    Ok(env.arena.forall(sorts, body_rec))
                } else {
                    Ok(env.arena.exists(sorts, body_rec))
                }
            }
            alg::Term::Matching(scrutinee, cases) => {
                let scrutinee_rec = tc_term_rec(scrutinee, false, env)?;
                tc_match_arms_rec(this, scrutinee, cases, scrutinee_rec, env)
            }
            alg::Term::Annotated(t, anns) => {
                check_pattern_placement(this, anns, pattern_ok)?;
                // a nested annotation is still the body of the quantifier
                let t_rec = tc_term_rec(t, pattern_ok, env)?;
                let anns_rec = tc_attributes_rec(anns, env)?;
                Ok(env.arena.annotated(t_rec, anns_rec))
            }
            alg::Term::Eq(a, b) => {
                let a_rec = tc_term_rec(a, false, env)?;
                let b_rec = tc_term_rec(b, false, env)?;
                typed_eq(env, a_rec, b_rec, &b.display_meta_data())
            }
            alg::Term::Distinct(ts)
            | alg::Term::And(ts)
            | alg::Term::Or(ts)
            | alg::Term::Xor(ts) => {
                let recs = tc_terms_rec(ts, env)?;
                tc_nary(env, this, ts, recs)
            }
            alg::Term::Not(t) => {
                let t_rec = tc_term_rec(t, false, env)?;
                typed_not(env, t_rec, &t.display_meta_data())
            }
            alg::Term::Implies(ts, t) => {
                let recs = tc_terms_rec(ts, env)?;
                let t_rec = tc_term_rec(t, false, env)?;
                tc_implies(env, this, ts, t, recs, t_rec)
            }
            alg::Term::Ite(b, t, e) => {
                let b_rec = tc_term_rec(b, false, env)?;
                let t_rec = tc_term_rec(t, false, env)?;
                let e_rec = tc_term_rec(e, false, env)?;
                tc_ite(env, b, e, b_rec, t_rec, e_rec)
            }
        }
    }

    /// Type-check a list of terms, left to right.
    fn tc_terms_rec<St, So, T>(ts: &[T], env: &mut TCEnv<'_, '_, Sort>) -> TC<Vec<Term>>
    where
        St: AllocatableString<Arena> + Contains<T = String>,
        So: for<'a, 'b> Typecheck<TCEnv<'a, 'b, ()>, Out = Sort>,
        T: Contains<T: Repr<T = alg::Term<St, So, T>>> + Display + MetaData,
    {
        let mut recs = Vec::with_capacity(ts.len());
        let mut i = 0usize;
        while i < ts.len() {
            recs.push(tc_term_rec(&ts[i], false, env)?);
            i += 1;
        }
        Ok(recs)
    }

    /// Type-check the bindings of a `let`, left to right, each under a fresh local id.
    fn tc_let_bindings_rec<St, So, T>(
        vs: &[VarBinding<St, T>],
        env: &mut TCEnv<'_, '_, Sort>,
    ) -> TC<Vec<VarBinding<Str, Term>>>
    where
        St: AllocatableString<Arena> + Contains<T = String>,
        So: for<'a, 'b> Typecheck<TCEnv<'a, 'b, ()>, Out = Sort>,
        T: Contains<T: Repr<T = alg::Term<St, So, T>>> + Display + MetaData,
    {
        let mut bindings = Vec::with_capacity(vs.len());
        let mut i = 0usize;
        while i < vs.len() {
            let t = tc_term_rec(&vs[i].2, false, env)?;
            let sym = vs[i].0.allocate(env.arena);
            bindings.push(VarBinding(sym, env.arena.new_local(), t));
            i += 1;
        }
        Ok(bindings)
    }

    /// Type-check the arms of the match expression `this`, each under the scope its pattern binds,
    /// and build the match from them and its type-checked scrutinee.
    fn tc_match_arms_rec<St, So, T>(
        this: &T,
        scrutinee: &T,
        cases: &[alg::PatternArm<St, T>],
        scrutinee_rec: Term,
        env: &mut TCEnv<'_, '_, Sort>,
    ) -> TC<Term>
    where
        St: AllocatableString<Arena> + Contains<T = String>,
        So: for<'a, 'b> Typecheck<TCEnv<'a, 'b, ()>, Out = Sort>,
        T: Contains<T: Repr<T = alg::Term<St, So, T>>> + Display + MetaData,
    {
        let mut arms = Vec::with_capacity(cases.len());
        let mut i = 0usize;
        while i < cases.len() {
            let pattern = tc_match_case_scope(env, scrutinee, &scrutinee_rec, &cases[i])?;
            let arm_res = tc_term_rec(&cases[i].body, false, env);
            let popped = env.local.scope_pop(this);
            let arm_rec = arm_res?;
            popped?;
            arms.push(PatternArm {
                pattern,
                body: arm_rec,
            });
            i += 1;
        }
        tc_match(env, this, cases, scrutinee_rec, arms)
    }

    /// Type-check the attributes of an annotated term, left to right.
    fn tc_attributes_rec<St, So, T>(
        anns: &[alg::Attribute<St, T>],
        env: &mut TCEnv<'_, '_, Sort>,
    ) -> TC<Vec<Attribute>>
    where
        St: AllocatableString<Arena> + Contains<T = String>,
        So: for<'a, 'b> Typecheck<TCEnv<'a, 'b, ()>, Out = Sort>,
        T: Contains<T: Repr<T = alg::Term<St, So, T>>> + Display + MetaData,
    {
        let mut anns_rec = Vec::with_capacity(anns.len());
        let mut i = 0usize;
        while i < anns.len() {
            match &anns[i] {
                alg::Attribute::Pattern(ts) => {
                    let pats = tc_terms_rec(ts, env)?;
                    anns_rec.push(Attribute::Pattern(pats));
                }
                #[cfg(feature = "no-pattern")]
                alg::Attribute::NoPattern(p) => {
                    let p_rec = tc_term_rec(p, false, env)?;
                    anns_rec.push(Attribute::NoPattern(p_rec));
                }
                alg::Attribute::Keyword(kw) => anns_rec.push(Attribute::Keyword(kw.clone())),
                alg::Attribute::Constant(kw, c) => {
                    let conv = constant_conv(c, env);
                    anns_rec.push(Attribute::Constant(kw.clone(), conv));
                }
                alg::Attribute::Symbol(kw, sym) => {
                    let sym_rec = sym.allocate(env.arena);
                    anns_rec.push(Attribute::Symbol(kw.clone(), sym_rec));
                }
                alg::Attribute::Named(name) => {
                    let name_rec = name.allocate(env.arena);
                    anns_rec.push(Attribute::Named(name_rec));
                }
            }
            i += 1;
        }
        Ok(anns_rec)
    }
}

/// Reject a `:pattern` or `:no-pattern` among `anns` unless the annotated term `current` is the
/// body of a quantifier.
fn check_pattern_placement<St, T>(
    current: &T,
    anns: &[alg::Attribute<St, T>],
    pattern_ok: bool,
) -> TC<()>
where
    T: MetaData,
{
    if pattern_ok {
        return Ok(());
    }
    for ann in anns {
        let keyword = match ann {
            alg::Attribute::Pattern(_) => ":pattern",
            #[cfg(feature = "no-pattern")]
            alg::Attribute::NoPattern(_) => ":no-pattern",
            _ => continue,
        };
        return Err(format!(
            "TC: {keyword}{} may only annotate the body of a quantifier!",
            current.display_meta_data()
        ));
    }
    Ok(())
}

/// Type-check a constant, against its sort annotation if there is one.
fn tc_constant<St, So, T>(
    env: &mut TCEnv<'_, '_, Sort>,
    current: &T,
    constant: &alg::Constant<St>,
    sort: &Option<So>,
) -> TC<Term>
where
    St: AllocatableString<Arena> + Contains<T = String>,
    So: for<'a, 'b> Typecheck<TCEnv<'a, 'b, ()>, Out = Sort>,
    T: Display + MetaData,
{
    let c = constant_conv(constant, env);
    let t = typed_constant(env, c)
        .map_err(|e| format!("{e} for {current}{}", current.display_meta_data()))?;
    if let Some(sort) = sort {
        let sort = sort.type_check(&mut env.with_empty_local())?;
        let s = t.get_sort(env);
        if s != sort {
            return sort_mismatch(&sort, &s, current, &current.display_meta_data());
        }
    }
    Ok(t)
}

/// Type-check a global identifier, with its optional sort annotation.
fn tc_global<St, So, T>(
    env: &mut TCEnv<'_, '_, Sort>,
    current: &T,
    id: &alg::QualifiedIdentifier<St, So>,
    sort: &Option<So>,
) -> TC<Term>
where
    St: AllocatableString<Arena>,
    So: for<'a, 'b> Typecheck<TCEnv<'a, 'b, ()>, Out = Sort>,
    T: MetaData,
{
    let qid = id.type_check(env)?;
    let sort = match sort {
        None => None,
        Some(sort) => Some(sort.type_check(&mut env.with_empty_local())?),
    };
    app::typed_qualified_identifier(env, qid, sort, &current.display_meta_data())
}

/// Resolve a local variable against the local scope.
fn tc_local<St, So, T>(
    env: &mut TCEnv<'_, '_, Sort>,
    current: &T,
    id: &alg::Local<St, So>,
) -> TC<Term>
where
    St: AllocatableString<Arena>,
    T: MetaData,
{
    let symbol = id.symbol.allocate(env.arena);
    match env.local.lookup(&symbol) {
        None => Err(format!(
            "TC: local variable {}{} is not bound!",
            symbol.sym_quote(),
            current.display_meta_data()
        )),
        Some((id, s)) => Ok(env.arena.local(alg::Local {
            id,
            symbol,
            sort: s,
        })),
    }
}

/// Type-check a function application, given its type-checked arguments `recs`.
fn tc_app<St, So, T>(
    env: &mut TCEnv<'_, '_, Sort>,
    current: &T,
    id: &alg::QualifiedIdentifier<St, So>,
    ts: &[T],
    s: &Option<So>,
    recs: Vec<Term>,
) -> TC<Term>
where
    St: AllocatableString<Arena>,
    So: for<'a, 'b> Typecheck<TCEnv<'a, 'b, ()>, Out = Sort>,
    T: MetaData,
{
    // 1. first we make sure f is not a local variable.
    check_global_var_locally(env, id.id_str())?;
    let nf = id.type_check(env)?;

    // 2. then we associate the type-checked arguments with potential location information
    let args = ts
        .iter()
        .zip(recs)
        .map(|(a, t)| WithMeta::new(t, a.display_meta_data()))
        .collect();
    let outs = match s {
        None => None,
        Some(outs) => Some(outs.type_check(&mut env.with_empty_local())?),
    };

    app::typed_app(
        env,
        nf,
        args,
        outs,
        &id.id_str().display_meta_data(),
        &current.display_meta_data(),
    )
}

/// Push the scope of a `let` whose bindings have been type-checked.
fn tc_let_scope(env: &mut TCEnv<'_, '_, Sort>, bindings: &[VarBinding<Str, Term>]) -> TC<()> {
    let sorts = bindings
        .iter()
        .map(|v| VarBinding(v.0.clone(), v.1, v.2.get_sort(env)))
        .collect::<Vec<_>>();
    sanitize_bindings(&sorts, |v| v.0.clone())?;
    env.local.loc_inc.push(sorts);
    Ok(())
}

/// Push the scope of a quantifier.
fn tc_quantifier_scope<St, So>(env: &mut TCEnv<'_, '_, Sort>, vs: &[VarBinding<St, So>]) -> TC<()>
where
    St: AllocatableString<Arena>,
    So: for<'a, 'b> Typecheck<TCEnv<'a, 'b, ()>, Out = Sort>,
{
    if !env.meta.theories.contains(&Theory::Quantifiers) {
        return Err("TC: the current logic does not support quantifiers!".to_string());
    }
    let sorts = vs
        .iter()
        .map(|v| {
            let sym = v.0.allocate(env.arena);
            let sort = v.2.type_check(&mut env.with_empty_local())?;
            Ok(VarBinding(sym, env.arena.new_local(), sort))
        })
        .collect::<TC<Vec<_>>>()?;
    sanitize_bindings(&sorts, |v| v.0.clone())?;
    env.local.loc_inc.push(sorts);
    Ok(())
}

/// Type-check the pattern of a match arm, and push the scope of the variables it binds.
fn tc_match_case_scope<St, T>(
    env: &mut TCEnv<'_, '_, Sort>,
    scrutinee: &T,
    scrutinee_rec: &Term,
    case: &alg::PatternArm<St, T>,
) -> TC<Pattern>
where
    St: AllocatableString<Arena>,
    T: MetaData,
{
    if !env.meta.theories.contains(&Theory::Datatypes) {
        return Err("TC: current logic does not support the theory of datatypes!".into());
    }

    // We determine the sorts of constructors if not already exists
    if !env.local.scrutinee_map.contains_key(scrutinee_rec) {
        let constructors =
            tc_determine_datatype_sort_map(env, scrutinee_rec, &scrutinee.display_meta_data())?;
        env.local
            .scrutinee_map
            .insert(scrutinee_rec.clone(), constructors);
    }
    let so = scrutinee_rec.get_sort(env);
    let constructors = env.local.scrutinee_map.get(scrutinee_rec).unwrap();
    let pattern = match &case.pattern {
        alg::Pattern::Ctor(ctor) => {
            let ctr = ctor.allocate(env.arena);
            match constructors.get(&ctr) {
                None => {
                    return Err(format!(
                        "TC: case {ctr}{} is not a constructor!",
                        ctor.display_meta_data()
                    ));
                }
                Some(args) => {
                    if !args.is_empty() {
                        return Err(format!(
                            "TC: constructor {ctr}{} requires a non-empty list of arguments",
                            ctor.display_meta_data()
                        ));
                    }
                }
            }
            env.local.loc_inc.push(vec![]);
            Pattern::Ctor(ctr)
        }
        alg::Pattern::Wildcard(ctor) => {
            // in this case, [ctor] is either a wildcard variable, or a nullary constructor.
            // depending on the case, we just need to TC with an extra variable [ctor],
            // if it is a wildcard.
            let (sorts, pattern) = match ctor {
                None => (vec![], Pattern::Wildcard(None)),
                Some((ctor, _)) => {
                    let ctr = ctor.allocate(env.arena);
                    match constructors.get(&ctr) {
                        None => {
                            let id = env.arena.new_local();
                            (
                                vec![VarBinding(ctr.clone(), id, so.clone())],
                                Pattern::Wildcard(Some((ctr.clone(), id))),
                            )
                        }
                        Some(args) => {
                            if args.is_empty() {
                                (vec![], Pattern::Ctor(ctr.clone()))
                            } else {
                                return Err(format!(
                                    "TC: constructor {ctr}{} requires a non-empty list of arguments!",
                                    ctr.display_meta_data()
                                ));
                            }
                        }
                    }
                }
            };
            sanitize_bindings(&sorts, |v| v.0.clone())?;
            env.local.loc_inc.push(sorts);
            pattern
        }
        alg::Pattern::Applied { ctor, arguments } => {
            // in this case, [ctor] must be a constructor, so we must extract its signature
            // from [constructors].
            let ctr = ctor.allocate(env.arena);
            match constructors.get(&ctr) {
                None => {
                    return Err(format!(
                        "TC: {ctr}{} is not a constructor of sort {so}!",
                        ctor.display_meta_data()
                    ));
                }
                Some(sig) => {
                    // first, the signature and the provided arguments must have the same
                    // length.
                    if sig.len() != arguments.len() {
                        return Err(format!(
                            "TC: {ctr}{} include {} arguments, but {} are required of sorts {}!",
                            ctor.display_meta_data(),
                            arguments.len(),
                            sig.len(),
                            sig.iter()
                                .map(|s| s.to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                        ));
                    }
                    let arguments = arguments
                        .iter()
                        .map(|o| {
                            o.as_ref().map(|(name, _)| {
                                let symbol = name.allocate(env.arena);
                                let fresh_id = env.arena.new_local();
                                (symbol, fresh_id)
                            })
                        })
                        .collect::<Vec<_>>();
                    let sorts = arguments
                        .iter()
                        .zip(sig)
                        .filter_map(|(o, s)| {
                            o.as_ref()
                                .map(|(name, id)| alg::VarBinding(name.clone(), *id, s.clone()))
                        })
                        .collect::<Vec<_>>();
                    sanitize_bindings(&sorts, |v| v.0.clone())?;
                    env.local.loc_inc.push(sorts);
                    Pattern::Applied {
                        ctor: ctr,
                        arguments,
                    }
                }
            }
        }
    };
    Ok(pattern)
}

/// Build a match expression from its type-checked arms, checking that they are exhaustive.
fn tc_match<St, T: Display + MetaData>(
    env: &mut TCEnv<'_, '_, Sort>,
    current: &T,
    cases: &[alg::PatternArm<St, T>],
    scrutinee_rec: Term,
    cases_rec: Vec<PatternArm>,
) -> TC<Term> {
    // the parser never produces an empty match, but the unchecked API can
    let Some(first) = cases_rec.first() else {
        return Err(format!(
            "TC: match expression{} must have at least one arm!",
            current.display_meta_data()
        ));
    };
    // all arms must have the same sort as the first one
    let arm_sort = first.body.get_sort(env);
    for (case, case_rec) in cases.iter().zip(&cases_rec).skip(1) {
        let s = case_rec.body.get_sort(env);
        if s != arm_sort {
            return sort_mismatch(&arm_sort, &s, &case.body, &case.body.display_meta_data());
        }
    }
    let constructors = env.local.scrutinee_map.get(&scrutinee_rec).unwrap();
    let mut unseen_ctors: HashSet<Str> = constructors.keys().cloned().collect();
    let mut covered = false;
    for case in &cases_rec {
        match &case.pattern {
            alg::Pattern::Wildcard(_) => {
                covered = true;
                break;
            }
            alg::Pattern::Ctor(ctor) | alg::Pattern::Applied { ctor, .. } => {
                unseen_ctors.remove(ctor);
            }
        }
    }
    if unseen_ctors.is_empty() {
        covered = true;
    }
    if !covered {
        Err(format!(
            "TC: arms for constructors {} are needed in the match expression{}!",
            unseen_ctors
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            current.display_meta_data()
        ))
    } else {
        Ok(env.arena.matching(scrutinee_rec, cases_rec))
    }
}

/// Build a `distinct`, `and`, `or` or `xor` term, whichever `current` is, from its type-checked
/// arguments.
fn tc_nary<St, So, T>(
    env: &mut TCEnv<'_, '_, Sort>,
    current: &T,
    ts: &[T],
    ts_rec: Vec<Term>,
) -> TC<Term>
where
    T: Contains<T: Repr<T = alg::Term<St, So, T>>> + MetaData,
{
    match current.inner().repr() {
        alg::Term::Distinct(_) => tc_distinct(env, ts, ts_rec),
        alg::Term::And(_) => tc_and(env, current, ts, ts_rec),
        alg::Term::Or(_) => tc_or(env, current, ts, ts_rec),
        alg::Term::Xor(_) => tc_xor(env, current, ts, ts_rec),
        _ => unreachable!("tc_nary is only called on distinct, and, or and xor"),
    }
}

fn tc_distinct<T: MetaData>(
    env: &mut TCEnv<'_, '_, Sort>,
    ts: &[T],
    ts_rec: Vec<Term>,
) -> TC<Term> {
    typed_distinct(
        env,
        ts.iter()
            .zip(ts_rec)
            .map(|(t, tr)| WithMeta::new(tr, t.display_meta_data()))
            .collect(),
    )
}

fn tc_and<T: MetaData>(
    env: &mut TCEnv<'_, '_, Sort>,
    current: &T,
    ts: &[T],
    ts_rec: Vec<Term>,
) -> TC<Term> {
    if ts_rec.is_empty() {
        return Err(format!(
            "TC: 'and'{} requires at least one argument!",
            current.display_meta_data()
        ));
    }

    check_all_bool_terms(
        ts.iter()
            .zip(&ts_rec)
            .map(|(t, tr)| WithMeta::new(tr, t.display_meta_data())),
        env,
    )?;
    Ok(env.arena.and(ts_rec))
}

fn tc_or<T: MetaData>(
    env: &mut TCEnv<'_, '_, Sort>,
    current: &T,
    ts: &[T],
    ts_rec: Vec<Term>,
) -> TC<Term> {
    if ts_rec.is_empty() {
        return Err(format!(
            "TC: 'or'{} requires at least one argument!",
            current.display_meta_data()
        ));
    }

    check_all_bool_terms(
        ts.iter()
            .zip(&ts_rec)
            .map(|(t, tr)| WithMeta::new(tr, t.display_meta_data())),
        env,
    )?;
    Ok(env.arena.or(ts_rec))
}

fn tc_xor<T: MetaData>(
    env: &mut TCEnv<'_, '_, Sort>,
    current: &T,
    ts: &[T],
    ts_rec: Vec<Term>,
) -> TC<Term> {
    if ts.len() < 2 {
        return Err(format!(
            "TC: 'xor'{} requires at least two arguments!",
            current.display_meta_data()
        ));
    }

    check_all_bool_terms(
        ts.iter()
            .zip(&ts_rec)
            .map(|(t, tr)| WithMeta::new(tr, t.display_meta_data())),
        env,
    )?;
    Ok(env.arena.xor(ts_rec))
}

/// Build an implication from its type-checked premises and conclusion.
fn tc_implies<T: MetaData>(
    env: &mut TCEnv<'_, '_, Sort>,
    current: &T,
    ts: &[T],
    t: &T,
    ts_rec: Vec<Term>,
    t_rec: Term,
) -> TC<Term> {
    if ts_rec.is_empty() {
        return Err(format!(
            "TC: implies '=>'{} should take at least one antecedent!",
            current.display_meta_data()
        ));
    }
    check_all_bool_terms(
        ts.iter()
            .zip(&ts_rec)
            .map(|(t, tr)| WithMeta::new(tr, t.display_meta_data())),
        env,
    )?;

    is_term_bool_alt(env, &t_rec, &t.display_meta_data())?;
    Ok(env.arena.implies(ts_rec, t_rec))
}

/// Build an `ite` term from its type-checked condition and branches.
fn tc_ite<T: Display + MetaData>(
    env: &mut TCEnv<'_, '_, Sort>,
    b: &T,
    e: &T,
    b_rec: Term,
    t_rec: Term,
    e_rec: Term,
) -> TC<Term> {
    is_term_bool_alt(env, &b_rec, &b.display_meta_data())?;
    let ts = t_rec.get_sort(env);
    let es = e_rec.get_sort(env);
    if ts != es {
        sort_mismatch(&ts, &es, e, &e.display_meta_data())
    } else {
        Ok(env.arena.ite(b_rec, t_rec, e_rec))
    }
}

impl<Str, T> Typecheck<TCEnv<'_, '_, Sort>> for alg::Attribute<Str, T>
where
    Str: Contains<T = String>,
    T: for<'a, 'b> Typecheck<TCEnv<'a, 'b, Sort>, Out = Term>,
{
    type Out = Attribute;

    fn type_check(&self, env: &mut TCEnvGen<'_, TCLocal<Sort>>) -> TC<Self::Out> {
        match self {
            alg::Attribute::Keyword(kw) => Ok(Attribute::Keyword(kw.clone())),
            alg::Attribute::Constant(kw, c) => {
                Ok(Attribute::Constant(kw.clone(), constant_conv(c, env)))
            }
            alg::Attribute::Symbol(kw, sym) => Ok(Attribute::Symbol(
                kw.clone(),
                env.arena.allocate_symbol(sym.inner()),
            )),
            alg::Attribute::Named(s) => Ok(Attribute::Named(env.arena.allocate_symbol(s.inner()))),
            alg::Attribute::Pattern(ts) => Ok(Attribute::Pattern(
                ts.iter()
                    .map(|t| t.type_check(env))
                    .collect::<TC<Vec<_>>>()?,
            )),
            #[cfg(feature = "no-pattern")]
            alg::Attribute::NoPattern(t) => Ok(Attribute::NoPattern(t.type_check(env)?)),
        }
    }
}

#[cfg(test)]
mod stack_safety {
    use crate::allocator::ObjectAllocatorExt;
    use crate::ast::{AlphaEquiv, Context, ScopedSortApi, Sort, Typecheck};

    /// `Array Int (Array Int (… Int))`, nested `depth` deep.
    fn deep_array(ctx: &mut Context, depth: usize) -> Sort {
        let mut s = ctx.int_sort();
        for _ in 0..depth {
            let idx = ctx.int_sort();
            s = ctx.array_sort(idx, s);
        }
        s
    }

    /// Re-checking a typed sort walks it the same way checking an untyped one does.
    #[test]
    fn tc_sort_is_flat() {
        let ok = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut ctx = Context::new();
                ctx.ensure_logic();
                let s = deep_array(&mut ctx, 100_000);
                let mut env = ctx.get_sort_tcenv();
                let checked = s.type_check(&mut env).unwrap();
                let r = checked == s;
                std::mem::forget((s, checked));
                r
            })
            .expect("spawn")
            .join();
        assert_eq!(ok.ok(), Some(true));
    }

    /// `(let ((x true)) (not (forall ((y Int)) (and x (=> x (ite x … x x))))))`, a cycle of five
    /// constructs nested `depth` cycles deep, so every scoped and unscoped kind of node recurses.
    fn deep_term_str(depth: usize) -> String {
        let mut s = String::new();
        for _ in 0..depth {
            s.push_str("(let ((x true)) (not (forall ((y Int)) (and x (=> x (ite x ");
        }
        s.push('x');
        for _ in 0..depth {
            s.push_str(" x))))))");
        }
        s
    }

    /// Checking an untyped term, and then re-checking the typed result.
    #[test]
    fn tc_term_is_flat() {
        let ok = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut ctx = Context::new();
                ctx.ensure_logic();
                let src = deep_term_str(5_000);
                let t = crate::untyped::UntypedAst.parse_term_str(&src).unwrap();
                let checked = t.type_check(&mut ctx).unwrap();
                let rechecked = checked.type_check(&mut ctx).unwrap();
                // re-checking gives every binder a fresh local id
                let r = checked.aeq(&rechecked);
                std::mem::forget((t, checked, rechecked));
                r
            })
            .expect("spawn")
            .join();
        assert_eq!(ok.ok(), Some(true));
    }
}

#[cfg(test)]
mod pattern_placement {
    use crate::ast::{Context, Typecheck};
    use crate::untyped::UntypedAst;

    fn check(src: &str) -> Result<(), String> {
        let mut ctx = Context::new();
        let decls = "(set-logic ALL)(declare-fun p (Int) Bool)(declare-fun f (Int) Int)";
        UntypedAst
            .parse_script_str(decls)
            .unwrap()
            .type_check(&mut ctx)?;
        let t = UntypedAst.parse_term_str(src).unwrap();
        t.type_check(&mut ctx).map(|_| ())
    }

    #[test]
    fn a_pattern_on_a_quantifier_body_is_accepted() {
        for src in [
            "(forall ((x Int)) (! (p x) :pattern ((p x))))",
            "(exists ((x Int)) (! (p x) :pattern ((f x)) :pattern ((p x))))",
            // a nested annotation is still the body
            "(forall ((x Int)) (! (! (p x) :pattern ((p x))) :named n))",
            "(forall ((x Int)) (! (! (p x) :named n) :pattern ((p x))))",
        ] {
            assert_eq!(check(src), Ok(()), "{src}");
        }
    }

    #[test]
    fn a_pattern_anywhere_else_is_rejected() {
        for src in [
            // the case of #166
            "(! (p 0) :pattern ((p 0)))",
            "(and (p 0) (! (p 1) :pattern ((p 1))))",
            // inside a quantifier, but not its body
            "(forall ((x Int)) (and (p x) (! (p x) :pattern ((p x)))))",
            "(forall ((x Int)) (let ((y x)) (! (p y) :pattern ((p y)))))",
            "(forall ((x Int)) (not (! (p x) :pattern ((p x)))))",
            // a pattern term is not a quantifier body either
            "(forall ((x Int)) (! (p x) :pattern ((! (p x) :pattern ((p x))))))",
        ] {
            let r = check(src);
            assert!(
                r.as_ref().is_err_and(|e| e.contains(":pattern")),
                "{src} gave {r:?}"
            );
        }
    }

    #[cfg(feature = "no-pattern")]
    #[test]
    fn no_pattern_follows_the_same_rule() {
        assert_eq!(
            check("(forall ((x Int)) (! (p x) :no-pattern (f x)))"),
            Ok(())
        );
        let r = check("(! (p 0) :no-pattern (f 0))");
        assert!(
            r.as_ref().is_err_and(|e| e.contains(":no-pattern")),
            "{r:?}"
        );
    }
}
