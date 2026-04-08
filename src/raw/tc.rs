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
use super::alg::VarBinding;
use super::instance::{
    Arena, Attribute, Constant, DatatypeDec, Identifier, Index, Pattern, PatternArm,
    QualifiedIdentifier, Sort, SortDef, Str, Term,
};
use crate::allocator::*;
use crate::ast::utils::is_term_bool_alt;
use crate::ast::{
    Context, ContextFrame, ContextMeta, FetchSort, HasArenaAlt, Monomorphization, SymbolQuote,
    TermRecursor, Theory,
};
use crate::containers::{LocEnv, Mapping, sanitize_bindings};
use crate::meta::WithMeta;
use crate::statics::{BITVEC, BOOL, INT, REAL, STRING};
use crate::traits::{AllocatableString, Contains};
use crate::traits::{MetaData, Repr};
pub(crate) use app::{typed_app, typed_qualified_identifier};
use dashu::integer::UBig;
use num_traits::cast::ToPrimitive;
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use unif::SortSubst;
use yaspar::ast::Keyword;

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
/// and [`ContextFrame`] (sorts and symbol table), plus a generic `Local` scope.
/// The `Local` parameter is [`TCLocal`] during normal type-checking, but can be
/// any type implementing [`Mapping`] for reuse in helper functions.
pub struct TCEnvGen<'a, Local> {
    pub(crate) arena: &'a mut Arena,
    pub(crate) meta: &'a ContextMeta,
    pub(crate) frame: &'a ContextFrame,
    pub(crate) local: Local,
}

impl<'a, Local> TCEnvGen<'a, Local> {
    /// Create a new environment from a [`Context`] and a local scope.
    pub(crate) fn new(context: &'a mut Context, local: Local) -> Self {
        Self {
            arena: &mut context.arena,
            meta: &context.meta,
            frame: &context.frame,
            local,
        }
    }

    /// Look up a sort definition by name, allocating the symbol in the arena.
    fn get_sort_def(&mut self, s: &str) -> TC<&'a SortDef> {
        let symbol = self.arena.allocate_symbol(s);
        match self.frame.sorts.get(&symbol) {
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
    pub(crate) fn with_empty_local<L: Mapping>(&mut self) -> TCEnvGen<'_, L> {
        TCEnvGen {
            arena: self.arena,
            meta: self.meta,
            frame: self.frame,
            local: L::empty(),
        }
    }

    pub(crate) fn convert_to_empty_local<L: Mapping>(self) -> TCEnvGen<'a, L> {
        TCEnvGen {
            arena: self.arena,
            meta: self.meta,
            frame: self.frame,
            local: L::empty(),
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
            frame: self.frame,
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
    } else if let Some(d) = env.frame.sorts.get(&id.symbol) {
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
    L: Mapping<Key = Str, Value = (usize, ())>,
{
    type Out = Sort;

    fn type_check(&self, env: &mut TCEnvGen<L>) -> TC<Self::Out> {
        let sorts = self
            .inner()
            .repr()
            .1
            .iter()
            .map(|s| s.type_check(env))
            .collect::<TC<Vec<_>>>()?;
        tc_sort(env, &self.inner().repr().0, sorts)
    }
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
    type Value = (usize, T);

    fn empty() -> Self {
        Default::default()
    }

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

impl<St, So, T> TermRecursor<St, So, T> for TCEnv<'_, '_, Sort>
where
    St: AllocatableString<Arena> + Contains<T = String>,
    So: for<'a, 'b> Typecheck<TCEnv<'a, 'b, ()>, Out = Sort>,
    T: Display + MetaData,
{
    type Out = Term;
    type Attr = Attribute;
    type Binding = VarBinding<Str, Term>;
    type Pattern = Pattern;
    type Arm = PatternArm;
    type Err = String;

    fn on_constant(
        &mut self,
        current: &T,
        constant: &alg::Constant<St>,
        sort: &Option<So>,
    ) -> TC<Term> {
        let c = constant_conv(constant, self);
        let t = typed_constant(self, c)
            .map_err(|e| format!("{e} for {current}{}", current.display_meta_data()))?;
        if let Some(sort) = sort {
            let sort = sort.type_check(&mut self.with_empty_local())?;
            let s = t.get_sort(self);
            if s != sort {
                return sort_mismatch(&sort, &s, current, &current.display_meta_data());
            }
        }
        Ok(t)
    }

    fn on_global(
        &mut self,
        current: &T,
        id: &alg::QualifiedIdentifier<St, So>,
        sort: &Option<So>,
    ) -> TC<Term> {
        let qid = id.type_check(self)?;
        let sort = match sort {
            None => None,
            Some(sort) => Some(sort.type_check(&mut self.with_empty_local())?),
        };
        app::typed_qualified_identifier(self, qid, sort, &current.display_meta_data())
    }

    fn on_local(&mut self, current: &T, id: &alg::Local<St, So>) -> TC<Term> {
        let symbol = id.symbol.allocate(self.arena);
        match self.local.lookup(&symbol) {
            None => Err(format!(
                "TC: local variable {}{} is not bound!",
                symbol.sym_quote(),
                current.display_meta_data()
            )),
            Some((id, s)) => Ok(self.arena.local(alg::Local {
                id,
                symbol,
                sort: Some(s),
            })),
        }
    }

    fn on_app(
        &mut self,
        current: &T,
        id: &alg::QualifiedIdentifier<St, So>,
        ts: &[T],
        s: &Option<So>,
        recs: Vec<Self::Out>,
    ) -> TC<Term> {
        // 1. first we make sure f is not a local variable.
        check_global_var_locally(self, id.id_str())?;
        let nf = id.type_check(self)?;

        // 2. then we associate the type-checked arguments with potential location information
        let args = ts
            .iter()
            .zip(recs)
            .map(|(a, t)| WithMeta::new(t, a.display_meta_data()))
            .collect();
        let outs = match s {
            None => None,
            Some(outs) => Some(outs.type_check(&mut self.with_empty_local())?),
        };

        app::typed_app(
            self,
            nf,
            args,
            outs,
            &id.id_str().display_meta_data(),
            &current.display_meta_data(),
        )
    }

    fn on_let_binding(
        &mut self,
        _current: &T,
        vs: &[VarBinding<St, T>],
        _body: &T,
        binding_idx: usize,
        binding_rec: Self::Out,
    ) -> Result<Self::Binding, Self::Err> {
        let v = &vs[binding_idx];
        let sym = v.0.allocate(self.arena);
        let new_id = self.arena.new_local();
        Ok(VarBinding(sym, new_id, binding_rec))
    }

    fn setup_let_scope(
        &mut self,
        _current: &T,
        _vs: &[VarBinding<St, T>],
        _body: &T,
        vs_rec: &[Self::Binding],
    ) -> Result<(), Self::Err> {
        let sorts = vs_rec
            .iter()
            .map(|v| VarBinding(v.0.clone(), v.1, v.2.get_sort(self)))
            .collect::<Vec<_>>();
        sanitize_bindings(&sorts, |v| v.0.clone())?;
        self.local.loc_inc.push(sorts);
        Ok(())
    }

    fn on_let(
        &mut self,
        current: &T,
        _vs: &[VarBinding<St, T>],
        _body: &T,
        vs_rec: Vec<Self::Binding>,
        body_rec: Self::Out,
    ) -> TC<Term> {
        self.local.scope_pop(current)?;
        Ok(self.arena.let_term(vs_rec, body_rec))
    }

    fn setup_quantifier_scope(
        &mut self,
        _current: &T,
        vs: &[VarBinding<St, So>],
        _t: &T,
        _is_forall: bool,
    ) -> Result<(), Self::Err> {
        if !self.meta.theories.contains(&Theory::Quantifiers) {
            return Err("TC: the current logic does not support quantifiers!".to_string());
        }
        let sorts = vs
            .iter()
            .map(|v| {
                let sym = v.0.allocate(self.arena);
                let sort = v.2.type_check(&mut self.with_empty_local())?;
                Ok(VarBinding(sym, self.arena.new_local(), sort))
            })
            .collect::<TC<Vec<_>>>()?;
        sanitize_bindings(&sorts, |v| v.0.clone())?;
        self.local.loc_inc.push(sorts);
        Ok(())
    }

    fn on_exists(
        &mut self,
        current: &T,
        _vs: &[VarBinding<St, So>],
        t: &T,
        t_rec: Self::Out,
    ) -> TC<Term> {
        let sorts = self.local.scope_pop(current)?;
        is_term_bool_alt(self, &t_rec, &t.display_meta_data())?;
        Ok(self.arena.exists(sorts, t_rec))
    }

    fn on_forall(
        &mut self,
        current: &T,
        _vs: &[VarBinding<St, So>],
        t: &T,
        t_rec: Self::Out,
    ) -> TC<Term> {
        let sorts =
            self.local.loc_inc.pop().ok_or_else(|| {
                format!("TC: scoping error, failed to manage scope for {current}")
            })?;
        is_term_bool_alt(self, &t_rec, &t.display_meta_data())?;
        Ok(self.arena.forall(sorts, t_rec))
    }

    fn setup_match_case_scope(
        &mut self,
        _current: &T,
        scrutinee: &T,
        cases: &[alg::PatternArm<St, T>],
        scrutinee_rec: &Self::Out,
        case_idx: usize,
    ) -> TC<Self::Pattern> {
        if !self.meta.theories.contains(&Theory::Datatypes) {
            return Err("TC: current logic does not support the theory of datatypes!".into());
        }

        // We determine the sorts of constructors if not already exists
        if !self.local.scrutinee_map.contains_key(scrutinee_rec) {
            let constructors = tc_determine_datatype_sort_map(
                self,
                scrutinee_rec,
                &scrutinee.display_meta_data(),
            )?;
            self.local
                .scrutinee_map
                .insert(scrutinee_rec.clone(), constructors);
        }
        let so = scrutinee_rec.get_sort(self);
        let constructors = self.local.scrutinee_map.get(scrutinee_rec).unwrap();
        let case = &cases[case_idx];
        let pattern = match &case.pattern {
            alg::Pattern::Ctor(ctor) => {
                let ctr = ctor.allocate(self.arena);
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
                self.local.loc_inc.push(vec![]);
                Pattern::Ctor(ctr)
            }
            alg::Pattern::Wildcard(ctor) => {
                // in this case, [ctor] is either a wildcard variable, or a nullary constructor.
                // depending on the case, we just need to TC with an extra variable [ctor],
                // if it is a wildcard.
                let (sorts, pattern) = match ctor {
                    None => (vec![], Pattern::Wildcard(None)),
                    Some((ctor, _)) => {
                        let ctr = ctor.allocate(self.arena);
                        match constructors.get(&ctr) {
                            None => {
                                let id = self.arena.new_local();
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
                self.local.loc_inc.push(sorts);
                pattern
            }
            alg::Pattern::Applied { ctor, arguments } => {
                // in this case, [ctor] must be a constructor, so we must extract its signature
                // from [constructors].
                let ctr = ctor.allocate(self.arena);
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
                                    let symbol = name.allocate(self.arena);
                                    let fresh_id = self.arena.new_local();
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
                        self.local.loc_inc.push(sorts);
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

    fn on_match_arm(
        &mut self,
        current: &T,
        _scrutinee: &T,
        _cases: &[alg::PatternArm<St, T>],
        _case_idx: usize,
        current_pattern: Self::Pattern,
        arm: Self::Out,
    ) -> Result<Self::Arm, Self::Err> {
        self.local.scope_pop(current)?;
        Ok(PatternArm {
            pattern: current_pattern,
            body: arm,
        })
    }

    fn on_match(
        &mut self,
        current: &T,
        _scrutinee: &T,
        _cases: &[alg::PatternArm<St, T>],
        scrutinee_rec: Self::Out,
        cases_rec: Vec<Self::Arm>,
    ) -> TC<Term> {
        let constructors = self.local.scrutinee_map.get(&scrutinee_rec).unwrap();
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
            Ok(self.arena.matching(scrutinee_rec, cases_rec))
        }
    }

    fn on_annotated(
        &mut self,
        _current: &T,
        _t: &T,
        _anns: &[alg::Attribute<St, T>],
        t_rec: Self::Out,
        anns_rec: Vec<Self::Attr>,
    ) -> TC<Term> {
        Ok(self.arena.annotated(t_rec, anns_rec))
    }

    fn on_attribute_keyword(&mut self, keyword: &Keyword) -> Result<Self::Attr, Self::Err> {
        Ok(Attribute::Keyword(keyword.clone()))
    }

    fn on_attribute_constant(
        &mut self,
        keyword: &Keyword,
        constant: &alg::Constant<St>,
    ) -> Result<Self::Attr, Self::Err> {
        Ok(Attribute::Constant(
            keyword.clone(),
            constant_conv(constant, self),
        ))
    }

    fn on_attribute_symbol(
        &mut self,
        keyword: &Keyword,
        symbol: &St,
    ) -> Result<Self::Attr, Self::Err> {
        Ok(Attribute::Symbol(
            keyword.clone(),
            symbol.allocate(self.arena),
        ))
    }

    fn on_attribute_named(&mut self, _current: &T, name: &St) -> TC<Self::Attr> {
        Ok(Attribute::Named(name.allocate(self.arena)))
    }

    fn on_attribute_pattern(
        &mut self,
        _patterns: &[T],
        patterns_rec: Vec<Self::Out>,
    ) -> Result<Self::Attr, Self::Err> {
        Ok(Attribute::Pattern(patterns_rec))
    }

    fn on_eq(
        &mut self,
        _current: &T,
        _a: &T,
        b: &T,
        a_rec: Self::Out,
        b_rec: Self::Out,
    ) -> TC<Term> {
        typed_eq(self, a_rec, b_rec, &b.display_meta_data())
    }

    fn on_distinct(&mut self, _current: &T, ts: &[T], ts_rec: Vec<Self::Out>) -> TC<Term> {
        typed_distinct(
            self,
            ts.iter()
                .zip(ts_rec)
                .map(|(t, tr)| WithMeta::new(tr, t.display_meta_data()))
                .collect(),
        )
    }

    fn on_and(&mut self, current: &T, ts: &[T], ts_rec: Vec<Self::Out>) -> TC<Term> {
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
            self,
        )?;
        Ok(self.arena.and(ts_rec))
    }

    fn on_or(&mut self, current: &T, ts: &[T], ts_rec: Vec<Self::Out>) -> TC<Term> {
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
            self,
        )?;
        Ok(self.arena.or(ts_rec))
    }

    fn on_xor(&mut self, current: &T, ts: &[T], ts_rec: Vec<Self::Out>) -> TC<Term> {
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
            self,
        )?;
        Ok(self.arena.xor(ts_rec))
    }

    fn on_not(&mut self, _current: &T, t: &T, t_rec: Self::Out) -> TC<Term> {
        typed_not(self, t_rec, &t.display_meta_data())
    }

    fn on_implies(
        &mut self,
        current: &T,
        ts: &[T],
        t: &T,
        ts_rec: Vec<Self::Out>,
        t_rec: Self::Out,
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
            self,
        )?;

        is_term_bool_alt(self, &t_rec, &t.display_meta_data())?;
        Ok(self.arena.implies(ts_rec, t_rec))
    }

    fn on_ite(
        &mut self,
        _current: &T,
        b: &T,
        _t: &T,
        e: &T,
        b_rec: Self::Out,
        t_rec: Self::Out,
        e_rec: Self::Out,
    ) -> TC<Term> {
        is_term_bool_alt(self, &b_rec, &b.display_meta_data())?;
        let ts = t_rec.get_sort(self);
        let es = e_rec.get_sort(self);
        if ts != es {
            sort_mismatch(&ts, &es, e, &e.display_meta_data())
        } else {
            Ok(self.arena.ite(b_rec, t_rec, e_rec))
        }
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
        env.recurse_on_term(self)
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
        }
    }
}
