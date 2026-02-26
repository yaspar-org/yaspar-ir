// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Type-checking
//!
//! This module checks an object and returns its corresponding typed representation.
//!
//! This module is organized in a form of constraint programming. It has the advantage of being able
//! to apply to different instantiations of the algebraic ASTs in [crate::raw::alg].
//!
//! One example application is to invoke `.type_check()` on a typed AST that is built by a user
//! using unchecked APIs. In this case, during developing, `.type_check()` can be invoked as a golden
//! standard and a single point of failure to ensure the AST properly maintains type invariants.

use super::alg;
use super::alg::VarBinding;
use super::instance::{
    Arena, Attribute, BvInSort, BvOutSort, Constant, DatatypeDec, Identifier, Index, Pattern,
    QualifiedIdentifier, Sig, SigIndex, Sort, SortDef, Str, Term,
};
use crate::allocator::*;
use crate::ast::utils::is_term_bool_alt;
use crate::ast::{FetchSort, FunctionMeta, HasArenaAlt, SymbolQuote, Theory};
use crate::locenv::LocEnv;
use crate::meta::WithMeta;
use crate::statics::{BITVEC, BOOL, BV_RE, INT, REAL, STRING};
use crate::traits::{AllocatableString, Contains};
use crate::traits::{MetaData, Repr};
use dashu::base::BitTest;
use dashu::integer::UBig;
use either::Either;
use num_traits::cast::ToPrimitive;
use regex::Captures;
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::str::FromStr;

/// Type-checking monad
pub type TC<T> = Result<T, String>;

/// The trait for type-checking
pub trait Typecheck<Env> {
    type Out;

    fn type_check(&self, env: &mut Env) -> TC<Self::Out>;
}

/// An extended environment to get below binders
pub struct TCEnv<'a, 'b, S> {
    pub(crate) arena: &'a mut Arena,
    pub(crate) theories: &'static HashSet<Theory>,
    pub(crate) sorts: &'a HashMap<Str, SortDef>,
    pub(crate) symbol_table: &'a HashMap<Str, Vec<(Sig, FunctionMeta)>>,
    pub(crate) local: LocEnv<'b, Str, S>,
}

impl<'a, 'b, S> TCEnv<'a, 'b, S> {
    pub(crate) fn convert_to_new_local<'c, T>(self, local: LocEnv<'c, Str, T>) -> TCEnv<'a, 'c, T> {
        TCEnv {
            arena: self.arena,
            theories: self.theories,
            sorts: self.sorts,
            symbol_table: self.symbol_table,
            local,
        }
    }

    pub(crate) fn with_empty_local<T>(&mut self) -> TCEnv<'_, 'static, T> {
        TCEnv {
            arena: self.arena,
            theories: self.theories,
            sorts: self.sorts,
            symbol_table: self.symbol_table,
            local: LocEnv::Nil,
        }
    }

    pub(crate) fn convert_to_empty_local<T>(self) -> TCEnv<'a, 'static, T> {
        TCEnv {
            arena: self.arena,
            theories: self.theories,
            sorts: self.sorts,
            symbol_table: self.symbol_table,
            local: LocEnv::Nil,
        }
    }

    pub(crate) fn push_local<'d>(
        &'d mut self,
        head: &'d [VarBinding<Str, S>],
    ) -> TC<TCEnv<'d, 'd, S>>
    where
        S: Clone,
    {
        let local = self.local.insert(head)?;
        Ok(TCEnv {
            arena: self.arena,
            theories: self.theories,
            sorts: self.sorts,
            symbol_table: self.symbol_table,
            local,
        })
    }

    fn get_sort_def(&mut self, s: &str) -> TC<&'a SortDef> {
        let symbol = self.arena.allocate_symbol(s);
        match self.sorts.get(&symbol) {
            None => Err(format!("TC: unknown sort: {}!", s)),
            Some(d) => Ok(d),
        }
    }

    /// Get the sort of `s` if it's a ground sort, i.e. a sort with no parametricity.
    fn get_ground_sort(&mut self, s: &str) -> TC<Sort> {
        match self.get_sort_def(s)? {
            SortDef::Opaque(n) => {
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
    pub(crate) fn get_datatype_dec(&mut self, s: &str) -> TC<&'a DatatypeDec> {
        match self.get_sort_def(s)? {
            SortDef::Datatype(d) => Ok(d),
            _ => Err(format!("TC: sort {} is not datatype!", s)),
        }
    }
}

impl<T> HasArenaAlt for TCEnv<'_, '_, T> {
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

impl<Str> Typecheck<TCEnv<'_, '_, Sort>> for alg::Constant<Str> {
    type Out = Sort;

    fn type_check(&self, env: &mut TCEnv<Sort>) -> TC<Sort> {
        match self {
            alg::Constant::Numeral(_) => {
                if env.theories.contains(&Theory::Reals) {
                    env.get_ground_sort(REAL)
                } else {
                    env.get_ground_sort(INT)
                }
            }
            alg::Constant::Decimal(_) => env.get_ground_sort(REAL),
            alg::Constant::String(_) => env.get_ground_sort(STRING),
            alg::Constant::Binary(_, n) => {
                if env.theories.contains(&Theory::Bitvectors) {
                    valid_bv_sort(env, UBig::from(*n))
                } else {
                    Err("TC: the current logic does not support bit vectors!".into())
                }
            }
            alg::Constant::Hexadecimal(_, n) => {
                if env.theories.contains(&Theory::Bitvectors) {
                    valid_bv_sort(env, UBig::from(4u8) * UBig::from(*n))
                } else {
                    Err("TC: the current logic does not support bit vectors!".into())
                }
            }
            alg::Constant::Bool(_) => env.get_ground_sort(BOOL),
        }
    }
}

fn identifier_not_found<T>(symbol: &Str, meta_string: &str) -> TC<T> {
    Err(format!(
        "TC: identifier {}{meta_string} does not exist!",
        symbol.sym_quote()
    ))
}

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

pub(crate) fn check_subst_instantiation(subst: &SortSubst, t: impl Display) -> TC<()> {
    let vs = subst_missed_vars(subst);
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

fn check_global_var_locally<T: Clone, S>(env: &mut TCEnv<T>, s: S) -> TC<Str>
where
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

fn tc_vec_sort_bool<T>(ts: &[T], env: &mut TCEnv<Sort>) -> TC<Vec<Term>>
where
    T: for<'a, 'b> Typecheck<TCEnv<'a, 'b, Sort>, Out = Term> + Display + MetaData,
{
    let mut result = vec![];
    for t in ts {
        let nt = t.type_check(env)?;
        is_term_bool_alt(env, &nt, &t.display_meta_data())?;
        result.push(nt);
    }
    Ok(result)
}

fn tc_with_local_env<T>(vs: &[VarBinding<Str, Sort>], t: &T, env: &mut TCEnv<Sort>) -> TC<Term>
where
    T: for<'a, 'b> Typecheck<TCEnv<'a, 'b, Sort>, Out = Term>,
{
    let mut ext_env = env.push_local(vs)?;
    t.type_check(&mut ext_env)
}

pub(crate) fn tc_binder<St, So, T>(
    vs: &[VarBinding<St, So>],
    t: &T,
    env: &mut TCEnv<Sort>,
) -> TC<(Vec<VarBinding<Str, Sort>>, Term)>
where
    St: Contains<T = String>,
    So: for<'a, 'b> Typecheck<TCEnv<'a, 'b, ()>, Out = Sort>,
    T: for<'a, 'b> Typecheck<TCEnv<'a, 'b, Sort>, Out = Term> + Display + MetaData,
{
    if !env.theories.contains(&Theory::Quantifiers) {
        return Err("TC: the current logic does not support quantifiers!".to_string());
    }
    let vs = {
        let mut env = env.with_empty_local();
        let mut ret = vec![];
        for v in vs {
            let sym = env.arena.allocate_symbol(v.0.inner());
            let vid = env.arena.new_local();
            ret.push(alg::VarBinding(sym, vid, v.2.type_check(&mut env)?));
        }
        ret
    };
    let nt = tc_with_local_env(&vs, t, env)?;
    is_term_bool_alt(env, &nt, &t.display_meta_data())?;
    Ok((vs, nt))
}

/// A [SortSubst] is a substitution from sort variables to ground sorts (sorts with no open variables)
pub(crate) type SortSubst = HashMap<Str, Option<Sort>>;

/// Unify a ground sort with an expected sort with potential open sort variables; update the
/// substitution if necessary
fn sort_unification(subst: &mut SortSubst, expected: &Sort, ground: &Sort) -> TC<bool> {
    // 1. if [ground] has arity > 0, then it's not possible for [expected] itself to be parametric
    if ground.1.is_empty() {
        // 2. in this case, it is possible for expected to be a variable, so we must check it
        let esymb = &expected.repr().0.symbol;
        if let Some(v) = subst.get(esymb) {
            // 3. then it is a variable,
            match v {
                None => {
                    // 3.1. but this variable is not unified, so we unify it with a ground type
                    subst.insert(esymb.clone(), Some(ground.clone()));
                    Ok(true)
                }
                Some(v) => Ok(*v == *ground), // otherwise, we must make sure the unified sort matches with [ground]
            }
        } else {
            // 3. then expected and ground must be equal
            Ok(*expected == *ground)
        }
    } else if expected.1.len() != ground.1.len() {
        Err(format!(
            "TC: sort mismatch: {} and {} cannot be unified!",
            ground, expected
        ))
    } else {
        // 2. [expected] and [ground]'s sort parameters are recursively unified
        for (e, g) in expected.1.iter().zip(ground.1.iter()) {
            if !sort_unification(subst, e, g)? {
                return Ok(false);
            }
        }
        // 3. in this case, we know all sort parameters match up, so sorts are unified
        Ok(true)
    }
}

fn empty_subst(vs: &[Str]) -> SortSubst {
    vs.iter().map(|s| (s.clone(), None)).collect()
}

/// Return variables in a substitutions that have not determined a sort
fn subst_missed_vars(subst: &SortSubst) -> Vec<Str> {
    subst
        .iter()
        .filter_map(|(k, v)| if v.is_none() { Some(k.clone()) } else { None })
        .collect()
}

pub(crate) fn apply_subst<A: HasArenaAlt>(arena: &mut A, subst: &SortSubst, s: &Sort) -> Sort {
    if s.1.is_empty() {
        let sym = &s.repr().0.symbol;
        if let Some(Some(v)) = subst.get(sym) {
            v.clone()
        } else {
            s.clone()
        }
    } else {
        let ss = s.1.iter().map(|s| apply_subst(arena, subst, s)).collect();
        arena.arena_alt().sort(s.repr().0.clone(), ss)
    }
}

fn format_subst(subst: &SortSubst) -> String {
    subst
        .iter()
        .map(|(k, v)| match v {
            None => {
                format!("?/{}", k)
            }
            Some(v) => {
                format!("{}/{}", v, k)
            }
        })
        .collect::<Vec<_>>()
        .join(", ")
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

/// Type-checking a sort also normalizes it
pub(crate) fn tc_sort<S>(
    env: &mut TCEnv<()>,
    id: &alg::Identifier<S>,
    sorts: impl IntoIterator<Item = Sort>,
) -> TC<Sort>
where
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
    } else if let Some(d) = env.sorts.get(&id.symbol) {
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
                SortDef::Opaque(_) => Ok(env.arena.sort_n(id.symbol, sorts)),
                SortDef::Datatype(_) => Ok(env.arena.sort_n(id.symbol, sorts)),
                SortDef::Transparent { params, sort } => {
                    // when there sort is transparent, we substitute its definition
                    let subst: SortSubst = params
                        .iter()
                        .cloned()
                        .zip(sorts)
                        .map(|(k, v)| (k, Some(v)))
                        .collect();
                    let s = apply_subst(env, &subst, sort);
                    Ok(s)
                }
            }
        }
    } else if env.theories.contains(&Theory::Bitvectors) && id.symbol.inner() == BITVEC {
        // this is a special case; admit (_ BitVec X) where X is a numeral
        let sorts = sorts.into_iter().collect::<Vec<_>>();
        match id.indices.as_slice() {
            [Index::Numeral(sz)] if sorts.is_empty() => valid_bv_sort(env, sz.clone()),
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

impl<Str, So> Typecheck<TCEnv<'_, '_, ()>> for So
where
    Str: AllocatableString<Arena>,
    So: Contains<T: Repr<T = alg::Sort<Str, So>>> + Display,
{
    type Out = Sort;

    fn type_check(&self, env: &mut TCEnv<()>) -> TC<Self::Out> {
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

/// Check whether `t` is an argument given an `expected` sort and a `subst`itution.
///
/// Return `Right(nt)` where `nt` is the potentially new term for the argument, or `Left(s)` if
/// `t` should be rejected, where `s` is the actual sort.
fn type_check_func_arg_with_implicit_coercion(
    env: &mut TCEnv<Sort>,
    t: &Term,
    expected: &Sort,
    subst: &mut SortSubst,
) -> TC<Either<Sort, Term>> {
    let ns = t.get_sort(env);
    let unifiable = sort_unification(subst, expected, &ns)?;
    if unifiable {
        return Ok(Either::Right(t.clone()));
    }
    // if the sorts are not unifiable, then there are two possibilities.
    // 1. if Reals_Ints is not a current theory, then we don't do anything, i.e. reject t as an argument.
    if !env.theories.contains(&Theory::RealInts) {
        return Ok(Either::Left(ns));
    }

    // 2. otherwise, we have to check whether there should be an implicit coercion.
    let expected_substed = apply_subst(env, subst, expected);
    if ns.is_int() && expected_substed.is_real() {
        // 3. if `t` has sort `Int` and is expected to have sort `Real`, then `to_real` is inserted.
        // this seems to be the only specified implicit coercion in the spec, so we just handle it
        // in the current way.
        //
        // c.f. https://smt-lib.org/logics-all.shtml#AUFNIRA
        let to_real = check_global_var_locally(env, "to_real")?; // this should pass for the sake of symbol table declaration.
        let to_real = QualifiedIdentifier::simple(to_real);
        let real = env.arena.real_sort();
        let coerced = env.arena.app(to_real, vec![t.clone()], Some(real));
        Ok(Either::Right(coerced))
    } else {
        // 4. otherwise, we reject t as an argument
        Ok(Either::Left(ns))
    }
}

/// Unify bit vector len variable
fn bv_len_unification(params: &mut [Option<UBig>], expected: UBig, idx: usize) -> TC<bool> {
    if idx >= params.len() {
        return Err(format!("TC: index {idx} is out of bounds!"));
    }
    if let Some(ex) = &params[idx] {
        Ok(*ex == expected)
    } else {
        if expected.is_zero() {
            return Err("TC: bit vector cannot have length 0!".to_string());
        }
        params[idx] = Some(expected);
        Ok(true)
    }
}

fn check_bv_param_instantiation(params: Vec<Option<UBig>>) -> TC<Vec<UBig>> {
    let mut ret = vec![];
    for (i, p) in params.into_iter().enumerate() {
        if let Some(p) = p {
            ret.push(p);
        } else {
            return Err(format!("TC: index {i} is not instantiated!"));
        }
    }
    Ok(ret)
}

fn bv_len_apply<T: HasArenaAlt>(env: &mut T, out: &BvOutSort, params: &[UBig]) -> TC<Sort> {
    match out {
        BvOutSort::BitVec(expr) => {
            let len = expr.eval(params)?;
            valid_bv_sort(env, len)
        }
        BvOutSort::Sort(s) => Ok(s.clone()),
    }
}

fn type_check_bv_func_arg_with_implicit_coercion(
    env: &mut TCEnv<Sort>,
    t: &Term,
    expected: &BvInSort,
    params: &mut [Option<UBig>],
) -> TC<Either<Sort, Term>> {
    match expected {
        BvInSort::Sort(s) => {
            type_check_func_arg_with_implicit_coercion(env, t, s, &mut HashMap::new())
        }
        BvInSort::BitVec(n) => {
            let ns = t.get_sort(env);
            if let Some(len) = ns.is_bv() {
                // t has sort (_ BitVec len)
                if !bv_len_unification(params, len, *n)? {
                    Err(format!(
                        "TC: bit vector sort {ns} cannot be unified with length {}!",
                        params[*n].clone().unwrap()
                    ))
                } else {
                    Ok(Either::Right(t.clone()))
                }
            } else {
                Ok(Either::Left(ns))
            }
        }
    }
}

fn type_check_with_func_sig(
    t: impl Display,
    env: &mut TCEnv<Sort>,
    f: WithMeta<&QualifiedIdentifier, &str>,
    args: &[WithMeta<Term, String>],
    outs: &Option<Sort>,
    sig: &Sig,
    app_string: &str,
) -> TC<Term> {
    let WithMeta {
        data: f,
        meta: f_meta,
    } = f;
    match sig {
        Sig::VarLenFunc(s, n, o) => {
            // 3.0 overloaded functions don't take indices
            check_empty_index(f, f_meta)?;

            // 3.1 make sure all arguments have the expected sort [s]
            let mut new_args = vec![];
            for (
                i,
                WithMeta {
                    data: nt,
                    meta: nt_meta,
                },
            ) in args.iter().enumerate()
            {
                match type_check_func_arg_with_implicit_coercion(env, nt, s, &mut HashMap::new())? {
                    Either::Left(ns) => {
                        return Err(format!(
                            "TC: the {i}'th argument{nt_meta} of function '{}' expects sort {s} but was given {ns}!",
                            f.id_str().sym_quote(),
                        ));
                    }
                    Either::Right(t) => {
                        new_args.push(t);
                    }
                }
            }

            if new_args.len() < *n {
                return Err(format!(
                    "TC: function '{}'{f_meta} expects at least {} argument(s)!",
                    f.id_str().sym_quote(),
                    n
                ));
            }

            // 3.2 if sorts of the overall application is ascribed, then this sort must also match.
            if let Some(fs) = &f.1
                && *fs != *o
            {
                return sort_mismatch(fs, o, t, app_string);
            }

            // 3.3 do the same for the ascribed sort
            if let Some(outs) = outs
                && *outs != *o
            {
                return sort_mismatch(outs, o, t, app_string);
            }

            // passing all tests
            Ok(env.arena.app(f.clone(), new_args, Some(o.clone())))
        }
        Sig::ParFunc(sig_indices, vs, ss, s) => {
            let mut subst: SortSubst = empty_subst(vs);

            // 3.0 determine the sorts for indices
            check_sig_indices(f, f_meta, sig_indices)?;

            // 3.1 # of input sorts in the signature must match # of arguments.
            check_arg_length(f, f_meta, args, ss.len())?;

            // 3.2 input sorts must match the argument sorts.
            let mut new_args = vec![];
            for (
                i,
                (
                    WithMeta {
                        data: nt,
                        meta: nt_meta,
                    },
                    s,
                ),
            ) in args.iter().zip(ss).enumerate()
            {
                match type_check_func_arg_with_implicit_coercion(env, nt, s, &mut subst)? {
                    Either::Left(ns) => {
                        return Err(format!(
                            "TC: the {i}'th argument{nt_meta} of function '{}' expects sort {s} but was given {ns}! subst: {}",
                            f.id_str().sym_quote(),
                            format_subst(&subst)
                        ));
                    }
                    Either::Right(nt) => new_args.push(nt),
                }
            }

            // 3.3 if sorts of the overall application is ascribed, then this sort must also match.
            if let Some(fs) = &f.1
                && !sort_unification(&mut subst, s, fs)?
            {
                return sort_mismatch(fs, s, t, app_string);
            }

            // 3.4 do the same for the ascribed sort
            if let Some(outs) = outs
                && !sort_unification(&mut subst, s, outs)?
            {
                return sort_mismatch(outs, s, t, app_string);
            }

            // 3.5 make sure all vars in the substitution have been materialized
            check_subst_instantiation(&subst, t)?;

            // passing all tests
            let ret_sort = apply_subst(env, &subst, s);
            Ok(env.arena.app(f.clone(), new_args, Some(ret_sort)))
        }
        Sig::BvFunc(m, n, is_extract, ss, s) => {
            let mut params = vec![None; *m + *n];

            // 3.0 check indices
            check_bv_sig_indices(f, f_meta, *m, &mut params)?;
            // at this point, the first m in params are instantiated.

            // 3.1 # of input sorts in the signature must match # of arguments.
            check_arg_length(f, f_meta, args, ss.len())?;

            let mut new_args = vec![];
            for (
                i,
                (
                    WithMeta {
                        data: nt,
                        meta: nt_meta,
                    },
                    s,
                ),
            ) in args.iter().zip(ss).enumerate()
            {
                match type_check_bv_func_arg_with_implicit_coercion(env, nt, s, &mut params)? {
                    Either::Left(ns) => {
                        return Err(format!(
                            "TC: the {i}'th argument{nt_meta} of function '{}' expects sort {s} but was given {ns}!",
                            f.id_str().sym_quote(),
                        ));
                    }
                    Either::Right(nt) => new_args.push(nt),
                }
            }

            // 3.2.1 we then make sure all parameters have been instantiated
            let params = check_bv_param_instantiation(params)?;

            // 3.2.2 we obtain the output sort
            let out_sort = bv_len_apply(env, s, &params)?;

            // 3.3 if sorts of the overall application is ascribed, then this sort must also match.
            if let Some(fs) = &f.1
                && *fs != out_sort
            {
                return sort_mismatch(fs, &out_sort, t, app_string);
            }

            // 3.4 do the same for the ascribed sort
            if let Some(outs) = outs
                && *outs != out_sort
            {
                return sort_mismatch(outs, &out_sort, t, app_string);
            }

            // 3.5 special check for extract
            if *is_extract {
                for i in *m..params.len() {
                    for j in 0..*m {
                        if params[i] <= params[j] {
                            return Err(format!(
                                "TC: invalid index in bit-vector extract{f_meta}: Index {} should be less than the bit-vector width {}",
                                params[j], params[i]
                            ));
                        }
                    }
                }
            }

            Ok(env.arena.app(f.clone(), new_args, Some(out_sort)))
        }
        Sig::BvVarLenFunc(m, s, n, o) => {
            let mut params = vec![None; *m];

            // 3.0 overloaded functions don't take indices
            check_empty_index(f, app_string)?;

            // 3.1 make sure all arguments have the expected sort [s]
            let mut new_args = vec![];
            for (
                i,
                WithMeta {
                    data: nt,
                    meta: nt_meta,
                },
            ) in args.iter().enumerate()
            {
                match type_check_bv_func_arg_with_implicit_coercion(env, nt, s, &mut params)? {
                    Either::Left(ns) => {
                        return Err(format!(
                            "TC: the {i}'th argument{nt_meta} of function '{}' expects sort {s} but was given {ns}!",
                            f.id_str().sym_quote(),
                        ));
                    }
                    Either::Right(t) => {
                        new_args.push(t);
                    }
                }
            }

            if new_args.len() < *n {
                return Err(format!(
                    "TC: function '{}'{f_meta} expects at least {n} argument(s)!",
                    f.id_str().sym_quote(),
                ));
            }

            // 3.2.1 we then make sure all parameters have been instantiated
            let params = check_bv_param_instantiation(params)?;

            // 3.2.2 we obtain the output sort
            let out_sort = bv_len_apply(env, o, &params)?;

            // 3.3 if sorts of the overall application is ascribed, then this sort must also match.
            if let Some(fs) = &f.1
                && *fs != out_sort
            {
                return sort_mismatch(fs, &out_sort, t, app_string);
            }

            // 3.4 do the same for the ascribed sort
            if let Some(outs) = outs
                && *outs != out_sort
            {
                return sort_mismatch(outs, &out_sort, t, app_string);
            }

            // passing all tests
            Ok(env.arena.app(f.clone(), new_args, Some(out_sort)))
        }
        Sig::BvConcat => {
            let mut lengths = vec![];

            // 3.0 overloaded functions don't take indices
            check_empty_index(f, app_string)?;

            // 3.1 make sure all arguments have sort BitVec
            if args.is_empty() {
                return Err(format!(
                    "TC: function '{}'{f_meta} expects at least 1 argument(s)!",
                    f.id_str().sym_quote(),
                ));
            }

            let mut new_args = vec![];
            for (
                i,
                WithMeta {
                    data: nt,
                    meta: nt_meta,
                },
            ) in args.iter().enumerate()
            {
                let ns = nt.get_sort(env);
                if let Some(l) = ns.is_bv() {
                    new_args.push(nt.clone());
                    lengths.push(l);
                } else {
                    return Err(format!(
                        "TC: the {i}'th argument{nt_meta} of function '{}' expects a BitVec but given {ns}!",
                        f.id_str().sym_quote(),
                    ));
                }
            }

            // 3.2.2 we obtain the output sort
            let total = lengths.iter().sum();
            let out_sort = env.arena_alt().bv_sort(total);

            // 3.3 if sorts of the overall application is ascribed, then this sort must also match.
            if let Some(fs) = &f.1
                && *fs != out_sort
            {
                return sort_mismatch(fs, &out_sort, t, app_string);
            }

            // 3.4 do the same for the ascribed sort
            if let Some(outs) = outs
                && *outs != out_sort
            {
                return sort_mismatch(outs, &out_sort, t, app_string);
            }

            // passing all tests
            Ok(env.arena.app(f.clone(), new_args, Some(out_sort)))
        }
    }
}

fn check_empty_index(f: &QualifiedIdentifier, meta_string: &str) -> TC<()> {
    if !f.0.indices.is_empty() {
        Err(format!(
            "TC: function '{}'{meta_string} shouldn't contain indices!",
            f.0.symbol
        ))
    } else {
        Ok(())
    }
}

fn check_arg_length<T>(
    f: &QualifiedIdentifier,
    meta_string: &str,
    args: &[T],
    arg_len: usize,
) -> TC<()> {
    if arg_len != args.len() {
        Err(format!(
            "TC: function '{}'{meta_string} expects {arg_len} arguments but {} were given!",
            f.id_str(),
            args.iter().len()
        ))
    } else {
        Ok(())
    }
}

pub(crate) fn typed_app(
    env: &mut TCEnv<Sort>,
    f: QualifiedIdentifier,
    args: Vec<WithMeta<Term, String>>,
    outs: Option<Sort>,
    id_meta: &str,
    app_meta: &str,
) -> TC<Term> {
    let symbol = &f.0.symbol;

    // 1. we fetch the list of signatures of f (a list because of overloading).
    let sigs = match env.symbol_table.get(symbol) {
        None => identifier_not_found(symbol, id_meta),
        Some(sigs) => Ok(sigs),
    }?;

    let print_struct = alg::AppFmt::new(&f, &args);

    // 2. we check each signature using this closure.
    if sigs.len() == 1 {
        type_check_with_func_sig(
            &print_struct,
            env,
            WithMeta::new(&f, id_meta),
            &args,
            &outs,
            &sigs[0].0,
            app_meta,
        )
    } else {
        // 3. if the function is overloaded, we try all signatures.
        let mut tc_res = Err(format!(
            "TC: overloaded function {f}{id_meta} does not have a case to match its list of arguments! '{print_struct}'",
        ));
        for (sig, _) in sigs {
            tc_res = type_check_with_func_sig(
                &print_struct,
                env,
                WithMeta::new(&f, id_meta),
                &args,
                &outs,
                sig,
                app_meta,
            );
            if tc_res.is_ok() {
                break;
            }
        }
        tc_res
    }
}

fn check_sig_indices(
    f: &QualifiedIdentifier,
    meta_string: &str,
    sig_indices: &[SigIndex],
) -> TC<()> {
    if sig_indices.len() != f.0.indices.len() {
        return Err(format!(
            "TC: function '{f}'{meta_string} expects {} indices but {} were given!",
            sig_indices.len(),
            f.0.indices.len()
        ));
    }
    for (spec, i) in sig_indices.iter().zip(&f.0.indices) {
        match (spec, i) {
            (SigIndex::Numeral, Index::Numeral(_)) => {}
            (SigIndex::Symbol(sym), Index::Symbol(s)) if *sym == *s => {}
            (SigIndex::Hexadecimal, Index::Hexadecimal(_, _)) => {}
            (SigIndex::Numeral, _) => {
                return Err(format!(
                    "TC: function '{f}'{meta_string} expects a numeral index, but {i} was given!",
                ));
            }
            (SigIndex::Symbol(s), _) => {
                return Err(format!(
                    "TC: function '{f}'{meta_string} expects a symbolic index {s}, but {i} was given!",
                ));
            }
            (SigIndex::Hexadecimal, _) => {
                return Err(format!(
                    "TC: function '{f}'{meta_string} expects a hexadecimal index, but {i} was given!",
                ));
            }
        }
    }
    Ok(())
}

fn check_bv_sig_indices(
    f: &QualifiedIdentifier,
    meta_string: &str,
    m: usize,
    params: &mut [Option<UBig>],
) -> TC<()> {
    if f.0.indices.len() != m {
        return Err(format!(
            "TC: function '{f}'{meta_string} expects {m} indices but {} were given!",
            f.0.indices.len()
        ));
    }
    for (i, idx) in f.0.indices.iter().enumerate() {
        match idx {
            Index::Numeral(n) => {
                params[i] = Some(n.clone());
            }
            Index::Symbol(_) | Index::Hexadecimal(_, _) => {
                return Err(format!(
                    "TC: function '{f}'{meta_string} expects a numeral index, but {idx} was given!",
                ));
            }
        }
    }
    Ok(())
}

impl<Str, T> Typecheck<TCEnv<'_, '_, T>> for alg::Index<Str>
where
    Str: AllocatableString<Arena>,
{
    type Out = Index;

    fn type_check(&self, env: &mut TCEnv<'_, '_, T>) -> TC<Self::Out> {
        match self {
            alg::Index::Numeral(n) => Ok(Index::Numeral(n.clone())),
            alg::Index::Symbol(s) => Ok(Index::Symbol(s.allocate(env.arena_alt()))),
            alg::Index::Hexadecimal(bs, n) => Ok(Index::Hexadecimal(bs.clone(), *n)),
        }
    }
}

impl<Str, T> Typecheck<TCEnv<'_, '_, T>> for alg::Identifier<Str>
where
    Str: AllocatableString<Arena>,
{
    type Out = Identifier;

    fn type_check(&self, env: &mut TCEnv<'_, '_, T>) -> TC<Self::Out> {
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

impl<Str, So, T> Typecheck<TCEnv<'_, '_, T>> for alg::QualifiedIdentifier<Str, So>
where
    Str: AllocatableString<Arena>,
    So: for<'a, 'b> Typecheck<TCEnv<'a, 'b, ()>, Out = Sort>,
{
    type Out = QualifiedIdentifier;

    fn type_check(&self, env: &mut TCEnv<'_, '_, T>) -> TC<Self::Out> {
        let i = self.0.type_check(env)?;
        let s = match &self.1 {
            None => None,
            Some(s) => Some(s.type_check(&mut env.with_empty_local())?),
        };
        Ok(alg::QualifiedIdentifier(i, s))
    }
}

impl<Str, T> Typecheck<TCEnv<'_, '_, Sort>> for alg::Attribute<Str, T>
where
    Str: Contains<T = String>,
    T: for<'a, 'b> Typecheck<TCEnv<'a, 'b, Sort>, Out = Term>,
{
    type Out = Attribute;

    fn type_check(&self, env: &mut TCEnv<'_, '_, Sort>) -> TC<Self::Out> {
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

/// Type-check a quantifier that we know is of the form `(_ bvX n)`.
fn handle_special_identifiers_of_bv<Str, So>(
    qid: &alg::QualifiedIdentifier<Str, So>,
    cap: Captures,
    env: &mut TCEnv<Sort>,
    sort: Option<Sort>,
    meta_string: &str,
) -> TC<Term>
where
    Str: Display + Contains<T = String>,
    So: Display,
{
    let x = UBig::from_str(cap.get(1).unwrap().as_str())
        .map_err(|e| format!("TC: numeric conversion error: {e}{meta_string}"))?;
    if qid.0.indices.len() != 1 {
        return Err(format!(
            "TC: {qid}{meta_string} is a bit vector, so it can only have exactly one numeral index!"
        ));
    }
    let n = match &qid.0.indices[0] {
        alg::Index::Numeral(n) => match n.to_usize() {
            None | Some(0) => {
                return Err(format!(
                    "TC: {qid}{meta_string} specifies a bit vector of an inappropriate length!"
                ));
            }
            Some(n) => n,
        },
        _ => {
            return Err(format!(
                "TC: {qid}{meta_string} is a bit vector, so it can only have one exactly numeral index!"
            ));
        }
    };
    if x.bit_len() > n {
        return Err(format!(
            "TC: {qid}{meta_string} requires {} bits, but {n} bits are specified! there are insufficient bits!",
            x.bit_len()
        ));
    }
    let mut bv = Vec::new();
    bv.extend(x.to_le_bytes());
    // pad bv to the right number of bytes
    let mut c = n.saturating_sub(8 * bv.len());
    while c != 0 {
        bv.push(0);
        c = c.saturating_sub(8);
    }
    let c = alg::Constant::Binary(bv, n);
    let s = c.type_check(env)?;
    if let Some(sort) = sort
        && s != sort
    // we know it's a bv, so there is no need to invoke substitution
    {
        return sort_mismatch(&s, &sort, c, meta_string);
    }
    Ok(env.arena.constant(c, Some(s)))
}

pub(crate) fn typed_qualified_identifier(
    env: &mut TCEnv<Sort>,
    qid: QualifiedIdentifier,
    sort: Option<Sort>,
    meta_string: &str,
) -> TC<Term> {
    if env.theories.contains(&Theory::Bitvectors) {
        // special handling for (_ bvX n)
        // c.f. https://smt-lib.org/logics-all.shtml#QF_BV
        let cap = BV_RE.captures(qid.id_str());
        if let Some(cap) = cap {
            return handle_special_identifiers_of_bv(&qid, cap, env, sort, meta_string);
        }
    }
    let symbol = qid.id_str();
    match env.local.lookup(symbol) {
        None => {
            // in this case, we hit a global variable
            let sig = match env.symbol_table.get(symbol) {
                None => {
                    return identifier_not_found(symbol, meta_string);
                }
                Some(sigs) => {
                    if sigs.len() != 1 {
                        return Err(format!(
                            "TC: identifier {qid}{meta_string} should not be overloaded!"
                        ));
                    }
                    &sigs[0].0
                }
            };
            match sig {
                Sig::VarLenFunc(_, _, _) => Err(format!(
                    "TC: {qid}{meta_string} has a signature of a variable length function, which cannot be used as a variable!"
                )),
                Sig::ParFunc(idx, pars, inps, out) => {
                    if !inps.is_empty() {
                        return Err(format!(
                            "TC: {qid}{meta_string} has signature {sig}, which cannot be used as a variable!"
                        ));
                    }
                    check_sig_indices(&qid, meta_string, idx)?;

                    let reference_ground_sort = match (&qid.1, sort) {
                        (Some(s), Some(sort)) => {
                            if *s != sort {
                                return sort_mismatch(s, &sort, &qid, meta_string);
                            } else {
                                Some(sort)
                            }
                        }
                        (Some(s), None) => Some(s.clone()),
                        (None, Some(sort)) => Some(sort),
                        (None, None) => None,
                    };

                    match reference_ground_sort {
                        None => {
                            // in this case, the variable does not have a known ground sort, so
                            // we ask this variable has a declared ground sort.
                            if pars.is_empty() {
                                Ok(env.arena.global(qid, Some(out.clone())))
                            } else {
                                Err(format!(
                                    "TC: {qid}{meta_string} has a polymorphic signature {sig}, which requires an explicit sort ascription!"
                                ))
                            }
                        }
                        Some(s) => {
                            // now we prepare a substitution
                            let mut subst: SortSubst = empty_subst(pars);
                            // we first unify the ascribed sort with the sort in the symbol table
                            if !sort_unification(&mut subst, out, &s)? {
                                return sort_mismatch(&s, out, &qid, meta_string);
                            }

                            // then we check whether all variables have been instantiated
                            check_subst_instantiation(&subst, &qid)?;

                            // now we have passed all tests
                            if subst.is_empty() {
                                Ok(env.arena.global(qid, Some(s)))
                            } else {
                                // if this variable requires non-trivial sort unification, then
                                // we should tag the ground sort.
                                Ok(env.arena.global(qid.with_sort(s.clone()), Some(s)))
                            }
                        }
                    }
                }
                Sig::BvFunc(_, _, _, _, _) | Sig::BvVarLenFunc(_, _, _, _) | Sig::BvConcat => {
                    Err(format!(
                        "TC: {qid}{meta_string} has a signature of a bit vector function, which cannot be used as a variable!"
                    ))
                }
            }
        }
        Some((l, s)) => {
            // in this case, we convert an untyped global variable into a typed local variable.
            if !qid.0.indices.is_empty() {
                Err(format!(
                    "TC: {qid}{meta_string} is a local variable and should not have indices!"
                ))
            } else if qid.1.as_ref().map(|qs| *qs != s).unwrap_or(false)
                || sort.as_ref().map(|qs| *qs != s).unwrap_or(false)
            {
                Err(format!(
                    "TC: {qid}{meta_string} is expected to have sort {s}!"
                ))
            } else {
                Ok(env.arena.local(alg::Local {
                    id: l,
                    symbol: symbol.clone(),
                    sort: Some(s.clone()),
                }))
            }
        }
    }
}

pub(crate) fn typed_constant(env: &mut TCEnv<Sort>, c: Constant) -> TC<Term> {
    let s = c.type_check(env)?;
    Ok(env.arena.constant(c, Some(s)))
}

pub(crate) fn typed_eq(env: &mut TCEnv<Sort>, at: Term, bt: Term, bt_meta: &str) -> TC<Term> {
    let sa = at.get_sort(env);
    let sb = bt.get_sort(env);
    if sa == sb {
        Ok(env.arena.eq(at, bt))
    } else {
        sort_mismatch(&sa, &sb, bt, bt_meta)
    }
}

pub(crate) fn typed_distinct(env: &mut TCEnv<Sort>, ts: Vec<WithMeta<Term, String>>) -> TC<Term> {
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

pub(crate) fn typed_not(env: &mut TCEnv<Sort>, t: Term, meta: &str) -> TC<Term> {
    is_term_bool_alt(env, &t, meta)?;
    Ok(env.arena.not(t))
}

/// this function determines whether a given term `t` is a datatype, and if it is the case,
/// the function returns the declaration of the datatype and a sort substitution for sort variables.
fn tc_determine_datatype_dec<'a>(
    env: &mut TCEnv<'a, '_, Sort>,
    t: &Term,
    meta: &str,
) -> TC<(&'a DatatypeDec, SortSubst)> {
    let so = t.get_sort(env);
    let sort_name = so.repr().0.symbol.clone();
    let dt = env
        .get_datatype_dec(&sort_name)
        .map_err(|_| format!("TC: sort {sort_name} of the given term{meta} is not a datatype!"))?;
    let mut subst: SortSubst = empty_subst(&dt.params);
    let expected = env.arena.sort_n_params(sort_name, dt.params.clone());
    if !sort_unification(&mut subst, &expected, &so)? {
        return Err(format!(
            "TC: {t}{meta} has sort {so}, which fails to unify with {expected}!"
        ));
    }
    check_subst_instantiation(&subst, t)?;
    Ok((dt, subst))
}

/// This function, given `t` a term of some datatype, determines a map from its constructors to
/// the sorts of arguments.
pub(crate) fn tc_determine_datatype_sort_map(
    env: &mut TCEnv<'_, '_, Sort>,
    t: &Term,
    meta: &str,
) -> TC<HashMap<Str, Vec<Sort>>> {
    let (dt, subst) = tc_determine_datatype_dec(env, t, meta)?;
    // now at this point, we know how to instantiate all sort variables.
    Ok(dt
        .constructors
        .iter()
        .map(|ctor| {
            (
                ctor.ctor.clone(),
                ctor.args
                    .iter()
                    .map(|arg| apply_subst(env, &subst, &arg.2))
                    .collect(),
            )
        })
        .collect())
}

impl<St, So, T> Typecheck<TCEnv<'_, '_, Sort>> for T
where
    St: AllocatableString<Arena> + Contains<T = String>,
    So: for<'a, 'b> Typecheck<TCEnv<'a, 'b, ()>, Out = Sort>,
    T: Contains<T: Repr<T = alg::Term<St, So, T>>> + Display + MetaData,
{
    type Out = Term;

    fn type_check(&self, env: &mut TCEnv<Sort>) -> TC<Self::Out> {
        match self.inner().repr() {
            alg::Term::Constant(c, _) => {
                let c = constant_conv(c, env);
                typed_constant(env, c)
                    .map_err(|e| format!("{e} for {self}{}", self.display_meta_data()))
            }
            alg::Term::Global(qid, sort) => {
                let qid = qid.type_check(env)?;
                let sort = match sort {
                    None => None,
                    Some(sort) => Some(sort.type_check(&mut env.with_empty_local())?),
                };
                typed_qualified_identifier(env, qid, sort, &self.display_meta_data())
            }
            alg::Term::Local(id) => {
                let symbol = id.symbol.allocate(env.arena_alt());
                match env.local.lookup(&symbol) {
                    None => Err(format!(
                        "TC: local variable {}{} is not bound!",
                        symbol.sym_quote(),
                        self.display_meta_data()
                    )),
                    Some((id, s)) => Ok(env.arena_alt().local(alg::Local {
                        id,
                        symbol,
                        sort: Some(s),
                    })),
                }
            }
            alg::Term::App(f, args, outs) => {
                // 1. first we make sure f is not a local variable.
                check_global_var_locally(env, f.id_str())?;
                let nf = f.type_check(env)?;

                // 2. then we typecheck the arguments
                let args = args
                    .iter()
                    .map(|a| Ok(WithMeta::new(a.type_check(env)?, a.display_meta_data())))
                    .collect::<TC<Vec<_>>>()?;
                let outs = match outs {
                    None => None,
                    Some(outs) => Some(outs.type_check(&mut env.with_empty_local())?),
                };

                typed_app(
                    env,
                    nf,
                    args,
                    outs,
                    &f.id_str().display_meta_data(),
                    &self.display_meta_data(),
                )
            }
            alg::Term::Let(vs, t) => {
                let ext = vs
                    .iter()
                    .map(|v| {
                        let t = v.2.type_check(env)?;
                        let vid = env.arena.new_local();
                        let sym = env.arena.allocate_symbol(v.0.inner());
                        Ok(VarBinding(sym, vid, t))
                    })
                    .collect::<TC<Vec<_>>>()?;
                let sorts = ext
                    .iter()
                    .map(|v| VarBinding(v.0.clone(), v.1, v.2.get_sort(env)))
                    .collect::<Vec<_>>();
                let nt = tc_with_local_env(&sorts, t, env)?;
                Ok(env.arena.let_term(ext, nt))
            }
            alg::Term::Exists(vs, t) => {
                let (vs, nt) = tc_binder(vs, t, env)?;
                Ok(env.arena.exists(vs, nt))
            }
            alg::Term::Forall(vs, t) => {
                let (vs, nt) = tc_binder(vs, t, env)?;
                Ok(env.arena.forall(vs, nt))
            }
            alg::Term::Annotated(t, ats) => {
                let nt = t.type_check(env)?;
                let nats = ats
                    .iter()
                    .map(|a| a.type_check(env))
                    .collect::<TC<Vec<_>>>()?;
                Ok(env.arena.annotated(nt, nats))
            }
            alg::Term::Eq(a, b) => {
                let at = a.type_check(env)?;
                let bt = b.type_check(env)?;
                typed_eq(env, at, bt, &b.display_meta_data())
            }
            alg::Term::Distinct(ts) => {
                let nts = ts
                    .iter()
                    .map(|t| Ok(WithMeta::new(t.type_check(env)?, t.display_meta_data())))
                    .collect::<TC<Vec<_>>>()?;
                typed_distinct(env, nts)
            }
            alg::Term::And(ts) => {
                if ts.is_empty() {
                    return Err(format!(
                        "TC: 'and'{} requires at least one argument!",
                        self.display_meta_data()
                    ));
                }
                let nts = tc_vec_sort_bool(ts, env)?;
                Ok(env.arena.and(nts))
            }
            alg::Term::Or(ts) => {
                if ts.is_empty() {
                    return Err(format!(
                        "TC: 'or'{} requires at least one argument!",
                        self.display_meta_data()
                    ));
                }
                let nts = tc_vec_sort_bool(ts, env)?;
                Ok(env.arena.or(nts))
            }
            alg::Term::Xor(ts) => {
                if ts.is_empty() {
                    return Err(format!(
                        "TC: 'xor'{} requires at least one argument!",
                        self.display_meta_data()
                    ));
                }
                let nts = tc_vec_sort_bool(ts, env)?;
                Ok(env.arena.xor(nts))
            }
            alg::Term::Not(t) => {
                let nt = t.type_check(env)?;
                typed_not(env, nt, &t.display_meta_data())
            }
            alg::Term::Implies(ts, t) => {
                if ts.is_empty() {
                    return Err(format!(
                        "TC: implies '=>'{} should take at least one left hand side!",
                        self.display_meta_data()
                    ));
                }
                let nts = tc_vec_sort_bool(ts, env)?;
                let nt = t.type_check(env)?;
                is_term_bool_alt(env, &nt, &t.display_meta_data())?;
                Ok(env.arena.implies(nts, nt))
            }
            alg::Term::Ite(c, t, e) => {
                let nc = c.type_check(env)?;
                is_term_bool_alt(env, &nc, &c.display_meta_data())?;
                let nt = t.type_check(env)?;
                let ne = e.type_check(env)?;
                let ts = nt.get_sort(env);
                let es = ne.get_sort(env);
                if ts != es {
                    sort_mismatch(&ts, &es, e, &e.display_meta_data())
                } else {
                    Ok(env.arena.ite(nc, nt, ne))
                }
            }
            alg::Term::Matching(t, arms) => {
                if !env.theories.contains(&Theory::Datatypes) {
                    return Err(
                        "TC: current logic does not support the theory of datatypes!".into(),
                    );
                }

                // 1. we type-check the scrutinee
                let nt = t.type_check(env)?;

                // 2. then we determine the sorts of constructors
                let so = nt.get_sort(env);
                let constructors =
                    tc_determine_datatype_sort_map(env, &nt, &t.display_meta_data())?;

                // now at this point, we know how to instantiate all sort variables.

                // 3. preparation work
                let mut unseen_ctors: HashSet<Str> = constructors.keys().cloned().collect();
                let mut covered = false;

                // 4. check the arms
                let mut narms = vec![];
                // need to make sure all branches have the same sort
                let mut body_sort = None;
                for arm in arms {
                    match &arm.pattern {
                        alg::Pattern::Ctor(ctor) => {
                            let ctr = ctor.allocate(env.arena);
                            match constructors.get(&ctr) {
                                None => {
                                    return Err(format!(
                                        "case {ctr}{} is not a constructor!",
                                        ctor.display_meta_data()
                                    ));
                                }
                                Some(args) => {
                                    if !args.is_empty() {
                                        return Err(format!(
                                            "case {ctr}{} is not a constructor with a non-empty argument list!",
                                            ctor.display_meta_data()
                                        ));
                                    }
                                }
                            }
                            // remove the current constructor from the unseen ones.
                            unseen_ctors.remove(&ctr);
                            let body = tc_match_case_body(env, &[], &arm.body, &mut body_sort)?;
                            narms.push(alg::PatternArm {
                                pattern: Pattern::Ctor(ctr),
                                body,
                            });
                        }
                        alg::Pattern::Wildcard(ctor) => {
                            // in this case, [ctor] is either a wildcard variable, or a nullary constructor.
                            // depending on the case, we just need to TC with an extra variable [ctor],
                            // if it is a wildcard.
                            let (sorts, pattern) = match ctor {
                                None => (vec![], Pattern::Wildcard(None)),
                                Some((ctor, id)) => {
                                    let ctr = ctor.allocate(env.arena_alt());
                                    match constructors.get(&ctr) {
                                        None => (
                                            vec![alg::VarBinding(ctr.clone(), *id, so.clone())],
                                            Pattern::Wildcard(Some((ctr.clone(), *id))),
                                        ),
                                        Some(args) => {
                                            if args.is_empty() {
                                                // remove the current constructor from the unseen ones.
                                                unseen_ctors.remove(&ctr);

                                                (vec![], Pattern::Ctor(ctr.clone()))
                                            } else {
                                                return Err(format!(
                                                    "case {ctr}{} is not a constructor with a non-empty argument list!",
                                                    ctr.display_meta_data()
                                                ));
                                            }
                                        }
                                    }
                                }
                            };
                            let body = tc_match_case_body(env, &sorts, &arm.body, &mut body_sort)?;
                            narms.push(alg::PatternArm { pattern, body });
                            covered = true;
                        }
                        alg::Pattern::Applied { ctor, arguments } => {
                            // in this case, [ctor] must be a constructor, so we must extract its signature
                            // from [constructors].
                            let ctr = ctor.allocate(env.arena_alt());
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
                                    // remove the current constructor from the unseen ones.
                                    unseen_ctors.remove(&ctr);
                                    let arguments = arguments
                                        .iter()
                                        .map(|o| {
                                            o.as_ref().map(|(name, _)| {
                                                let symbol =
                                                    env.arena.allocate_symbol(name.inner());
                                                let fresh_id = env.arena.new_local();
                                                (symbol, fresh_id)
                                            })
                                        })
                                        .collect::<Vec<_>>();
                                    let sorts = arguments
                                        .iter()
                                        .zip(sig)
                                        .filter_map(|(o, s)| {
                                            o.as_ref().map(|(name, id)| {
                                                alg::VarBinding(name.clone(), *id, s.clone())
                                            })
                                        })
                                        .collect::<Vec<_>>();
                                    let body =
                                        tc_match_case_body(env, &sorts, &arm.body, &mut body_sort)?;
                                    narms.push(alg::PatternArm {
                                        pattern: Pattern::Applied {
                                            ctor: ctr,
                                            arguments,
                                        },
                                        body,
                                    });
                                }
                            }
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
                        self.display_meta_data()
                    ))
                } else {
                    Ok(env.arena.matching(nt, narms))
                }
            }
        }
    }
}

fn tc_match_case_body<T>(
    env: &mut TCEnv<'_, '_, Sort>,
    bindings: &[VarBinding<Str, Sort>],
    body: &T,
    body_sort: &mut Option<Sort>,
) -> TC<Term>
where
    T: for<'a, 'b> Typecheck<TCEnv<'a, 'b, Sort>, Out = Term>,
    T: MetaData,
{
    let nbody = tc_with_local_env(bindings, body, env)?;
    let sort = nbody.get_sort(env);
    if let Some(s) = body_sort.as_ref() {
        if *s != sort {
            return sort_mismatch(s, &sort, nbody, &body.display_meta_data());
        }
    } else {
        *body_sort = Some(sort);
    }
    Ok(nbody)
}
