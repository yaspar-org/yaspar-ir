// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use super::unif::{SortSubst, apply_subst, sort_unification};
use super::{TC, TCEnvGen, Typecheck, unif};
use crate::allocator::{ObjectAllocatorExt, TermAllocator};
use crate::ast::SymbolQuote;
use crate::containers::Mapping;
use crate::meta::WithMeta;
use crate::raw::alg;
use crate::raw::instance::{
    BvInSort, BvOutSort, FetchSort, HasArenaAlt, Index, QualifiedIdentifier, Sig, SigIndex, Sort,
    Str, Term, Theory,
};
use crate::statics::{BV_RE, TO_REAL};
use crate::traits::Contains;
use dashu::base::BitTest;
use dashu::integer::UBig;
use either::Either;
use num_traits::ToPrimitive;
use regex::Captures;
use std::collections::HashMap;
use std::fmt::Display;
use std::str::FromStr;

/// Validate that the indices on a qualified identifier match the expected signature indices.
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

/// Type-check a quantifier that we know is of the form `(_ bvX n)`.
fn handle_special_identifiers_of_bv<Str, So, L>(
    qid: &alg::QualifiedIdentifier<Str, So>,
    cap: Captures,
    env: &mut TCEnvGen<L>,
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
        return super::sort_mismatch(&s, &sort, c, meta_string);
    }
    Ok(env.arena.constant(c, Some(s)))
}

/// Type-check a qualified identifier (possibly with sort ascription) and return a typed term.
///
/// Handles local variables, global constants, polymorphic symbols, and bitvector literals.
pub(crate) fn typed_qualified_identifier<L>(
    env: &mut TCEnvGen<L>,
    qid: QualifiedIdentifier,
    sort: Option<Sort>,
    meta_string: &str,
) -> TC<Term>
where
    L: Mapping<Key = Str, Value = (usize, Sort)>,
{
    if env.meta.theories.contains(&Theory::Bitvectors) {
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
            let sig = match env.frame.symbol_table.get(symbol) {
                None => {
                    return super::identifier_not_found(symbol, meta_string);
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
                                return super::sort_mismatch(s, &sort, &qid, meta_string);
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
                            let mut subst: SortSubst = unif::empty_subst(pars);
                            // we first unify the ascribed sort with the sort in the symbol table
                            if !unif::sort_unification(&mut subst, out, &s)? {
                                return super::sort_mismatch(&s, out, &qid, meta_string);
                            }

                            // then we check whether all variables have been instantiated
                            super::check_subst_instantiation(&subst, &qid)?;

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
                    sort: s.clone(),
                }))
            }
        }
    }
}

/// Check whether `t` is an argument given an `expected` sort and a `subst`itution.
///
/// Return `Right(nt)` where `nt` is the potentially new term for the argument, or `Left(s)` if
/// `t` should be rejected, where `s` is the actual sort.
fn type_check_func_arg_with_implicit_coercion<L>(
    env: &mut TCEnvGen<L>,
    t: &Term,
    expected: &Sort,
    subst: &mut SortSubst,
) -> TC<Either<Sort, Term>>
where
    L: Mapping<Key = Str>,
{
    let ns = t.get_sort(env);
    let unifiable = sort_unification(subst, expected, &ns)?;
    if unifiable {
        return Ok(Either::Right(t.clone()));
    }
    // if the sorts are not unifiable, then there are two possibilities.
    // 1. if Reals_Ints is not a current theory, then we don't do anything, i.e. reject t as an argument.
    if !env.meta.theories.contains(&Theory::RealInts) {
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
        let to_real = super::check_global_var_locally(env, TO_REAL)?; // this should pass for the sake of symbol table declaration.
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

/// Check that all bitvector length parameters have been instantiated.
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

/// Compute the output sort of a bitvector function given instantiated length parameters.
fn bv_len_apply<T: HasArenaAlt>(env: &mut T, out: &BvOutSort, params: &[UBig]) -> TC<Sort> {
    match out {
        BvOutSort::BitVec(expr) => {
            let len = expr.eval(params)?;
            super::valid_bv_sort(env, len)
        }
        BvOutSort::Sort(s) => Ok(s.clone()),
    }
}

/// Type-check a bitvector function argument, unifying its length with the expected parameter.
fn type_check_bv_func_arg_with_implicit_coercion<L>(
    env: &mut TCEnvGen<L>,
    t: &Term,
    expected: &BvInSort,
    params: &mut [Option<UBig>],
) -> TC<Either<Sort, Term>>
where
    L: Mapping<Key = Str>,
{
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

/// Type-check a function application against a single signature.
///
/// Dispatches on the signature variant (`VarLenFunc`, `ParFunc`, `BvFunc`, etc.),
/// validates argument sorts, performs sort unification, and returns the typed application term.
fn type_check_with_func_sig<L>(
    t: impl Display,
    env: &mut TCEnvGen<L>,
    f: WithMeta<&QualifiedIdentifier, &str>,
    args: &[WithMeta<Term, String>],
    outs: &Option<Sort>,
    sig: &Sig,
    app_string: &str,
) -> TC<Term>
where
    L: Mapping<Key = Str>,
{
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
                return super::sort_mismatch(fs, o, t, app_string);
            }

            // 3.3 do the same for the ascribed sort
            if let Some(outs) = outs
                && *outs != *o
            {
                return super::sort_mismatch(outs, o, t, app_string);
            }

            // passing all tests
            Ok(env.arena.app(f.clone(), new_args, Some(o.clone())))
        }
        Sig::ParFunc(sig_indices, vs, ss, s) => {
            let mut subst: SortSubst = unif::empty_subst(vs);

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
                            unif::format_subst(&subst)
                        ));
                    }
                    Either::Right(nt) => new_args.push(nt),
                }
            }

            // 3.3 if sorts of the overall application is ascribed, then this sort must also match.
            if let Some(fs) = &f.1
                && !unif::sort_unification(&mut subst, s, fs)?
            {
                return super::sort_mismatch(fs, s, t, app_string);
            }

            // 3.4 do the same for the ascribed sort
            if let Some(outs) = outs
                && !unif::sort_unification(&mut subst, s, outs)?
            {
                return super::sort_mismatch(outs, s, t, app_string);
            }

            // 3.5 make sure all vars in the substitution have been materialized
            super::check_subst_instantiation(&subst, t)?;

            // passing all tests
            let ret_sort = unif::apply_subst(env, &subst, s);
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
                return super::sort_mismatch(fs, &out_sort, t, app_string);
            }

            // 3.4 do the same for the ascribed sort
            if let Some(outs) = outs
                && *outs != out_sort
            {
                return super::sort_mismatch(outs, &out_sort, t, app_string);
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
                return super::sort_mismatch(fs, &out_sort, t, app_string);
            }

            // 3.4 do the same for the ascribed sort
            if let Some(outs) = outs
                && *outs != out_sort
            {
                return super::sort_mismatch(outs, &out_sort, t, app_string);
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
                return super::sort_mismatch(fs, &out_sort, t, app_string);
            }

            // 3.4 do the same for the ascribed sort
            if let Some(outs) = outs
                && *outs != out_sort
            {
                return super::sort_mismatch(outs, &out_sort, t, app_string);
            }

            // passing all tests
            Ok(env.arena.app(f.clone(), new_args, Some(out_sort)))
        }
    }
}

/// Ensure a function identifier has no indices.
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

/// Validate that the number of arguments matches the expected arity.
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

/// Validate and extract numeral indices for a bitvector function signature.
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

/// Type-check a function application `(f args...)`.
///
/// Looks up the function's signature(s) in the symbol table and tries each one
/// (for overloaded functions) until one succeeds. Delegates to [`type_check_with_func_sig`]
/// for the actual per-signature checking.
pub(crate) fn typed_app<L>(
    env: &mut TCEnvGen<L>,
    f: QualifiedIdentifier,
    args: Vec<WithMeta<Term, String>>,
    outs: Option<Sort>,
    id_meta: &str,
    app_meta: &str,
) -> TC<Term>
where
    L: Mapping<Key = Str>,
{
    let symbol = &f.0.symbol;

    // 1. Make sure that the application is not nullary
    if args.len() == 0 {
        return Err(format!("TC: Applications cannot be nullary, use a Global instead"))
    }
    // 2. we fetch the list of signatures of f (a list because of overloading).
    let sigs = match env.frame.symbol_table.get(symbol) {
        None => super::identifier_not_found(symbol, id_meta),
        Some(sigs) => Ok(sigs),
    }?;

    let print_struct = alg::AppFmt::new(&f, &args);

    // 3. we check each signature using this closure.
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
        // 4. if the function is overloaded, we try all signatures.
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
