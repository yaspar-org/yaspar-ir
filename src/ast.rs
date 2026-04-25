// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Typed AST types, the global context, and term transformation algorithms.
//!
//! This is the main module of the crate. It re-exports the core types and traits needed to work
//! with well-formed SMTLib objects:
//!
//! # Core types
//!
//! - [`Context`] — the global environment that tracks the current logic, declared sorts, and the
//!   symbol table. Most operations require a mutable reference to a context.
//! - [`Term`], [`Sort`], [`Command`] — hashconsed typed AST nodes. Use `.repr()` (from the
//!   [`Repr`] trait) to pattern-match on their internal structure ([`ATerm`], etc.).
//! - [`Arena`] — the memory arena that manages hashconsed allocations. Accessed via `Context`.
//!
//! # Traits
//!
//! - [`CheckedApi`] — well-formedness-checked term building (see the `ctx::checked` module).
//! - [`ScopedSortApi`] — well-formedness-checked sort building (auto-derived from `CheckedApi`).
//! - [`Typecheck`] — convert untyped ASTs (or re-check typed ASTs) via `.type_check(&mut ctx)`.
//! - [`LetElim`] — eliminate let-bindings by inlining bound terms.
//! - [`Repr`] — access the internal enum representation of a hashconsed object.
//!
//! # Sub-modules
//!
//! - [`fv`] — free variable computation.
//! - [`subst`] — local substitution.
//! - [`gsubst`] — global definition expansion.
//! - [`letintro`] — let-introduction via topological sorting (inverse of let-elimination).
//! - [`mono`] — monomorphization of parametric datatypes.

mod boilerplates;
#[cfg(feature = "cnf")]
pub(crate) mod cnf;
mod ctx;
pub mod fv;
pub mod gsubst;
#[cfg(feature = "implicant-generation")]
pub(crate) mod implicant;
pub(crate) mod letelim;
pub mod letintro;
pub mod mono;
pub mod subst;

pub use crate::allocator::*;

pub use crate::ast::ctx::*;
#[cfg(feature = "implicant-generation")]
use crate::ast::implicant::ImplicantEnv;
#[cfg(feature = "implicant-generation")]
pub use crate::ast::implicant::ImplicantIterator;
#[cfg(feature = "implicant-generation")]
pub use crate::ast::implicant::{FindImplicant, Model};
pub use crate::raw::alg;
pub use crate::raw::alg::rec::{Bottom, IsBottom, TermRecursor};
pub use crate::raw::alg::rec_memo::Memoize;
pub use crate::raw::tc::{TC, TCEnv, Typecheck, unif::SortSubst};
pub use crate::untyped as u;
pub use boilerplates::TypedBuilder;
pub use gsubst::{GlobalSubst, GlobalSubstituter, GlobalSubstituterInner};
pub use mono::{Monomorphization, find_sort_subst_from_datatype_dec};
#[allow(deprecated)]
pub use subst::{
    Substitute, SubstituteV2, Substituter, SubstituterInner, Substitution, SubstitutionV2,
};

pub use crate::ast::letelim::{LetElim, LetEliminator, LetEliminatorInner};
use crate::traits::MetaData;
#[cfg(feature = "implicant-generation")]
use sat_interface::SatSolver;

/// Return a list of logic supported by the crate
pub fn list_of_logics() -> &'static [&'static str] {
    &crate::ast::ctx::ALL_LOGICS
}

/// Convenience alias: a [`TermRecursor`] specialized to the typed AST
pub trait TypedTermRecursor: TermRecursor<Str, Sort, Term> {}

impl<C> Typecheck<C> for u::Sort
where
    C: ScopedSortApi,
{
    type Out = Sort;

    fn type_check(&self, env: &mut C) -> TC<Self::Out> {
        let mut env = env.get_sort_tcenv();
        self.type_check(&mut env)
    }
}

impl<C> Typecheck<C> for Sort
where
    C: ScopedSortApi,
{
    type Out = Sort;

    fn type_check(&self, env: &mut C) -> TC<Self::Out> {
        let mut env = env.get_sort_tcenv();
        self.type_check(&mut env)
    }
}

/// these type constraints say that
///
/// If an environment implements [CheckedApi], then it can provide a type-checking environment [TCEnv],
/// so we can use that for type-checking.
impl<C, T, O> Typecheck<C> for T
where
    C: StrAllocator<Str = Str> + CheckedApi,
    T: for<'a, 'b> Typecheck<TCEnv<'a, 'b, Sort>, Out = O>,
    O: 'static,
{
    type Out = O;

    fn type_check(&self, env: &mut C) -> TC<Self::Out> {
        let mut env = env.get_tcenv();
        self.type_check(&mut env)
    }
}

impl<T, O> Typecheck<Context> for Vec<T>
where
    O: 'static,
    T: Typecheck<Context, Out = O>,
{
    type Out = Vec<O>;

    fn type_check(&self, env: &mut Context) -> TC<Self::Out> {
        self.iter().map(|t| t.type_check(env)).collect()
    }
}

fn type_check_command(command: &u::Command, env: &mut Context) -> TC<Command> {
    match command.repr() {
        ACommand::Assert(t) => {
            env.ensure_logic();
            let nt = t.type_check(env)?;
            env.typed_assert(nt)
        }
        ACommand::DeclareConst(name, sort) => {
            env.ensure_logic();
            let nsort = sort.type_check(env)?;
            let name = env.arena.allocate_symbol(name.inner());
            env.add_symbol(name.clone(), Sig::sort(nsort.clone()))?;
            Ok(env.arena.declare_const(name, nsort))
        }
        ACommand::DeclareFun(symbol, inp, o) => {
            env.ensure_logic();
            let mut ns = vec![];
            for s in inp {
                ns.push(s.type_check(env)?);
            }
            let no = o.type_check(env)?;
            let sym = env.arena.allocate_symbol(symbol.inner());

            env.add_symbol(sym.clone(), Sig::func(ns.clone(), no.clone()))?;
            Ok(env.arena.declare_fun(sym, ns, no))
        }
        ACommand::DeclareSort(symbol, arity) => {
            env.ensure_logic();
            let sym = env.arena.allocate_symbol(symbol.inner());
            env.add_sort(sym.clone(), *arity)?;
            Ok(env.arena.declare_sort(sym, *arity))
        }
        ACommand::DefineSort(symbol, params, sort) => {
            env.ensure_logic();
            let mut ds_env = env.build_sort_alias(symbol, params)?;
            let sort = sort.type_check(&mut ds_env)?;
            ds_env.typed_define_sort(sort)
        }
        ACommand::DefineFun(fd) => {
            env.ensure_logic();
            let vars = fd
                .vars
                .iter()
                .map(|v| {
                    let sort = v.2.type_check(env)?;
                    Ok((&v.0, sort))
                })
                .collect::<TC<Vec<_>>>()?;
            let out_sort = fd.out_sort.type_check(env)?;
            let mut df_env = env.build_fun_out_sort(&fd.name, vars, out_sort)?;
            let body = fd.body.type_check(&mut df_env)?;
            df_env.typed_define_fun(body)
        }
        ACommand::DefineConst(name, sort, term) => {
            env.ensure_logic();
            let sort = sort.type_check(env)?;
            let term = term.type_check(env)?;
            env.typed_define_const_sorted(name, sort, term)
        }
        ACommand::SetInfo(attr) => {
            let attr = attr.type_check(env)?;
            Ok(env.arena.set_info(attr))
        }
        ACommand::SetOption(opt) => env.typed_set_option(opt),
        ACommand::SetLogic(l) => {
            env.set_ctx_logic(l)?;
            let logic = env.arena.allocate_symbol(l.inner());
            Ok(env.arena.set_logic(logic))
        }
        ACommand::CheckSat => {
            env.ensure_logic();
            Ok(env.arena.check_sat())
        }
        ACommand::CheckSatAssuming(terms) => {
            env.ensure_logic();
            let terms = terms.type_check(env)?;
            env.typed_check_sat_assuming(terms)
        }
        ACommand::DeclareDatatype(name, dec) => {
            env.ensure_logic();
            let mut d_ctx = env.build_datatypes([(name, &dec.params)])?;
            let mut c_ctx = d_ctx.build_datatype(name)?;
            c_ctx.build_datatype_constructor_declarations(&dec.constructors)?;
            c_ctx.typed_datatype()?;
            d_ctx.typed_declare_datatypes()
        }
        ACommand::DeclareDatatypes(defs) => {
            env.ensure_logic();
            let meta_args = defs
                .iter()
                .map(|def| (&def.name, &def.dec.params))
                .collect::<Vec<_>>();
            let mut d_ctx = env.build_datatypes(meta_args)?;
            for def in defs {
                let mut c_ctx = d_ctx.build_datatype(&def.name)?;
                c_ctx.build_datatype_constructor_declarations(&def.dec.constructors)?;
                c_ctx.typed_datatype()?;
            }
            d_ctx.typed_declare_datatypes()
        }
        ACommand::DefineFunRec(fd) => {
            env.ensure_logic();
            let args = fd
                .vars
                .iter()
                .map(|v| Ok((&v.0, v.2.type_check(env)?)))
                .collect::<TC<Vec<_>>>()?;
            let out = fd.out_sort.type_check(env)?;
            let mut ctx = env.build_rec_funs([RecFunc::new(&fd.name, args, out)])?;
            let mut f_ctx = ctx.build_function(&fd.name)?;
            let body = fd.body.type_check(&mut f_ctx)?;
            f_ctx.typed_function(body)?;
            ctx.typed_define_funs_rec()
        }
        ACommand::DefineFunsRec(fds) => {
            env.ensure_logic();
            let args = fds
                .iter()
                .map(|fd| {
                    let args = fd
                        .vars
                        .iter()
                        .map(|v| Ok((&v.0, v.2.type_check(env)?)))
                        .collect::<TC<Vec<_>>>()?;
                    let out = fd.out_sort.type_check(env)?;
                    Ok(RecFunc::new(&fd.name, args, out))
                })
                .collect::<TC<Vec<_>>>()?;
            let mut ctx = env.build_rec_funs(args)?;
            for fd in fds {
                let mut f_ctx = ctx.build_function(&fd.name)?;
                let body = fd.body.type_check(&mut f_ctx)?;
                f_ctx.typed_function(body)?;
            }
            ctx.typed_define_funs_rec()
        }
        ACommand::Echo(s) => {
            let s = env.arena.allocate_str(s.inner());
            Ok(env.arena.echo(s))
        }
        ACommand::Exit => Ok(env.arena.exit()),
        ACommand::GetAssertions => Ok(env.arena.get_assertions()),
        ACommand::GetAssignment => Ok(env.arena.get_assignment()),
        ACommand::GetInfo(kw) => Ok(env.arena.get_info(kw.clone())),
        ACommand::GetModel => Ok(env.arena.get_model()),
        ACommand::GetOption(opt) => Ok(env.arena.get_option(opt.clone())),
        ACommand::GetProof => Ok(env.arena.get_proof()),
        ACommand::GetUnsatAssumptions => Ok(env.arena.get_unsat_assumptions()),
        ACommand::GetUnsatCore => Ok(env.arena.get_unsat_core()),
        ACommand::GetValue(ts) => {
            if ts.is_empty() {
                return Err("get-value should contain at least one term!".into());
            }
            let nts = ts.type_check(env)?;
            nts.iter().try_for_each(is_quantifier_free)?;
            Ok(env.arena.get_value(nts))
        }
        ACommand::Pop(n) => Ok(env.arena.pop(n.clone())),
        ACommand::Push(n) => Ok(env.arena.push(n.clone())),
        ACommand::Reset => Ok(env.arena.reset()),
        ACommand::ResetAssertions => Ok(env.arena.reset_assertions()),
    }
}

/// Check whether the current term is quantifier-free
fn is_quantifier_free(term: &Term) -> TC<()> {
    match term.repr() {
        ATerm::Constant(_, _) | ATerm::Global(_, _) | ATerm::Local(_) => Ok(()),
        ATerm::App(_, ts, _) => ts.iter().try_for_each(is_quantifier_free),
        ATerm::Let(bindings, body) => {
            bindings.iter().try_for_each(|b| is_quantifier_free(&b.2))?;
            is_quantifier_free(body)
        }
        ATerm::Exists(_, _) | ATerm::Forall(_, _) => Err(format!("{} includes a quantifier", term)),
        ATerm::Matching(t, arms) => {
            is_quantifier_free(t)?;
            arms.iter().try_for_each(|a| is_quantifier_free(&a.body))
        }
        ATerm::Annotated(t, _) | ATerm::Not(t) => is_quantifier_free(t),
        ATerm::Eq(a, b) => {
            is_quantifier_free(a)?;
            is_quantifier_free(b)
        }
        ATerm::Distinct(ts) | ATerm::And(ts) | ATerm::Or(ts) | ATerm::Xor(ts) => {
            ts.iter().try_for_each(is_quantifier_free)
        }
        ATerm::Implies(ts, t) => {
            ts.iter().try_for_each(is_quantifier_free)?;
            is_quantifier_free(t)
        }
        ATerm::Ite(c, t, e) => {
            is_quantifier_free(c)?;
            is_quantifier_free(t)?;
            is_quantifier_free(e)
        }
    }
}

impl Typecheck<Context> for u::Command {
    type Out = Command;

    fn type_check(&self, env: &mut Context) -> TC<Self::Out> {
        let r = type_check_command(self, env);
        r.map_err(|mut e| {
            e.push_str(&self.display_meta_data());
            e
        })
    }
}

impl LetElim<Context> for Term {
    fn let_elim(&self, env: &mut Context) -> Self {
        LetEliminator::create(env).recurse_on_term_no_err(self)
    }
}

#[cfg(feature = "implicant-generation")]
impl<Solver> FindImplicant<&mut Context, Solver> for Vec<Term>
where
    Solver: SatSolver,
{
    fn find_one_implicant(&self, env: &mut Context, solver: &mut Solver) -> Option<Result<Self>> {
        self.find_one_implicant(
            ImplicantEnv {
                arena: &mut env.arena,
                cnf_cache: &mut env.caches.cnf_cache,
            },
            solver,
        )
    }
}
