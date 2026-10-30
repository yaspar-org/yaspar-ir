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
//! - [`AlphaEquiv`] — compare terms up to renaming of bound variables.
//! - [`Repr`] — access the internal enum representation of a hashconsed object.
//!
//! # Sub-modules
//!
//! - [`fv`] — free variable computation.
//! - [`subst`] — local substitution.
//! - [`gsubst`] — global definition expansion.
//! - [`letintro`] — let-introduction via topological sorting (inverse of let-elimination).
//! - [`mono`] — monomorphization of parametric datatypes.

pub(crate) mod alpha_eq;
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
pub(crate) mod rename;
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
pub use crate::raw::alg::LocalId;
pub use crate::raw::alg::display::{PrintConfig, StructuredPrint};
pub use crate::raw::alg::rec::{Bottom, IsBottom, TermRecursor};
pub use crate::raw::alg::rec_memo::Memoize;
pub use crate::raw::tc::{TC, TCEnv, Typecheck, unif::SortSubst};
pub use crate::untyped as u;
pub use boilerplates::TypedBuilder;
#[allow(deprecated)]
pub use gsubst::GlobalSubstituterInner;
pub use gsubst::{GlobalSubst, GlobalSubstituter};
pub use mono::{Monomorphization, find_sort_subst_from_datatype_dec};
pub use rename::AlphaRename;
pub use subst::{Substitute, Substitution};

pub use crate::ast::alpha_eq::AlphaEquiv;
pub use crate::ast::letelim::LetElim;
#[allow(deprecated)]
pub use crate::ast::letelim::{LetEliminator, LetEliminatorInner};
use crate::traits::MetaData;
#[cfg(feature = "implicant-generation")]
use sat_interface::SatSolver;

/// Return a list of logic supported by the crate
pub fn list_of_logics() -> &'static [&'static str] {
    &crate::ast::ctx::ALL_LOGICS
}

/// Convenience alias: a [`TermRecursor`] specialized to the typed AST
pub trait TypedTermRecursor: TermRecursor<Str, Sort, Term> {}

/// Sorts and terms type-check in every builder context, in the dialect of its [`Context`].
///
/// One impl per context type, rather than one blanket over [`CheckedApi`] and [`ScopedSortApi`]:
/// a blanket would have to name the dialect only in its bounds, which Rust does not allow.
macro_rules! typecheck_sorts_in {
    ($($ctx:ty),* $(,)?) => {$(
        impl<const D: Dialect> Typecheck<$ctx> for u::Sort {
            type Out = Sort;

            fn type_check(&self, env: &mut $ctx) -> TC<Self::Out> {
                let mut env = ScopedSortApi::<D>::get_sort_tcenv(env);
                self.type_check(&mut env)
            }
        }

        impl<const D: Dialect> Typecheck<$ctx> for Sort {
            type Out = Sort;

            fn type_check(&self, env: &mut $ctx) -> TC<Self::Out> {
                let mut env = ScopedSortApi::<D>::get_sort_tcenv(env);
                self.type_check(&mut env)
            }
        }
    )*};
}

/// If a context implements [CheckedApi], then it provides a type-checking environment [TCEnv],
/// so terms can be type-checked in it.
macro_rules! typecheck_terms_in {
    ($($ctx:ty),* $(,)?) => {$(
        impl<T, O, const D: Dialect> Typecheck<$ctx> for T
        where
            T: for<'a, 'b> Typecheck<TCEnv<'a, 'b, Sort, D>, Out = O>,
            O: 'static,
        {
            type Out = O;

            fn type_check(&self, env: &mut $ctx) -> TC<Self::Out> {
                let mut env = CheckedApi::<D>::get_tcenv(env);
                self.type_check(&mut env)
            }
        }
    )*};
}

typecheck_sorts_in!(
    Context<D>,
    QuantifierContext<'_, '_, D>,
    LetContext<'_, '_, D>,
    ArmContext<'_, '_, '_, D>,
    FunctionContext<'_, D>,
    EachRecFunContext<'_, D>,
    DefSortContext<'_, D>,
    DtDeclContext<'_, '_, D>,
);

typecheck_terms_in!(
    Context<D>,
    QuantifierContext<'_, '_, D>,
    LetContext<'_, '_, D>,
    ArmContext<'_, '_, '_, D>,
    FunctionContext<'_, D>,
    EachRecFunContext<'_, D>,
);

impl<T, O, const D: Dialect> Typecheck<Context<D>> for Vec<T>
where
    O: 'static,
    T: Typecheck<Context<D>, Out = O>,
{
    type Out = Vec<O>;

    fn type_check(&self, env: &mut Context<D>) -> TC<Self::Out> {
        self.iter().map(|t| t.type_check(env)).collect()
    }
}

fn type_check_command<const D: Dialect>(command: &u::Command, env: &mut Context<D>) -> TC<Command> {
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
            let nts = ts.type_check(env)?;
            env.typed_get_value(nts)
        }
        ACommand::Pop(n) => env.typed_pop(n.clone()),
        ACommand::Push(n) => env.typed_push(n.clone()),
        ACommand::Reset => Ok(env.reset_context()),
        ACommand::ResetAssertions => Ok(env.reset_assertion_stack()),
    }
}

impl<const D: Dialect> Typecheck<Context<D>> for u::Command {
    type Out = Command;

    fn type_check(&self, env: &mut Context<D>) -> TC<Self::Out> {
        let r = type_check_command(self, env);
        r.map_err(|mut e| {
            e.push_str(&self.display_meta_data());
            e
        })
    }
}

#[cfg(feature = "implicant-generation")]
impl<Solver, const D: Dialect> FindImplicant<&mut Context<D>, Solver> for Vec<Term>
where
    Solver: SatSolver,
{
    fn find_one_implicant(
        &self,
        env: &mut Context<D>,
        solver: &mut Solver,
    ) -> Option<Result<Self>> {
        self.find_one_implicant(
            ImplicantEnv {
                arena: &mut env.arena,
                cnf_cache: &mut env.caches.cnf_cache,
            },
            solver,
        )
    }
}
