#[cfg(feature = "cnf")]
pub(crate) mod cnf;
mod ctx;
pub mod fv;
pub mod gsubst;
#[cfg(feature = "implicant-generation")]
pub(crate) mod implicant;
pub mod letintro;
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
pub use crate::raw::letelim::*;
pub use crate::raw::tc::{TCEnv, Typecheck, TC};
pub use crate::untyped as u;
pub use gsubst::{GlobalSubstInplace, GlobalSubstPreproc};
pub use subst::{Substitute, Substitution};

use crate::traits::MetaData;
#[cfg(feature = "implicant-generation")]
use sat_interface::SatSolver;

/// Return a list of logic supported by the crate
pub fn list_of_logics() -> &'static [&'static str] {
    &crate::ast::ctx::ALL_LOGICS
}

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

/// zthese type constraints say that
///
/// If an environment implements [TypedApi], then it can provide a type-checking environment [TCEnv],
/// so we can use that for type-checking.
impl<C, T, O> Typecheck<C> for T
where
    C: StrAllocator<Str = Str> + TypedApi,
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
            let nts = ts.type_check(env)?;
            Ok(env.arena.get_value(nts))
        }
        ACommand::Pop(n) => Ok(env.arena.pop(n.clone())),
        ACommand::Push(n) => Ok(env.arena.push(n.clone())),
        ACommand::Reset => Ok(env.arena.reset()),
        ACommand::ResetAssertions => Ok(env.arena.reset_assertions()),
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
        self.let_elim(&mut env.arena)
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
