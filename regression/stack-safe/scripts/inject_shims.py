#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Give the harness both versions of every entry point it measures.

`#[stack_safe]` keeps, beside every function it rewrites, a copy as written: `f_orig`, which
recurses on the native stack and calls the other `_orig` copies of its scope. This script appends
to each file with covered functions an `__ssbench` module holding the entry points, written once
and compiled twice:

* in `__ssbench::stacksafe`, the covered names mean the rewritten functions;
* in `__ssbench::native`, each covered name is aliased to its `_orig` copy (`use f_orig as f`).

A crate-root `yaspar_ir::__ssbench::{stacksafe, native}` re-exposes them with public types. Where
yaspar-ir has a public entry point, `stacksafe` calls that instead, so a shim that stops matching
the wrapper it mirrors makes the two sides differ.

Nothing existing is edited: everything is appended after the last line of a file.

Usage: inject_shims.py <yaspar-ir source root>
"""
import pathlib
import sys

MARK = "// ---- injected by regression/stack-safe/scripts/inject_shims.py ----"


def shim(names: list[str], body: str, extra: str = "") -> str:
    """`body` twice: with `names` as the rewritten functions, and as their `_orig` copies."""
    aliases = "\n".join(
        f"                #[allow(unused_imports)] use super::super::{n}_orig as {n};" for n in names
    )
    return f"""
#[doc(hidden)]
#[allow(dead_code, private_interfaces, clippy::all)]
pub(crate) mod __ssbench {{
    #[allow(unused_imports)]
    use super::*;
    macro_rules! __ssbench_twice {{
        ($($body:tt)*) => {{
            pub(crate) mod stacksafe {{
                #[allow(unused_imports)]
                use super::super::*;
                $($body)*
            }}
            pub(crate) mod native {{
                #[allow(unused_imports)]
                use super::super::*;
{aliases}
                $($body)*
            }}
        }};
    }}
    __ssbench_twice! {{
{body}
    }}
{extra}
}}
"""


FILE_SHIMS = {
    "src/ast/cnf.rs": shim(["nnf_of", "pg_of", "tseitin_of"], """
    pub(crate) fn nnf(arena: &mut Arena, t: &Term) -> (Term, CNFCache) {
        let mut cache = CNFCache::new();
        let r = nnf_of(t, &mut CNFEnv { arena, cache: &mut cache }, true);
        (r, cache)
    }
    pub(crate) fn pg(arena: &mut Arena, t: &Term) -> (i32, Formula, CNFCache) {
        let mut cache = CNFCache::new();
        let mut formula = Formula::empty();
        let v = pg_of(t, &mut CNFEnv { arena, cache: &mut cache }, &mut formula);
        (v, formula, cache)
    }
    pub(crate) fn tseitin(arena: &mut Arena, t: &Term) -> (i32, Formula, CNFCache) {
        let mut cache = CNFCache::new();
        let mut formula = Formula::empty();
        let v = tseitin_of(t, &mut CNFEnv { arena, cache: &mut cache }, &mut formula);
        (v, formula, cache)
    }
"""),
    "src/ast/implicant.rs": shim(["implicant_of"], """
    /// Says every term is true, so an `or` descends into its first child.
    pub(crate) struct AllTrue;
    impl Model for AllTrue {
        fn evaluate(&mut self, _: &Term) -> Option<bool> {
            Some(true)
        }
        fn block(&mut self, _: &Term) {}
    }
    pub(crate) fn implicant(arena: &mut Arena, t: &Term) -> Term {
        implicant_of(t, arena, &mut AllTrue, false)
    }
"""),
    "src/ast/alpha_eq.rs": shim(["aeq_impl"], """
    pub(crate) fn aeq(a: &Term, b: &Term, permissive: bool) -> bool {
        aeq_impl(&mut AEqCtx::new(), a, b, permissive)
    }
"""),
    "src/ast/ctx/dt.rs": shim(["wf_sort"], """
    /// `wf_sort` at the top of a constructor argument, with no datatype being defined.
    pub(crate) fn wf_sort_top(ctx: &mut crate::ast::Context, s: &Sort) -> bool {
        let mut env = crate::ast::ScopedSortApi::get_sort_tcenv(ctx);
        wf_sort(&[], s, &mut env, true)
    }
"""),
    # a method: `use` cannot alias it, so each side is written out
    "src/ast/ctx/checked.rs": """
#[doc(hidden)]
#[allow(dead_code, clippy::all)]
pub(crate) mod __ssbench {
    pub(crate) mod stacksafe {
        use super::super::*;
        pub(crate) fn scan(ctx: &mut crate::ast::Context, t: &Term) -> (bool, HashMap<Str, Term>) {
            let mut acc = HashMap::new();
            let ok = ctx.scan_named(t, &mut acc).is_ok();
            (ok, acc)
        }
    }
    pub(crate) mod native {
        use super::super::*;
        pub(crate) fn scan(ctx: &mut crate::ast::Context, t: &Term) -> (bool, HashMap<Str, Term>) {
            let mut acc = HashMap::new();
            let ok = ctx.scan_named_orig(t, &mut acc).is_ok();
            (ok, acc)
        }
    }
}
""",
    "src/ast/letintro.rs": shim(["find_sections_of", "let_intro_of"], """
    use super::Prepared;
    /// The first half of `topo_let_intro`.
    pub(crate) fn find_sections(t: &Term) -> Prepared {
        let cell = Rc::new(RefCell::new(Section::new()));
        let mut map = HashMap::new();
        let _ = find_sections_of(t, &cell, &mut map, false);
        Prepared { cell, map }
    }
    /// The second half, on what `find_sections` produced for the same term.
    pub(crate) fn let_intro<E: HasArenaAlt>(t: &Term, p: &mut Prepared, env: &mut E) -> (Term, HashMap<Term, Local>) {
        let mut vars = HashMap::new();
        let r = let_intro_of(t, p.cell.clone(), &mut p.map, &mut vars, env);
        (r, vars)
    }
    /// Both halves, as `TopoLetIntro::topo_let_intro` runs them.
    pub(crate) fn topo_let_intro<E: HasArenaAlt>(t: &Term, env: &mut E) -> Term {
        let mut p = find_sections(t);
        let mut vars = HashMap::new();
        let_intro_of(t, p.cell.clone(), &mut p.map, &mut vars, env)
    }
""", extra="""
    /// What `find_sections` leaves for `let_intro`, from either side.
    pub struct Prepared {
        pub(crate) cell: SectionCell,
        pub(crate) map: HashMap<Term, SectionCell>,
    }

    /// Whether two runs of `find_sections` recorded the same sections: the same sub-terms with the
    /// same reference counts and levels, the same binders, and the same bound variables.
    pub(crate) fn same_sections(a: &SectionCell, b: &SectionCell) -> bool {
        let (a, b) = (a.borrow(), b.borrow());
        a.level == b.level
            && a.bound_variables == b.bound_variables
            && a.let_hierarchy.len() == b.let_hierarchy.len()
            && a.let_hierarchy.iter().all(|(t, r)| {
                b.let_hierarchy
                    .get(t)
                    .is_some_and(|s| s.referenced == r.referenced && s.level == r.level)
            })
    }
    pub(crate) fn same_prepared(a: &Prepared, b: &Prepared) -> bool {
        same_sections(&a.cell, &b.cell)
            && a.map.len() == b.map.len()
            && a.map.iter().all(|(t, c)| b.map.get(t).is_some_and(|d| same_sections(c, d)))
    }
"""),
    "src/ast/gsubst.rs": shim(["gsubst_term"], """
    /// `gsubst_with_names` on one term: a fresh cache of expanded definitions on every call.
    pub(crate) fn gsubst(ctx: &mut Context, names: &HashSet<Str>, t: &Term) -> Term {
        let mut cache = HashMap::new();
        let block = HashSet::new();
        let mut g = GlobalSubstituter::create(ctx, names, &block, &mut cache);
        gsubst_term(t, &mut g)
    }
"""),
    "src/raw/instance.rs": shim(["term_maybe_sort"], """
    /// `FetchSort::maybe_sort`: its fast path, then the descent.
    pub(crate) fn maybe_sort<T: HasArenaAlt>(t: &Term, arena: &mut T) -> Option<Sort> {
        match t.repr() {
            alg::Term::Constant(_, s) => s.clone(),
            alg::Term::Global(_, so) => so.clone(),
            alg::Term::Local(id) => Some(id.sort.clone()),
            alg::Term::App(_, _, s) => s.clone(),
            _ => term_maybe_sort(t, arena),
        }
    }
"""),
    "src/raw/tc.rs": shim(["tc_sort_rec"], """
    pub(crate) fn tc_sort(env: &mut crate::ast::TCEnv<'_, '_, ()>, s: &Sort) -> TC<Sort> {
        tc_sort_rec(s, env)
    }
"""),
    "src/raw/alg.rs": shim(["eval_bv_len"], """
    pub(crate) fn eval(e: &BvLenExpr) -> Result<UBig, String> {
        eval_bv_len(e, &[])
    }
"""),
    "src/raw/tc/unif.rs": shim(["sort_unification", "apply_subst"], """
    pub(crate) fn unify(subst: &mut SortSubst, expected: &Sort, ground: &Sort) -> TC<bool> {
        sort_unification(subst, expected, ground)
    }
    pub(crate) fn apply<A: HasArenaAlt>(arena: &mut A, subst: &SortSubst, s: &Sort) -> Sort {
        apply_subst(arena, subst, s)
    }
"""),
    # `Display` / `StructuredPrint::print`: a document, then its rendering
    "src/raw/alg/display.rs": shim(["write_term", "write_sort", "write_bv_len", "write_forest"], """
    pub(crate) fn show_term(t: &crate::ast::Term) -> String {
        let mut w = PrintSpace::new(&PrintConfig::UNLIMITED);
        let cut = write_term(t.repr(), &mut w).is_none();
        let mut out = String::new();
        let _ = write_forest(&w.finish(cut), &mut out);
        out
    }
    pub(crate) fn show_sort(s: &crate::ast::Sort) -> String {
        let mut w = PrintSpace::new(&PrintConfig::UNLIMITED);
        let cut = write_sort(s.repr(), &mut w).is_none();
        let mut out = String::new();
        let _ = write_forest(&w.finish(cut), &mut out);
        out
    }
    pub(crate) fn show_bv_len(e: &alg::BvLenExpr) -> String {
        let mut w = PrintSpace::new(&PrintConfig::UNLIMITED);
        let cut = write_bv_len(e, &mut w).is_none();
        let mut out = String::new();
        let _ = write_forest(&w.finish(cut), &mut out);
        out
    }
"""),
    "src/cvc5.rs": shim(["sort_to_cvc5", "conv_csort", "conv_cterm", "is_const_of"], """
    pub(crate) fn to_cvc5<'tm, Ctx>(s: &Sort, env: &mut Cvc5Env<'tm, Ctx>) -> Res<CSort<'tm>> {
        sort_to_cvc5(s, env)
    }
    pub(crate) fn from_csort<'tm, Ctx: HasMutRef<Context>>(cs: &CSort<'tm>, env: &mut Cvc5Env<'tm, Ctx>) -> Res<Sort> {
        conv_csort(cs, env)
    }
    pub(crate) fn from_cterm<'tm, Ctx: HasMutRef<Context>>(ct: &CTerm<'tm>, env: &mut Cvc5Env<'tm, Ctx>) -> Res<Term> {
        conv_cterm(ct, env)
    }
    pub(crate) fn is_const(t: &CTerm) -> bool {
        is_const_of(t.clone())
    }
"""),
}

# Re-exports that carry a shim out of a private module, one hop per parent.
REEXPORTS = {
    "src/ast/ctx/mod.rs": [
        "#[doc(hidden)] pub(crate) use dt::__ssbench as __ssbench_dt;",
        "#[doc(hidden)] pub(crate) use checked::__ssbench as __ssbench_checked;",
    ],
    "src/ast.rs": [
        "#[doc(hidden)] pub(crate) use ctx::{__ssbench_checked, __ssbench_dt};",
    ],
    "src/lib.rs": [
        "#[doc(hidden)] pub mod __ssbench;",
    ],
}

ROOT_SHIM = '''// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Injected by regression/stack-safe/scripts/inject_shims.py: every measured entry point, twice.
//! `stacksafe::f` runs the rewritten functions, `native::f` the `_orig` copies #[stack_safe] keeps;
//! both take and return the same public types.
#![allow(missing_docs, private_interfaces, unnameable_types, clippy::all)]

use crate::ast::{Context, Sort, SortSubst, Str, Term};
use std::collections::{HashMap, HashSet};

/// State a call leaves behind (a memo cache, fresh-variable bookkeeping) that is not part of its
/// answer, kept only so that dropping it happens outside the timed region.
pub struct Opaque<T>(#[allow(dead_code)] T);

/// What `find_sections` recorded, for `let_intro` and for comparing two runs.
pub struct LetIntroPrepared(crate::ast::letintro::__ssbench::Prepared);

impl LetIntroPrepared {
    /// Whether two runs recorded the same sections.
    pub fn same(&self, other: &Self) -> bool {
        crate::ast::letintro::__ssbench::same_prepared(&self.0, &other.0)
    }
}

pub fn empty_subst(vars: &[Str]) -> SortSubst {
    crate::raw::tc::unif::empty_subst(vars)
}

/// The entry points without a public counterpart: the same shim on both sides.
macro_rules! side {
    ($side:ident, { $($extra:tt)* }) => {
        pub mod $side {
            use super::*;
            use crate::ast::cnf::CNFCache;

            pub fn nnf(ctx: &mut Context, t: &Term) -> (Term, Opaque<CNFCache>) {
                let (r, cache) = crate::ast::cnf::__ssbench::$side::nnf(&mut ctx.arena, t);
                (r, Opaque(cache))
            }
            pub fn pg(ctx: &mut Context, t: &Term) -> (i32, sat_interface::Formula, Opaque<CNFCache>) {
                let (v, f, cache) = crate::ast::cnf::__ssbench::$side::pg(&mut ctx.arena, t);
                (v, f, Opaque(cache))
            }
            pub fn tseitin(ctx: &mut Context, t: &Term) -> (i32, sat_interface::Formula, Opaque<CNFCache>) {
                let (v, f, cache) = crate::ast::cnf::__ssbench::$side::tseitin(&mut ctx.arena, t);
                (v, f, Opaque(cache))
            }
            pub fn implicant(ctx: &mut Context, t: &Term) -> Term {
                crate::ast::implicant::__ssbench::$side::implicant(&mut ctx.arena, t)
            }
            pub fn wf_sort(ctx: &mut Context, s: &Sort) -> bool {
                crate::ast::__ssbench_dt::$side::wf_sort_top(ctx, s)
            }
            pub fn scan_named(ctx: &mut Context, t: &Term) -> (bool, HashMap<Str, Term>) {
                crate::ast::__ssbench_checked::$side::scan(ctx, t)
            }
            pub fn find_sections(t: &Term) -> LetIntroPrepared {
                LetIntroPrepared(crate::ast::letintro::__ssbench::$side::find_sections(t))
            }
            pub fn let_intro(ctx: &mut Context, t: &Term, p: &mut LetIntroPrepared) -> (Term, Opaque<HashMap<Term, crate::ast::Local>>) {
                let (r, vars) = crate::ast::letintro::__ssbench::$side::let_intro(t, &mut p.0, &mut ctx.arena);
                (r, Opaque(vars))
            }
            pub fn sort_unification(subst: &mut SortSubst, expected: &Sort, ground: &Sort) -> Result<bool, String> {
                crate::raw::tc::unif::__ssbench::$side::unify(subst, expected, ground)
            }
            pub fn apply_subst(ctx: &mut Context, subst: &SortSubst, s: &Sort) -> Sort {
                crate::raw::tc::unif::__ssbench::$side::apply(&mut ctx.arena, subst, s)
            }
            #[cfg(feature = "cvc5-dep")]
            pub fn is_const(t: &crate::cvc5::CTerm) -> bool {
                crate::cvc5::__ssbench::$side::is_const(t)
            }

            $($extra)*
        }
    };
}

// the rewritten functions, through yaspar-ir's own public entry points where there are any
side!(stacksafe, {
    use crate::ast::letintro::TopoLetIntro;
    use crate::ast::{AlphaEquiv, FetchSort, GlobalSubst, Typecheck};

    pub fn aeq(a: &Term, b: &Term, permissive: bool) -> bool {
        if permissive { a.aeq_permissive(b) } else { a.aeq(b) }
    }
    pub fn topo_let_intro(ctx: &mut Context, t: &Term) -> Term {
        t.topo_let_intro(&mut ctx.arena)
    }
    pub fn gsubst(ctx: &mut Context, names: &HashSet<Str>, t: &Term) -> Term {
        t.gsubst_with_names(names, ctx)
    }
    pub fn maybe_sort(ctx: &mut Context, t: &Term) -> Option<Sort> {
        t.maybe_sort(&mut ctx.arena)
    }
    pub fn tc_sort(ctx: &mut Context, s: &Sort) -> Result<Sort, String> {
        let mut env = crate::ast::ScopedSortApi::get_sort_tcenv(ctx);
        s.type_check(&mut env)
    }
    pub fn eval_bv_len(e: &crate::ast::alg::BvLenExpr) -> Result<dashu::integer::UBig, String> {
        e.eval(&[])
    }
    pub fn show_term(t: &Term) -> String {
        t.to_string()
    }
    pub fn show_sort(s: &Sort) -> String {
        s.to_string()
    }
    pub fn show_bv_len(e: &crate::ast::alg::BvLenExpr) -> String {
        e.to_string()
    }
    #[cfg(feature = "cvc5-dep")]
    pub fn sort_to_cvc5<'tm, Ctx>(s: &Sort, env: &mut crate::cvc5::Cvc5Env<'tm, Ctx>) -> Result<crate::cvc5::CSort<'tm>, String> {
        crate::cvc5::ConvertToCvc5::to_cvc5(s, env)
    }
    #[cfg(feature = "cvc5-dep")]
    pub fn conv_csort<'tm, Ctx: crate::traits::HasMutRef<Context>>(cs: &crate::cvc5::CSort<'tm>, env: &mut crate::cvc5::Cvc5Env<'tm, Ctx>) -> Result<Sort, String> {
        crate::cvc5::ConvertFromCvc5::conv_from_cvc5(cs, env)
    }
    #[cfg(feature = "cvc5-dep")]
    pub fn conv_cterm<'tm, Ctx: crate::traits::HasMutRef<Context>>(ct: &crate::cvc5::CTerm<'tm>, env: &mut crate::cvc5::Cvc5Env<'tm, Ctx>) -> Result<Term, String> {
        crate::cvc5::ConvertFromCvc5::conv_from_cvc5(ct, env)
    }
});

// the `_orig` copies, through shims that mirror those entry points
side!(native, {
    pub fn aeq(a: &Term, b: &Term, permissive: bool) -> bool {
        crate::ast::alpha_eq::__ssbench::native::aeq(a, b, permissive)
    }
    pub fn topo_let_intro(ctx: &mut Context, t: &Term) -> Term {
        crate::ast::letintro::__ssbench::native::topo_let_intro(t, &mut ctx.arena)
    }
    pub fn gsubst(ctx: &mut Context, names: &HashSet<Str>, t: &Term) -> Term {
        crate::ast::gsubst::__ssbench::native::gsubst(ctx, names, t)
    }
    pub fn maybe_sort(ctx: &mut Context, t: &Term) -> Option<Sort> {
        crate::raw::instance::__ssbench::native::maybe_sort(t, &mut ctx.arena)
    }
    pub fn tc_sort(ctx: &mut Context, s: &Sort) -> Result<Sort, String> {
        let mut env = crate::ast::ScopedSortApi::get_sort_tcenv(ctx);
        crate::raw::tc::__ssbench::native::tc_sort(&mut env, s)
    }
    pub fn eval_bv_len(e: &crate::ast::alg::BvLenExpr) -> Result<dashu::integer::UBig, String> {
        crate::raw::alg::__ssbench::native::eval(e)
    }
    pub fn show_term(t: &Term) -> String {
        crate::raw::alg::display::__ssbench::native::show_term(t)
    }
    pub fn show_sort(s: &Sort) -> String {
        crate::raw::alg::display::__ssbench::native::show_sort(s)
    }
    pub fn show_bv_len(e: &crate::ast::alg::BvLenExpr) -> String {
        crate::raw::alg::display::__ssbench::native::show_bv_len(e)
    }
    #[cfg(feature = "cvc5-dep")]
    pub fn sort_to_cvc5<'tm, Ctx>(s: &Sort, env: &mut crate::cvc5::Cvc5Env<'tm, Ctx>) -> Result<crate::cvc5::CSort<'tm>, String> {
        crate::cvc5::__ssbench::native::to_cvc5(s, env)
    }
    #[cfg(feature = "cvc5-dep")]
    pub fn conv_csort<'tm, Ctx: crate::traits::HasMutRef<Context>>(cs: &crate::cvc5::CSort<'tm>, env: &mut crate::cvc5::Cvc5Env<'tm, Ctx>) -> Result<Sort, String> {
        crate::cvc5::__ssbench::native::from_csort(cs, env)
    }
    #[cfg(feature = "cvc5-dep")]
    pub fn conv_cterm<'tm, Ctx: crate::traits::HasMutRef<Context>>(ct: &crate::cvc5::CTerm<'tm>, env: &mut crate::cvc5::Cvc5Env<'tm, Ctx>) -> Result<Term, String> {
        crate::cvc5::__ssbench::native::from_cterm(ct, env)
    }
});
'''


def append(path: pathlib.Path, text: str) -> None:
    src = path.read_text()
    if MARK in src:
        sys.exit(f"{path}: already injected")
    path.write_text(src.rstrip("\n") + "\n\n" + MARK + "\n" + text.strip("\n") + "\n")


def main() -> None:
    root = pathlib.Path(sys.argv[1])
    for rel, code in FILE_SHIMS.items():
        append(root / rel, code)
    for rel, lines in REEXPORTS.items():
        append(root / rel, "\n".join(lines))
    (root / "src/__ssbench.rs").write_text(ROOT_SHIM)
    print(f"injected shims into {len(FILE_SHIMS)} files")


if __name__ == "__main__":
    main()
