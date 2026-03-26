// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Monomorphization of parametric datatypes.
//!
//! This module provides functionality to instantiate parametric datatypes with concrete sorts,
//! eliminating sort variables by substituting them with ground types.

use crate::allocator::{LocalVarAllocator, TermAllocator};
use crate::ast::alg;
use crate::ast::alg::VarBinding;
use crate::ast::{
    ATerm, Attribute, ConstructorDec, DatatypeDec, HasArenaAlt, Local, QualifiedIdentifier, Sort,
    Str, TC, Term,
};
use crate::locenv::LocEnv;
use crate::raw::tc::unif::{SortSubst, apply_subst};
use crate::traits::Repr;

/// Trait for monomorphizing parametric types by substituting sort variables with concrete sorts.
pub trait Monomorphization<E, I> {
    type Output;

    /// Monomorphize `self` using the provided input and environment.
    fn monomorphize(&self, input: &I, env: &mut E) -> Self::Output;
}

/// Environment for monomorphizing terms, tracking local variable ID mappings.
struct TermMonoEnv<'a, E> {
    arena: &'a mut E,
    local: LocEnv<'a, Str, ()>,
}

/// Apply a sort substitution to a sort, replacing sort variables with their concrete instantiations.
impl<E> Monomorphization<E, SortSubst> for Sort
where
    E: HasArenaAlt,
{
    type Output = Self;
    fn monomorphize(&self, input: &SortSubst, env: &mut E) -> Self {
        apply_subst(env, input, self)
    }
}

/// Monomorphize a variable binding by applying the substitution to its second component.
impl<E, S, T> Monomorphization<E, SortSubst> for VarBinding<S, T>
where
    E: HasArenaAlt,
    S: Clone,
    T: Monomorphization<E, SortSubst, Output = T>,
{
    type Output = Self;
    fn monomorphize(&self, input: &SortSubst, env: &mut E) -> Self {
        Self(self.0.clone(), self.1, self.2.monomorphize(input, env))
    }
}

/// Monomorphize a constructor declaration by applying the substitution to all argument sorts.
impl<E> Monomorphization<E, SortSubst> for ConstructorDec
where
    E: HasArenaAlt,
{
    type Output = Self;
    fn monomorphize(&self, input: &SortSubst, env: &mut E) -> Self {
        Self {
            ctor: self.ctor.clone(),
            args: self
                .args
                .iter()
                .map(|b| b.monomorphize(input, env))
                .collect(),
        }
    }
}

/// Compute the substitution for [Sort] based on a [DatatypeDec]
pub fn find_sort_subst_from_datatype_dec(dec: &DatatypeDec, input: &Sort) -> TC<SortSubst> {
    if dec.params.len() != input.1.len() {
        return Err(format!(
            "Sort {input} has {} sub-sorts, but {} are required!",
            input.1.len(),
            dec.params.len()
        ));
    }

    Ok(dec
        .params
        .iter()
        .zip(input.1.iter())
        .map(|(a, b)| (a.clone(), Some(b.clone())))
        .collect())
}

/// Monomorphize a datatype declaration by instantiating its sort parameters with concrete sorts.
///
/// Given a parametric datatype and a concrete sort instantiation, this creates a new datatype
/// with no parameters where all occurrences of sort variables are replaced with the provided sorts.
impl<E> Monomorphization<E, Sort> for DatatypeDec
where
    E: HasArenaAlt,
{
    type Output = TC<DatatypeDec>;

    fn monomorphize(&self, input: &Sort, env: &mut E) -> Self::Output {
        let subst = find_sort_subst_from_datatype_dec(self, input)?;

        Ok(DatatypeDec {
            params: vec![],
            constructors: self
                .constructors
                .iter()
                .map(|ctor| ctor.monomorphize(&subst, env))
                .collect(),
        })
    }
}

/// Monomorphize a qualified identifier by applying the substitution to its optional sort.
fn monomorphize_qid<E: HasArenaAlt>(
    qid: &QualifiedIdentifier,
    subst: &SortSubst,
    env: &mut E,
) -> QualifiedIdentifier {
    alg::QualifiedIdentifier(
        qid.0.clone(),
        qid.1.as_ref().map(|s| s.monomorphize(subst, env)),
    )
}

/// Monomorphize an attribute by applying the substitution to pattern terms.
fn monomorphize_attribute<'a, E: HasArenaAlt>(
    attr: &Attribute,
    subst: &SortSubst,
    env: &mut TermMonoEnv<'a, E>,
) -> Attribute {
    match attr {
        Attribute::Pattern(ts) => Attribute::Pattern(
            ts.iter()
                .map(|t| monomorphize_term(t, subst, env))
                .collect(),
        ),
        _ => attr.clone(),
    }
}

/// Recursively monomorphize a term by substituting sort variables with concrete sorts.
///
/// This traverses the term structure, applying the sort substitution to all embedded sorts
/// (in constants, globals, locals, applications, quantifiers, etc.) and re-allocating local
/// variable IDs to avoid collisions. Delegates to [`monomorphize_qid`] for qualified identifiers
/// and [`monomorphize_attribute`] for annotations.
fn monomorphize_term<'a, E: HasArenaAlt>(
    term: &Term,
    subst: &SortSubst,
    env: &mut TermMonoEnv<'a, E>,
) -> Term {
    match term.repr() {
        ATerm::Constant(c, sort) => {
            let s = sort.as_ref().map(|s| s.monomorphize(subst, env.arena));
            env.arena.arena_alt().constant(c.clone(), s)
        }
        ATerm::Global(id, sort) => {
            let nid = monomorphize_qid(id, subst, env.arena);
            let s = sort.as_ref().map(|s| s.monomorphize(subst, env.arena));
            env.arena.arena_alt().global(nid, s)
        }
        ATerm::Local(l) => {
            if let Some((new_id, _)) = env.local.lookup(&l.symbol) {
                let new_sort = l.sort.as_ref().map(|s| s.monomorphize(subst, env.arena));
                env.arena.arena_alt().local(Local {
                    id: new_id,
                    symbol: l.symbol.clone(),
                    sort: new_sort,
                })
            } else {
                term.clone()
            }
        }
        ATerm::App(id, ts, sort) => {
            let nid = monomorphize_qid(id, subst, env.arena);
            let nts = ts
                .iter()
                .map(|t| monomorphize_term(t, subst, env))
                .collect();
            let s = sort.as_ref().map(|s| s.monomorphize(subst, env.arena));
            env.arena.arena_alt().app(nid, nts, s)
        }
        ATerm::Let(bindings, body) => {
            let nbindings: Vec<_> = bindings
                .iter()
                .map(|b| {
                    let new_id = env.arena.arena_alt().new_local();
                    VarBinding(b.0.clone(), new_id, monomorphize_term(&b.2, subst, env))
                })
                .collect();
            let tracking: Vec<_> = nbindings
                .iter()
                .map(|b| VarBinding(b.0.clone(), b.1, ()))
                .collect();
            let local = env.local.insert(&tracking).unwrap();
            let mut new_env = TermMonoEnv {
                arena: env.arena,
                local,
            };
            let nbody = monomorphize_term(body, subst, &mut new_env);
            env.arena.arena_alt().let_term(nbindings, nbody)
        }
        ATerm::Exists(vars, body) => {
            let nvars: Vec<_> = vars
                .iter()
                .map(|v| {
                    let new_id = env.arena.arena_alt().new_local();
                    VarBinding(v.0.clone(), new_id, v.2.monomorphize(subst, env.arena))
                })
                .collect();
            let tracking: Vec<_> = nvars
                .iter()
                .map(|v| VarBinding(v.0.clone(), v.1, ()))
                .collect();
            let local = env.local.insert(&tracking).unwrap();
            let mut new_env = TermMonoEnv {
                arena: env.arena,
                local,
            };
            let nbody = monomorphize_term(body, subst, &mut new_env);
            env.arena.arena_alt().exists(nvars, nbody)
        }
        ATerm::Forall(vars, body) => {
            let nvars: Vec<_> = vars
                .iter()
                .map(|v| {
                    let new_id = env.arena.arena_alt().new_local();
                    VarBinding(v.0.clone(), new_id, v.2.monomorphize(subst, env.arena))
                })
                .collect();
            let tracking: Vec<_> = nvars
                .iter()
                .map(|v| VarBinding(v.0.clone(), v.1, ()))
                .collect();
            let local = env.local.insert(&tracking).unwrap();
            let mut new_env = TermMonoEnv {
                arena: env.arena,
                local,
            };
            let nbody = monomorphize_term(body, subst, &mut new_env);
            env.arena.arena_alt().forall(nvars, nbody)
        }
        ATerm::Matching(scrutinee, cases) => {
            let nscrutinee = monomorphize_term(scrutinee, subst, env);
            let ncases = cases
                .iter()
                .map(|c| {
                    let vars: Vec<_> = c
                        .pattern
                        .variables()
                        .iter()
                        .map(|&s| {
                            let new_id = env.arena.arena_alt().new_local();
                            VarBinding(s.clone(), new_id, ())
                        })
                        .collect();
                    let local = env.local.insert(&vars).unwrap();
                    let mut new_env = TermMonoEnv {
                        arena: env.arena,
                        local,
                    };
                    crate::ast::alg::PatternArm {
                        pattern: c.pattern.clone(),
                        body: monomorphize_term(&c.body, subst, &mut new_env),
                    }
                })
                .collect();
            env.arena.arena_alt().matching(nscrutinee, ncases)
        }
        ATerm::Annotated(t, anns) => {
            let nt = monomorphize_term(t, subst, env);
            let nanns = anns
                .iter()
                .map(|a| monomorphize_attribute(a, subst, env))
                .collect();
            env.arena.arena_alt().annotated(nt, nanns)
        }
        ATerm::Eq(a, b) => {
            let na = monomorphize_term(a, subst, env);
            let nb = monomorphize_term(b, subst, env);
            env.arena.arena_alt().eq(na, nb)
        }
        ATerm::Distinct(ts) => {
            let nts = ts
                .iter()
                .map(|t| monomorphize_term(t, subst, env))
                .collect();
            env.arena.arena_alt().distinct(nts)
        }
        ATerm::And(ts) => {
            let nts = ts
                .iter()
                .map(|t| monomorphize_term(t, subst, env))
                .collect();
            env.arena.arena_alt().and(nts)
        }
        ATerm::Or(ts) => {
            let nts = ts
                .iter()
                .map(|t| monomorphize_term(t, subst, env))
                .collect();
            env.arena.arena_alt().or(nts)
        }
        ATerm::Xor(ts) => {
            let nts = ts
                .iter()
                .map(|t| monomorphize_term(t, subst, env))
                .collect();
            env.arena.arena_alt().xor(nts)
        }
        ATerm::Implies(ts, concl) => {
            let nts = ts
                .iter()
                .map(|t| monomorphize_term(t, subst, env))
                .collect();
            let nconcl = monomorphize_term(concl, subst, env);
            env.arena.arena_alt().implies(nts, nconcl)
        }
        ATerm::Not(t) => {
            let nt = monomorphize_term(t, subst, env);
            env.arena.arena_alt().not(nt)
        }
        ATerm::Ite(c, t, e) => {
            let nc = monomorphize_term(c, subst, env);
            let nt = monomorphize_term(t, subst, env);
            let ne = monomorphize_term(e, subst, env);
            env.arena.arena_alt().ite(nc, nt, ne)
        }
    }
}

/// Monomorphize a term by applying the sort substitution.
impl<E> Monomorphization<E, SortSubst> for Term
where
    E: HasArenaAlt,
{
    type Output = Self;

    fn monomorphize(&self, subst: &SortSubst, env: &mut E) -> Self {
        let mut mono_env = TermMonoEnv {
            arena: env,
            local: LocEnv::Nil,
        };
        monomorphize_term(self, subst, &mut mono_env)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::allocator::{ObjectAllocatorExt, SortAllocator, StrAllocator};
    use crate::ast::{ASortDef, Context, Typecheck};
    use crate::untyped::UntypedAst;

    /// Test monomorphizing a parametric `List` datatype with `Int`.
    /// Declares `(List (par (X) ...))`, instantiates it as `(List Int)`, and verifies
    /// that all constructor argument sorts in the result are closed (no open sort variables).
    #[test]
    fn test_sort_monomorphize() {
        let mut ctx = Context::new();
        ctx.ensure_logic();

        UntypedAst
            .parse_command_str(
                "(declare-datatype List (par (X) ((nil) (cons (car X) (cdr (List X))))))",
            )
            .unwrap()
            .type_check(&mut ctx)
            .unwrap();

        let int = ctx.int_sort();
        let list_sym = ctx.allocate_symbol("List");
        let list_int = ctx.sort_n(list_sym.clone(), vec![int]);
        let dt = match ctx.get_sort_def(&list_sym).unwrap() {
            ASortDef::Datatype(d) => d.clone(),
            _ => panic!("Expected datatype"),
        };
        let mono_dt = dt.monomorphize(&list_int, &mut ctx).unwrap();

        for ctor in &mono_dt.constructors {
            for arg in &ctor.args {
                // TC makes sure no open sort variable.
                arg.2.type_check(&mut ctx).unwrap();
            }
        }
    }

    /// Test monomorphizing a parametric `Pair` datatype with `Int` and `Bool`.
    /// Declares `(Pair (par (A B) ...))`, instantiates it as `(Pair Int Bool)`, and verifies
    /// that all constructor argument sorts in the result are closed (no open sort variables).
    #[test]
    fn test_constructor_monomorphize() {
        let mut ctx = Context::new();
        ctx.ensure_logic();

        UntypedAst
            .parse_command_str("(declare-datatype Pair (par (A B) ((mk-pair (fst A) (snd B)))))")
            .unwrap()
            .type_check(&mut ctx)
            .unwrap();

        let int = ctx.int_sort();
        let bool = ctx.bool_sort();
        let pair_sym = ctx.allocate_symbol("Pair");
        let pair = ctx.sort_n(pair_sym.clone(), vec![int, bool]);
        let dt = match ctx.get_sort_def(&pair_sym).unwrap() {
            ASortDef::Datatype(d) => d.clone(),
            _ => panic!("Expected datatype"),
        };
        let mono_dt = dt.monomorphize(&pair, &mut ctx).unwrap();

        for ctor in &mono_dt.constructors {
            for arg in &ctor.args {
                // TC makes sure no open sort variable.
                arg.2.type_check(&mut ctx).unwrap();
            }
        }
    }

    /// Test monomorphizing a simple global term whose sort contains a sort variable.
    /// Builds `(as nil (List X))` with sort variable `X`, monomorphizes with `X -> Int`,
    /// and verifies the result is `(as nil (List Int))`.
    #[test]
    fn test_term_monomorphize_global() {
        let mut ctx = Context::new();
        ctx.ensure_logic();

        UntypedAst
            .parse_command_str(
                "(declare-datatype List (par (X) ((nil) (cons (car X) (cdr (List X))))))",
            )
            .unwrap()
            .type_check(&mut ctx)
            .unwrap();

        let x_sym = ctx.allocate_symbol("X");
        let x_sort = ctx.sort0(x_sym.clone());
        let list_sym = ctx.allocate_symbol("List");
        let list_x = ctx.sort_n(list_sym, vec![x_sort]);
        let nil_sym = ctx.allocate_symbol("nil");
        let nil = ctx.global(
            alg::QualifiedIdentifier::simple_sorted(nil_sym, list_x.clone()),
            Some(list_x),
        );

        let int = ctx.int_sort();
        let subst: SortSubst = [(x_sym, Some(int))].into_iter().collect();
        let result = nil.monomorphize(&subst, &mut ctx);
        assert_eq!(result.to_string(), "(as nil (List Int))");
        result.type_check(&mut ctx).unwrap();
    }

    /// Test monomorphizing a function application term with sort variables.
    /// Builds `(cons x (as nil (List X)))` with sort variable `X`, monomorphizes with `X -> Int`,
    /// and verifies the result is `(cons x (as nil (List Int)))`.
    #[test]
    fn test_term_monomorphize_app() {
        let mut ctx = Context::new();
        ctx.ensure_logic();

        UntypedAst
            .parse_command_str(
                "(declare-datatype List (par (X) ((nil) (cons (car X) (cdr (List X))))))",
            )
            .unwrap()
            .type_check(&mut ctx)
            .unwrap();

        UntypedAst
            .parse_command_str("(declare-const x Int)")
            .unwrap()
            .type_check(&mut ctx)
            .unwrap();

        let x_sym = ctx.allocate_symbol("X");
        let x_sort = ctx.sort0(x_sym.clone());
        let list_sym = ctx.allocate_symbol("List");
        let list_x = ctx.sort_n(list_sym, vec![x_sort.clone()]);

        let nil_sym = ctx.allocate_symbol("nil");
        let nil = ctx.global(
            alg::QualifiedIdentifier::simple_sorted(nil_sym, list_x.clone()),
            Some(list_x.clone()),
        );

        let x_var = ctx.simple_sorted_symbol("x", x_sort);
        let cons_sym = ctx.allocate_symbol("cons");
        let cons_app = ctx.app(
            alg::QualifiedIdentifier::simple(cons_sym),
            vec![x_var, nil],
            Some(list_x),
        );

        let int = ctx.int_sort();
        let subst: SortSubst = [(x_sym, Some(int))].into_iter().collect();
        let result = cons_app.monomorphize(&subst, &mut ctx);
        assert_eq!(result.to_string(), "(cons x (as nil (List Int)))");
        result.type_check(&mut ctx).unwrap();
    }

    /// Test monomorphizing a let-binding term with sort variables in the bound value.
    /// Builds `(let ((y (as nil (List X)))) y)` with sort variable `X`, monomorphizes
    /// with `X -> Bool`, and verifies the result preserves the let structure with
    /// the substituted sort.
    #[test]
    fn test_term_monomorphize_let() {
        let mut ctx = Context::new();
        ctx.ensure_logic();

        UntypedAst
            .parse_command_str(
                "(declare-datatype List (par (X) ((nil) (cons (car X) (cdr (List X))))))",
            )
            .unwrap()
            .type_check(&mut ctx)
            .unwrap();

        let x_sym = ctx.allocate_symbol("X");
        let x_sort = ctx.sort0(x_sym.clone());
        let list_sym = ctx.allocate_symbol("List");
        let list_x = ctx.sort_n(list_sym, vec![x_sort]);

        let nil_sym = ctx.allocate_symbol("nil");
        let nil = ctx.global(
            alg::QualifiedIdentifier::simple_sorted(nil_sym, list_x.clone()),
            Some(list_x),
        );

        let y_sym = ctx.allocate_symbol("y");
        let y_id = ctx.new_local();
        let y_local = ctx.local(Local {
            id: y_id,
            symbol: y_sym.clone(),
            sort: None,
        });
        let let_term = ctx.let_term(vec![VarBinding(y_sym, y_id, nil)], y_local);

        let bool_sort = ctx.bool_sort();
        let subst: SortSubst = [(x_sym, Some(bool_sort))].into_iter().collect();
        let result = let_term.monomorphize(&subst, &mut ctx);
        assert_eq!(result.to_string(), "(let ((y (as nil (List Bool)))) y)");
        result.type_check(&mut ctx).unwrap();
    }

    /// Test monomorphizing a quantified term with sort variables in the bound variable sorts.
    /// Builds `(forall ((x X)) (= x x))` with sort variable `X`, monomorphizes with `X -> Real`,
    /// and verifies the result is `(forall ((x Real)) (= x x))`.
    #[test]
    fn test_term_monomorphize_forall() {
        let mut ctx = Context::new();
        ctx.ensure_logic();

        let x_sym = ctx.allocate_symbol("X");
        let x_sort = ctx.sort0(x_sym.clone());

        let var_sym = ctx.allocate_symbol("x");
        let var_id = ctx.new_local();
        let var_local = ctx.local(Local {
            id: var_id,
            symbol: var_sym.clone(),
            sort: Some(x_sort.clone()),
        });
        let eq = ctx.eq(var_local.clone(), var_local);
        let forall = ctx.forall(vec![VarBinding(var_sym, var_id, x_sort)], eq);

        let real = ctx.real_sort();
        let subst: SortSubst = [(x_sym, Some(real))].into_iter().collect();
        let result = forall.monomorphize(&subst, &mut ctx);
        assert_eq!(result.to_string(), "(forall ((x Real)) (= x x))");
        result.type_check(&mut ctx).unwrap();
    }

    /// Test monomorphizing an existential quantifier.
    /// Builds `(exists ((x X)) (= x x))` with sort variable `X`, monomorphizes with `X -> Int`,
    /// and verifies the result is `(exists ((x Int)) (= x x))`.
    #[test]
    fn test_term_monomorphize_exists() {
        let mut ctx = Context::new();
        ctx.ensure_logic();

        let x_sym = ctx.allocate_symbol("X");
        let x_sort = ctx.sort0(x_sym.clone());

        let var_sym = ctx.allocate_symbol("x");
        let var_id = ctx.new_local();
        let var_local = ctx.local(Local {
            id: var_id,
            symbol: var_sym.clone(),
            sort: Some(x_sort.clone()),
        });
        let eq = ctx.eq(var_local.clone(), var_local);
        let exists = ctx.exists(vec![VarBinding(var_sym, var_id, x_sort)], eq);

        let int = ctx.int_sort();
        let subst: SortSubst = [(x_sym, Some(int))].into_iter().collect();
        let result = exists.monomorphize(&subst, &mut ctx);
        assert_eq!(result.to_string(), "(exists ((x Int)) (= x x))");
        result.type_check(&mut ctx).unwrap();
    }

    /// Test monomorphizing `not`, `ite`, and `distinct` terms.
    #[test]
    fn test_term_monomorphize_logical_ops() {
        let mut ctx = Context::new();
        ctx.ensure_logic();

        let x_sym = ctx.allocate_symbol("X");
        let x_sort = ctx.sort0(x_sym.clone());

        let var_sym = ctx.allocate_symbol("a");
        let var_id = ctx.new_local();
        let a = ctx.local(Local {
            id: var_id,
            symbol: var_sym.clone(),
            sort: Some(x_sort.clone()),
        });

        let b_sym = ctx.allocate_symbol("b");
        let b_id = ctx.new_local();
        let b = ctx.local(Local {
            id: b_id,
            symbol: b_sym.clone(),
            sort: Some(x_sort.clone()),
        });

        // (distinct a b)
        let dist = ctx.distinct(vec![a.clone(), b.clone()]);
        // (not (distinct a b))
        let neg = ctx.not(dist.clone());
        // (ite (distinct a b) a b)
        let ite = ctx.ite(dist, a, b);

        let int = ctx.int_sort();
        let subst: SortSubst = [(x_sym, Some(int))].into_iter().collect();

        let neg_result = neg.monomorphize(&subst, &mut ctx);
        assert_eq!(neg_result.to_string(), "(not (distinct a b))");

        let ite_result = ite.monomorphize(&subst, &mut ctx);
        assert_eq!(ite_result.to_string(), "(ite (distinct a b) a b)");
    }

    /// Test monomorphizing `and`, `or`, and `implies` terms.
    #[test]
    fn test_term_monomorphize_connectives() {
        let mut ctx = Context::new();
        ctx.ensure_logic();

        let x_sym = ctx.allocate_symbol("X");
        let x_sort = ctx.sort0(x_sym.clone());

        let a_sym = ctx.allocate_symbol("a");
        let a_id = ctx.new_local();
        let a = ctx.local(Local {
            id: a_id,
            symbol: a_sym.clone(),
            sort: Some(x_sort.clone()),
        });
        let b_sym = ctx.allocate_symbol("b");
        let b_id = ctx.new_local();
        let b = ctx.local(Local {
            id: b_id,
            symbol: b_sym.clone(),
            sort: Some(x_sort.clone()),
        });

        let eq_ab = ctx.eq(a.clone(), b.clone());
        let eq_ba = ctx.eq(b, a);

        let conj = ctx.and(vec![eq_ab.clone(), eq_ba.clone()]);
        let disj = ctx.or(vec![eq_ab.clone(), eq_ba.clone()]);
        let imp = ctx.implies(vec![eq_ab], eq_ba);

        let int = ctx.int_sort();
        let subst: SortSubst = [(x_sym, Some(int))].into_iter().collect();

        assert_eq!(
            conj.monomorphize(&subst, &mut ctx).to_string(),
            "(and (= a b) (= b a))"
        );
        assert_eq!(
            disj.monomorphize(&subst, &mut ctx).to_string(),
            "(or (= a b) (= b a))"
        );
        assert_eq!(
            imp.monomorphize(&subst, &mut ctx).to_string(),
            "(=> (= a b) (= b a))"
        );
    }

    /// Test monomorphizing a match expression with sort variables.
    #[test]
    fn test_term_monomorphize_matching() {
        let mut ctx = Context::new();
        ctx.ensure_logic();

        UntypedAst
            .parse_command_str(
                "(declare-datatype List (par (X) ((nil) (cons (car X) (cdr (List X))))))",
            )
            .unwrap()
            .type_check(&mut ctx)
            .unwrap();

        // Build: (match (as nil (List X)) ((nil 0) ((cons h t) 1)))
        // using unchecked APIs with sort variable X
        let x_sym = ctx.allocate_symbol("X");
        let x_sort = ctx.sort0(x_sym.clone());
        let list_sym = ctx.allocate_symbol("List");
        let list_x = ctx.sort_n(list_sym, vec![x_sort]);

        let nil_sym = ctx.allocate_symbol("nil");
        let nil = ctx.global(
            alg::QualifiedIdentifier::simple_sorted(nil_sym, list_x.clone()),
            Some(list_x),
        );

        let int_sort = ctx.int_sort();
        let zero = ctx.constant(alg::Constant::Numeral(0u8.into()), Some(int_sort.clone()));
        let one = ctx.constant(alg::Constant::Numeral(1u8.into()), Some(int_sort));

        let nil_pattern = alg::Pattern::Ctor(ctx.allocate_symbol("nil"));
        let h_sym = ctx.allocate_symbol("h");
        let h_id = ctx.new_local();
        let t_sym = ctx.allocate_symbol("t");
        let t_id = ctx.new_local();
        let cons_pattern = alg::Pattern::Applied {
            ctor: ctx.allocate_symbol("cons"),
            arguments: vec![Some((h_sym, h_id)), Some((t_sym, t_id))],
        };

        let match_term = ctx.matching(
            nil.clone(),
            vec![
                alg::PatternArm {
                    pattern: nil_pattern,
                    body: zero,
                },
                alg::PatternArm {
                    pattern: cons_pattern,
                    body: one,
                },
            ],
        );

        let int = ctx.int_sort();
        let subst: SortSubst = [(x_sym, Some(int))].into_iter().collect();
        let result = match_term.monomorphize(&subst, &mut ctx);
        // The match structure should be preserved with substituted sorts
        assert!(result.to_string().contains("match"));
        assert!(result.to_string().contains("(as nil (List Int))"));
    }
}
