// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Monomorphization of parametric datatypes.
//!
//! This module provides functionality to instantiate parametric datatypes with concrete sorts,
//! eliminating sort variables by substituting them with ground types.

use super::boilerplates::TypedBuilder;
use crate::allocator::{LocalVarAllocator, TermAllocator};
use crate::ast::alg::VarBinding;
use crate::ast::{
    Attribute, Constant, ConstructorDec, DatatypeDec, HasArena, HasArenaAlt, Local,
    QualifiedIdentifier, Sort, Str, TC, Term,
};
use crate::ast::{Memoize, alg};
use crate::containers::Mapping;
use crate::raw::alg::rec::Bottom;
use crate::raw::instance::PatternArm;
use crate::raw::tc::unif::{SortSubst, apply_subst};
use delegate::delegate;
use std::collections::HashMap;
use yaspar::ast::Keyword;

use crate::ast::{TermRecursor, TypedTermRecursor};

/// Trait for monomorphizing parametric types by substituting sort variables with concrete sorts.
pub trait Monomorphization<E, I> {
    type Output;

    /// Monomorphize `self` using the provided input and environment.
    fn monomorphize(&self, input: &I, env: &mut E) -> Self::Output;
}

/// Stack-safe term monomorphization using [`TermRecursor`].
///
/// Applies a [`SortSubst`] to every sort embedded in a term (constants, globals, locals,
/// applications, quantifier bindings) and re-allocates local variable IDs to avoid collisions.
///
/// The environment stack maps `(name, old_id)` to `new_id` for scoped constructs.
pub struct MonomorphizerInner<'a, E> {
    inner: TypedBuilder<'a, E>,
    subst: &'a SortSubst,
    /// Scoped old-id → new-id mappings. Each frame corresponds to a let, quantifier, or match arm.
    env: Vec<HashMap<(Str, usize), usize>>,
}

pub type Monomorphizer<'a, E> = Memoize<MonomorphizerInner<'a, E>, HashMap<Term, Term>>;

impl<'a, E> Monomorphizer<'a, E>
where
    E: HasArena,
{
    pub fn create(arena: &'a mut E, subst: &'a SortSubst) -> Self {
        Memoize::new(MonomorphizerInner::new(arena, subst))
    }
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

/// Monomorphize a term by applying the sort substitution.
impl<E> Monomorphization<E, SortSubst> for Term
where
    E: HasArena,
{
    type Output = Self;

    fn monomorphize(&self, subst: &SortSubst, env: &mut E) -> Self {
        let mut mono = MonomorphizerInner::new(env, subst);
        mono.recurse_on_term_no_err(self)
    }
}

impl<'a, E: HasArena> MonomorphizerInner<'a, E> {
    pub fn new(arena: &'a mut E, subst: &'a SortSubst) -> Self {
        Self {
            inner: TypedBuilder::new(arena),
            subst,
            env: Vec::new(),
        }
    }

    fn mono_sort(&mut self, s: &Sort) -> Sort {
        apply_subst(self.inner.arena(), self.subst, s)
    }

    fn mono_opt_sort(&mut self, s: &Option<Sort>) -> Option<Sort> {
        s.as_ref().map(|s| self.mono_sort(s))
    }

    fn mono_qid(&mut self, qid: &QualifiedIdentifier) -> QualifiedIdentifier {
        alg::QualifiedIdentifier(qid.0.clone(), self.mono_opt_sort(&qid.1))
    }

    /// Look up a local variable's new id from the env stack.
    fn lookup_new_id(&self, name: &Str, id: usize) -> Option<usize> {
        let key = (name.clone(), id);
        self.env.lookup(&key)
    }

    /// Allocate new local IDs for a set of bindings and push a scope frame.
    fn push_scope_for<T>(&mut self, vs: &[VarBinding<Str, T>]) {
        let frame = vs
            .iter()
            .map(|v| {
                let new_id = self.inner.arena().new_local();
                ((v.0.clone(), v.1), new_id)
            })
            .collect();
        self.env.push(frame);
    }

    /// Get the new id for a binding from the current top frame.
    fn new_id_for(&self, name: &Str, old_id: usize) -> usize {
        self.env.last().unwrap()[&(name.clone(), old_id)]
    }

    /// Monomorphize quantifier bindings: remap IDs and apply sort substitution.
    /// Pops the scope frame.
    fn mono_quantifier_vars(&mut self, vs: &[VarBinding<Str, Sort>]) -> Vec<VarBinding<Str, Sort>> {
        let nvars = vs
            .iter()
            .map(|v| {
                VarBinding(
                    v.0.clone(),
                    self.new_id_for(&v.0, v.1),
                    self.mono_sort(&v.2),
                )
            })
            .collect();
        self.env.pop();
        nvars
    }
}

impl<E: HasArena> TermRecursor<Str, Sort, Term> for MonomorphizerInner<'_, E> {
    type Out = Term;
    type Attr = Attribute;
    type Binding = Term;
    type Pattern = ();
    type Arm = PatternArm;
    type Err = Bottom;

    delegate! {
        to self.inner {
            fn on_match(&mut self, current: &Term, scrutinee: &Term, cases: &[PatternArm], scrutinee_rec: Self::Out, cases_rec: Vec<Self::Arm>) -> Result<Term, Bottom>;
            fn on_annotated(&mut self, current: &Term, t: &Term, anns: &[Attribute], t_rec: Term, anns_rec: Vec<Attribute>) -> Result<Term, Bottom>;
            fn on_attribute_keyword(&mut self, keyword: &Keyword) -> Result<Attribute, Bottom>;
            fn on_attribute_constant(&mut self, keyword: &Keyword, constant: &Constant) -> Result<Attribute, Bottom>;
            fn on_attribute_symbol(&mut self, keyword: &Keyword, symbol: &Str) -> Result<Attribute, Bottom>;
            fn on_attribute_named(&mut self, name: &Str) -> Result<Attribute, Bottom>;
            fn on_attribute_pattern(&mut self, patterns: &[Term], patterns_rec: Vec<Term>) -> Result<Attribute, Bottom>;
            fn on_eq(&mut self, current: &Term, a: &Term, b: &Term, a_rec: Term, b_rec: Term) -> Result<Term, Bottom>;
            fn on_distinct(&mut self, current: &Term, ts: &[Term], ts_rec: Vec<Term>) -> Result<Term, Bottom>;
            fn on_and(&mut self, current: &Term, ts: &[Term], ts_rec: Vec<Term>) -> Result<Term, Bottom>;
            fn on_or(&mut self, current: &Term, ts: &[Term], ts_rec: Vec<Term>) -> Result<Term, Bottom>;
            fn on_xor(&mut self, current: &Term, ts: &[Term], ts_rec: Vec<Term>) -> Result<Term, Bottom>;
            fn on_not(&mut self, current: &Term, t: &Term, t_rec: Term) -> Result<Term, Bottom>;
            fn on_implies(&mut self, current: &Term, ts: &[Term], t: &Term, ts_rec: Vec<Term>, t_rec: Term) -> Result<Term, Bottom>;
            fn on_ite(&mut self, current: &Term, b: &Term, t: &Term, e: &Term, b_rec: Term, t_rec: Term, e_rec: Term) -> Result<Term, Bottom>;
        }
    }

    // --- Leaves (custom: apply sort substitution) ---

    fn on_constant(&mut self, _: &Term, c: &Constant, sort: &Option<Sort>) -> Result<Term, Bottom> {
        let s = self.mono_opt_sort(sort);
        Ok(self.inner.arena().constant(c.clone(), s))
    }

    fn on_global(
        &mut self,
        _: &Term,
        id: &QualifiedIdentifier,
        sort: &Option<Sort>,
    ) -> Result<Term, Bottom> {
        let nid = self.mono_qid(id);
        let s = self.mono_opt_sort(sort);
        Ok(self.inner.arena().global(nid, s))
    }

    fn on_local(&mut self, current: &Term, l: &Local) -> Result<Term, Bottom> {
        Ok(if let Some(new_id) = self.lookup_new_id(&l.symbol, l.id) {
            let new_sort = self.mono_sort(&l.sort);
            self.inner.arena().local(Local {
                id: new_id,
                symbol: l.symbol.clone(),
                sort: new_sort,
            })
        } else {
            current.clone()
        })
    }

    // --- App (custom: apply sort substitution to qid and sort) ---

    fn on_app(
        &mut self,
        _: &Term,
        id: &QualifiedIdentifier,
        _: &[Term],
        sort: &Option<Sort>,
        recs: Vec<Term>,
    ) -> Result<Term, Bottom> {
        let nid = self.mono_qid(id);
        let s = self.mono_opt_sort(sort);
        Ok(self.inner.arena().app(nid, recs, s))
    }

    // --- Let (custom: remap local IDs) ---

    fn on_let_binding(
        &mut self,
        _: &Term,
        _: &[VarBinding<Str, Term>],
        _: &Term,
        _: usize,
        rec: Term,
    ) -> Result<Term, Bottom> {
        Ok(rec)
    }

    fn setup_let_scope(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Term>],
        _: &Term,
        _: &[Term],
    ) -> Result<(), Bottom> {
        self.push_scope_for(vs);
        Ok(())
    }

    fn on_let(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Term>],
        _: &Term,
        vs_rec: Vec<Term>,
        body: Term,
    ) -> Result<Term, Bottom> {
        let nbindings = vs
            .iter()
            .zip(vs_rec)
            .map(|(v, rec)| VarBinding(v.0.clone(), self.new_id_for(&v.0, v.1), rec))
            .collect();
        self.env.pop();
        Ok(self.inner.arena().let_term(nbindings, body))
    }

    // --- Quantifiers (custom: remap IDs + monomorphize sorts) ---

    fn setup_quantifier_scope(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Sort>],
        _: &Term,
        _: bool,
    ) -> Result<(), Bottom> {
        self.push_scope_for(vs);
        Ok(())
    }

    fn on_exists(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Sort>],
        _: &Term,
        body: Term,
    ) -> Result<Term, Bottom> {
        let nvars = self.mono_quantifier_vars(vs);
        Ok(self.inner.arena().exists(nvars, body))
    }

    fn on_forall(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Sort>],
        _: &Term,
        body: Term,
    ) -> Result<Term, Bottom> {
        let nvars = self.mono_quantifier_vars(vs);
        Ok(self.inner.arena().forall(nvars, body))
    }

    // --- Match (custom: remap pattern variable IDs) ---

    fn setup_match_case_scope(
        &mut self,
        _: &Term,
        _: &Term,
        cases: &[PatternArm],
        _: &Term,
        idx: usize,
    ) -> Result<(), Bottom> {
        let vars = cases[idx].pattern.variables_and_ids();
        let frame = vars
            .into_iter()
            .map(|(name, old_id)| {
                let new_id = self.inner.arena().new_local();
                ((name, old_id), new_id)
            })
            .collect();
        self.env.push(frame);
        Ok(())
    }

    fn on_match_arm(
        &mut self,
        _: &Term,
        _: &Term,
        cases: &[PatternArm],
        _scrutinee_rec: &Term,
        idx: usize,
        _: (),
        body: Term,
    ) -> Result<PatternArm, Bottom> {
        let arm = PatternArm {
            pattern: cases[idx].pattern.clone(),
            body,
        };
        self.env.pop();
        Ok(arm)
    }
}

impl<E: HasArena> TypedTermRecursor for MonomorphizerInner<'_, E> {}

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
            Some(list_x.clone()),
        );

        let y_sym = ctx.allocate_symbol("y");
        let y_id = ctx.new_local();
        let y_local = ctx.local(Local {
            id: y_id,
            symbol: y_sym.clone(),
            sort: list_x,
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
            sort: x_sort.clone(),
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
            sort: x_sort.clone(),
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
            sort: x_sort.clone(),
        });

        let b_sym = ctx.allocate_symbol("b");
        let b_id = ctx.new_local();
        let b = ctx.local(Local {
            id: b_id,
            symbol: b_sym.clone(),
            sort: x_sort.clone(),
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
            sort: x_sort.clone(),
        });
        let b_sym = ctx.allocate_symbol("b");
        let b_id = ctx.new_local();
        let b = ctx.local(Local {
            id: b_id,
            symbol: b_sym.clone(),
            sort: x_sort.clone(),
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
