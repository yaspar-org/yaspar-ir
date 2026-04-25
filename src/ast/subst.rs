// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// The legacy `Substitution` / `Substitute` API is deprecated but still implemented here.
#![allow(deprecated)]

//! Local substitution of variables in terms.
//!
//! This module provides [`Substitution`], a mapping from variable names to replacement terms,
//! and the [`Substitute`] trait for applying substitutions to terms. The substitution operation
//! correctly handles variable shadowing in binders (`let`, `forall`, `exists`, `match`):
//! a substitution for `x` is suspended inside a scope that re-binds `x`.
//!
//! # Example
//!
//! ```rust
//! use yaspar_ir::ast::{CheckedApi, Context, ScopedSortApi, Typecheck};
//! use yaspar_ir::ast::subst::{Substitution, Substitute};
//! use yaspar_ir::untyped::UntypedAst;
//!
//! let mut context = Context::new();
//! context.ensure_logic();
//! let int = context.wf_sort("Int").unwrap();
//! let mut q = context.build_quantifier_with_domain([("x", int.clone()), ("y", int)]).unwrap();
//! let term = UntypedAst.parse_term_str("(+ x y)").unwrap().type_check(&mut q).unwrap();
//! let one = q.numeral(1u8.into()).unwrap();
//! let subst = Substitution::new([("x", one)], &mut q);
//! let result = term.subst(&subst, &mut q);
//! assert_eq!(result.to_string(), "(+ 1 y)");
//! ```
//!
//! For expanding global definitions (e.g. `define-fun` bodies), see [`crate::ast::gsubst`].

use crate::allocator::{LocalVarAllocator, TermAllocator};
use crate::ast::alg::VarBinding;
use crate::ast::{
    ATerm, Arena, Attribute, Constant, HasArena, HasArenaAlt,
    Local, Memoize, Pattern, PatternArm, QualifiedIdentifier, Sort, Str, Term,
    TermRecursor, TypedBuilder, TypedTermRecursor,
};
use crate::containers::{Mapping, MemLinkedList};
use crate::raw::alg::rec::Bottom;
use crate::traits::{AllocatableString, Repr};
use delegate::delegate;
use std::collections::HashMap;
use yaspar::ast::Keyword;

/// A mapping from variable names to replacement terms.
///
/// Create with [`Substitution::new`] (from name–term pairs) or [`Substitution::empty`].
/// Apply to a term via the [`Substitute`] trait.
#[deprecated = "this type is to be replaced in 2.7.4"]
pub struct Substitution(HashMap<Str, Option<Term>>);

impl Substitution {
    pub fn empty() -> Substitution {
        Substitution(HashMap::new())
    }

    pub fn new_str(bindings: impl IntoIterator<Item = (Str, Term)>) -> Substitution {
        let map = bindings.into_iter().map(|(s, t)| (s, Some(t))).collect();
        Substitution(map)
    }

    pub fn new<S, E>(bindings: impl IntoIterator<Item = (S, Term)>, env: &mut E) -> Substitution
    where
        S: AllocatableString<Arena>,
        E: HasArena,
    {
        Self::new_str(
            bindings
                .into_iter()
                .map(|(s, t)| (s.allocate(env.arena()), t)),
        )
    }

    /// Push one more binding to the substitution
    ///
    /// c.f. [Self::extend]
    pub fn push(&mut self, name: Str, term: Term) {
        self.0.insert(name, Some(term));
    }

    /// Push multiple bindings to the substitution
    ///
    /// c.f. [Self::push]
    pub fn extend(&mut self, bindings: impl IntoIterator<Item = (Str, Term)>) {
        for (name, term) in bindings {
            self.0.insert(name, Some(term));
        }
    }
}

impl Default for Substitution {
    fn default() -> Substitution {
        Substitution::empty()
    }
}

/// Apply a substitution to `Self`.
///
/// Note that it is the caller's responsibility to maintain well-sortedness invariance.
#[deprecated = "this trait is to be replaced in 2.7.4"]
pub trait Substitute<E> {
    fn subst(&self, subst: &Substitution, env: &mut E) -> Self;
}

/// A stack of substitutions to handle shadowing
type SubstList<'a> = MemLinkedList<'a, Substitution>;

impl SubstList<'_> {
    fn lookup(&self, x: &Str) -> Option<Term> {
        match self {
            SubstList::Nil => None,
            SubstList::Cons { car, cdr } => {
                if let Some(t) = car.0.get(x) {
                    t.clone()
                } else {
                    cdr.lookup(x)
                }
            }
        }
    }
}

trait SubstituteImpl<E> {
    fn subst_impl(&self, substs: &SubstList, env: &mut E) -> Self;
}

impl<E, X> Substitute<E> for X
where
    E: HasArenaAlt,
    X: SubstituteImpl<E>,
{
    fn subst(&self, subst: &Substitution, env: &mut E) -> Self {
        self.subst_impl(
            &SubstList::Cons {
                car: subst,
                cdr: &SubstList::Nil,
            },
            env,
        )
    }
}

impl<E, T> SubstituteImpl<E> for Vec<T>
where
    E: HasArenaAlt,
    T: SubstituteImpl<E>,
{
    fn subst_impl(&self, substs: &SubstList, env: &mut E) -> Self {
        self.iter().map(|a| a.subst_impl(substs, env)).collect()
    }
}

impl<E> SubstituteImpl<E> for Attribute
where
    E: HasArenaAlt,
{
    fn subst_impl(&self, substs: &SubstList, env: &mut E) -> Self {
        match self {
            Attribute::Pattern(t) => Attribute::Pattern(t.subst_impl(substs, env)),
            _ => self.clone(),
        }
    }
}

fn subst_binder_shadow<V, E>(
    vars: &[V],
    body: &Term,
    substs: &SubstList,
    env: &mut E,
    f: impl Fn(&V) -> Str,
) -> Term
where
    E: HasArenaAlt,
{
    let shadow = vars.iter().map(|v| (f(v), None)).collect();
    let subst = Substitution(shadow);
    body.subst_impl(
        &SubstList::Cons {
            car: &subst,
            cdr: substs,
        },
        env,
    )
}

impl<E> SubstituteImpl<E> for Term
where
    E: HasArenaAlt,
{
    fn subst_impl(&self, substs: &SubstList, env: &mut E) -> Self {
        match self.repr() {
            ATerm::Constant(_, _) | ATerm::Global(_, _) => self.clone(),
            ATerm::Local(var) => {
                if let Some(t) = substs.lookup(&var.symbol) {
                    t
                } else {
                    self.clone()
                }
            }
            ATerm::App(f, args, s) => {
                let nargs = args.subst_impl(substs, env);
                env.arena_alt().app(f.clone(), nargs, s.clone())
            }
            ATerm::Let(bindings, body) => {
                let nbindings = bindings
                    .iter()
                    .map(|b| VarBinding(b.0.clone(), b.1, b.2.subst_impl(substs, env)))
                    .collect();
                let nbody = subst_binder_shadow(bindings, body, substs, env, |v| v.0.clone());
                env.arena_alt().let_term(nbindings, nbody)
            }
            ATerm::Exists(vars, body) => {
                let nbody = subst_binder_shadow(vars, body, substs, env, |v| v.0.clone());
                env.arena_alt().exists(vars.clone(), nbody)
            }
            ATerm::Forall(vars, body) => {
                let nbody = subst_binder_shadow(vars, body, substs, env, |v| v.0.clone());
                env.arena_alt().forall(vars.clone(), nbody)
            }
            ATerm::Matching(t, cases) => {
                let nt = t.subst_impl(substs, env);
                let ncases = cases
                    .iter()
                    .map(|c| {
                        let nbody = subst_binder_shadow(
                            &c.pattern.variables(),
                            &c.body,
                            substs,
                            env,
                            |v| Str::clone(v),
                        );
                        PatternArm {
                            pattern: c.pattern.clone(),
                            body: nbody,
                        }
                    })
                    .collect();
                env.arena_alt().matching(nt, ncases)
            }
            ATerm::Annotated(t, annos) => {
                let nt = t.subst_impl(substs, env);
                let nannos = annos.subst_impl(substs, env);
                env.arena_alt().annotated(nt, nannos)
            }
            ATerm::Eq(a, b) => {
                let na = a.subst_impl(substs, env);
                let nb = b.subst_impl(substs, env);
                env.arena_alt().eq(na, nb)
            }
            ATerm::Distinct(ts) => {
                let nts = ts.subst_impl(substs, env);
                env.arena_alt().distinct(nts)
            }
            ATerm::And(ts) => {
                let nts = ts.subst_impl(substs, env);
                env.arena_alt().and(nts)
            }
            ATerm::Or(ts) => {
                let nts = ts.subst_impl(substs, env);
                env.arena_alt().or(nts)
            }
            ATerm::Xor(ts) => {
                let nts = ts.subst_impl(substs, env);
                env.arena_alt().xor(nts)
            }
            ATerm::Implies(ts, concl) => {
                let nts = ts.subst_impl(substs, env);
                let concl = concl.subst_impl(substs, env);
                env.arena_alt().implies(nts, concl)
            }
            ATerm::Not(t) => {
                let nt = t.subst_impl(substs, env);
                env.arena_alt().not(nt)
            }
            ATerm::Ite(c, t, e) => {
                let nc = c.subst_impl(substs, env);
                let nt = t.subst_impl(substs, env);
                let ne = e.subst_impl(substs, env);
                env.arena_alt().ite(nc, nt, ne)
            }
        }
    }
}

/// A mapping from variable names to replacement terms.
///
/// Create with [`SubstitutionV2::new`] (from name–term pairs) or [`SubstitutionV2::empty`].
/// Apply to a term via the [`SubstituteV2`] trait.
#[derive(Clone, Debug)]
pub struct SubstitutionV2(HashMap<usize, Term>);

impl Default for SubstitutionV2 {
    fn default() -> Self {
        SubstitutionV2::empty()
    }
}

impl SubstitutionV2 {
    pub fn empty() -> Self {
        Self(HashMap::new())
    }

    pub fn new(bindings: impl IntoIterator<Item = (Local, Term)>) -> Self {
        let map = bindings.into_iter().map(|(l, t)| (l.id, t)).collect();
        SubstitutionV2(map)
    }

    /// Push one more binding to the substitution
    ///
    /// c.f. [Self::extend]
    pub fn push(&mut self, loc: Local, term: Term) {
        self.push_with_id(loc.id, term)
    }

    /// Push multiple bindings to the substitution
    ///
    /// c.f. [Self::push]
    pub fn extend(&mut self, bindings: impl IntoIterator<Item = (Local, Term)>) {
        self.extend_with_id(bindings.into_iter().map(|(l, t)| (l.id, t)))
    }

    pub fn push_with_id(&mut self, loc_id: usize, term: Term) {
        self.0.insert(loc_id, term);
    }

    pub fn extend_with_id(&mut self, bindings: impl IntoIterator<Item = (usize, Term)>) {
        for (id, term) in bindings {
            self.0.insert(id, term);
        }
    }
}

/// Apply a substitution to `Self`.
///
/// Note that it is the caller's responsibility to maintain well-sortedness invariance.
pub trait SubstituteV2<E> {
    type Out;

    fn subst(&self, subst: &SubstitutionV2, env: &mut E) -> Self::Out;
}

impl<E> SubstituteV2<E> for [Term]
where
    E: HasArena,
{
    type Out = Vec<Term>;

    fn subst(&self, subst: &SubstitutionV2, env: &mut E) -> Self::Out {
        let mut s = Substituter::create(env, subst);
        self.iter().map(|t| s.recurse_on_term_no_err(t)).collect()
    }
}

impl<E> SubstituteV2<E> for Term
where
    E: HasArena,
{
    type Out = Self;

    fn subst(&self, subst: &SubstitutionV2, env: &mut E) -> Self::Out {
        Substituter::create(env, subst).recurse_on_term_no_err(self)
    }
}

pub type Substituter<'a, E> = Memoize<SubstituterInner<'a, E>, HashMap<Term, Term>>;

impl<'a, E> Substituter<'a, E>
where
    E: HasArena,
{
    pub fn create(env: &'a mut E, subst: &'a SubstitutionV2) -> Self {
        Memoize::new(SubstituterInner::new(env, subst))
    }
}

/// Stack-safe local substitution using [`TermRecursor`].
///
/// Replaces local variables by name according to a [`SubstitutionV2`]. Binders (`let`, `forall`,
/// `exists`, `match`) shadow substitutions for re-bound names. Unlike [`LetEliminatorInner`],
/// let-bindings are preserved — only the RHS values are recursed and the body sees shadows.
pub struct SubstituterInner<'a, E> {
    inner: TypedBuilder<'a, E>,
    /// The base substitution (name → replacement term).
    subst: &'a SubstitutionV2,
    /// Shadow stack: each frame maps local variable id to a fresh id and block substitution in scoped bodies.
    shadows: Vec<HashMap<usize, usize>>,
}

impl<'a, E: HasArena> SubstituterInner<'a, E> {
    pub fn new(arena: &'a mut E, subst: &'a SubstitutionV2) -> Self {
        Self {
            inner: TypedBuilder::new(arena),
            subst,
            shadows: Vec::new(),
        }
    }

    fn get_shadow(&self, id: usize) -> Option<usize> {
        self.shadows.lookup(&id)
    }
}

impl<E: HasArena> TermRecursor<Str, Sort, Term> for SubstituterInner<'_, E> {
    type Out = Term;
    type Attr = Attribute;
    type Binding = VarBinding<Str, Term>;
    type Pattern = Pattern;
    type Arm = PatternArm;
    type Err = Bottom;

    delegate! {
        to self.inner {
            fn on_constant(&mut self, current: &Term, constant: &Constant, sort: &Option<Sort>) -> Result<Term, Bottom>;
            fn on_global(&mut self, current: &Term, id: &QualifiedIdentifier, sort: &Option<Sort>) -> Result<Term, Bottom>;
            fn on_app(&mut self, current: &Term, f: &QualifiedIdentifier, args: &[Term], sort: &Option<Sort>, recs: Vec<Term>) -> Result<Term, Bottom>;
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

    fn on_local(&mut self, current: &Term, id: &Local) -> Result<Term, Bottom> {
        if let Some(new_id) = self.get_shadow(id.id) {
            let new_loc = Local {
                id: new_id,
                symbol: id.symbol.clone(),
                sort: id.sort.clone(),
            };

            return Ok(self.inner.local(new_loc));
        }
        if let Some(t) = self.subst.0.lookup(&id.id) {
            return Ok(t);
        }
        Ok(current.clone())
    }

    // --- Let: RHS is recursed normally, body gets shadows for bound names ---

    fn on_let_binding(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Term>],
        _body: &Term,
        binding_idx: usize,
        binding_rec: Term,
    ) -> Result<Self::Binding, Bottom> {
        let new_id = self.inner.new_local();
        let v = &vs[binding_idx];
        Ok(VarBinding(v.0.clone(), new_id, binding_rec))
    }
    fn setup_let_scope(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Term>],
        _body: &Term,
        vs_rec: &[Self::Binding],
    ) -> Result<(), Bottom> {
        self.shadows
            .push(vs.iter().zip(vs_rec).map(|(v1, v2)| (v1.1, v2.1)).collect());
        Ok(())
    }

    fn on_let(
        &mut self,
        _current: &Term,
        _vs: &[VarBinding<Str, Term>],
        _body: &Term,
        vs_rec: Vec<Self::Binding>,
        body_rec: Term,
    ) -> Result<Term, Bottom> {
        self.shadows.pop();
        Ok(self.inner.let_term(vs_rec, body_rec))
    }

    // --- Quantifiers: shadow bound names ---

    fn setup_quantifier_scope(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Sort>],
        _: &Term,
        _: bool,
    ) -> Result<(), Bottom> {
        self.shadows
            .push(vs.iter().map(|v| (v.1, self.inner.new_local())).collect());
        Ok(())
    }

    fn on_forall(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Sort>],
        _body: &Term,
        body_rec: Term,
    ) -> Result<Term, Bottom> {
        let map = self.shadows.pop().unwrap();
        let new_vs = vs
            .iter()
            .map(|v| VarBinding(v.0.clone(), *map.get(&v.1).unwrap(), v.2.clone()))
            .collect();
        Ok(self.inner.forall(new_vs, body_rec))
    }

    fn on_exists(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Sort>],
        _body: &Term,
        body_rec: Term,
    ) -> Result<Term, Bottom> {
        let map = self.shadows.pop().unwrap();
        let new_vs = vs
            .iter()
            .map(|v| VarBinding(v.0.clone(), *map.get(&v.1).unwrap(), v.2.clone()))
            .collect();
        Ok(self.inner.exists(new_vs, body_rec))
    }

    // --- Match: shadow pattern-bound names ---

    fn setup_match_case_scope(
        &mut self,
        _current: &Term,
        _scrutinee: &Term,
        cases: &[PatternArm],
        _scrutinee_rec: &Self::Out,
        case_idx: usize,
    ) -> Result<Pattern, Bottom> {
        let (map, pat) = match &cases[case_idx].pattern {
            Pattern::Wildcard(None) => (Default::default(), Pattern::Wildcard(None)),
            Pattern::Wildcard(Some((name, id))) => {
                let new_id = self.inner.new_local();
                (
                    HashMap::from([(*id, new_id)]),
                    Pattern::Wildcard(Some((name.clone(), new_id))),
                )
            }
            Pattern::Ctor(ctor) => (Default::default(), Pattern::Ctor(ctor.clone())),
            Pattern::Applied { ctor, arguments } => {
                let mut new_args = vec![];
                let mut map = HashMap::new();
                for a in arguments {
                    match a {
                        None => {
                            new_args.push(None);
                        }
                        Some((name, old_id)) => {
                            let new_id = self.inner.new_local();
                            new_args.push(Some((name.clone(), new_id)));
                            map.insert(*old_id, new_id);
                        }
                    }
                }
                (
                    map,
                    Pattern::Applied {
                        ctor: ctor.clone(),
                        arguments: new_args,
                    },
                )
            }
        };
        self.shadows.push(map);
        Ok(pat)
    }

    fn on_match_arm(
        &mut self,
        _current: &Term,
        _scrutinee: &Term,
        _cases: &[PatternArm],
        _scrutinee_rec: &Self::Out,
        _case_idx: usize,
        current_pattern: Pattern,
        arm: Term,
    ) -> Result<PatternArm, Bottom> {
        self.shadows.pop();
        Ok(PatternArm {
            pattern: current_pattern,
            body: arm,
        })
    }
}

impl<E: HasArena> TypedTermRecursor for SubstituterInner<'_, E> {}
