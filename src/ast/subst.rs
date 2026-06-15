// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Local substitution of variables in terms.
//!
//! This module provides [`Substitution`], a mapping from local variable IDs to replacement
//! terms, and the [`Substitute`] trait for applying substitutions. The substitution operation
//! correctly handles variable shadowing in binders (`let`, `forall`, `exists`, `match`):
//! a substitution is suspended inside a scope that re-binds the same variable.
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
//! let loc = q.get_direct_bindings()[0].clone().into();
//! let subst = Substitution::new([(loc, one)]);
//! let result = term.subst(&subst, &mut q);
//! assert_eq!(result.to_string(), "(+ 1 y)");
//! ```
//!
//! For expanding global definitions (e.g. `define-fun` bodies), see [`crate::ast::gsubst`].

use crate::allocator::{LocalVarAllocator, TermAllocator};
use crate::ast::alg::VarBinding;
use crate::ast::{
    Attribute, Constant, HasArena, Local, Memoize, Pattern, PatternArm, QualifiedIdentifier, Sort,
    Str, Term, TermRecursor, TypedBuilder, TypedTermRecursor,
};
use crate::containers::Mapping;
use crate::raw::alg::rec::Bottom;
use delegate::delegate;
use std::collections::HashMap;
use yaspar::ast::Keyword;

/// A mapping from local variable IDs to replacement terms.
///
/// Create with [`Substitution::new`] (from `Local`–term pairs) or [`Substitution::empty`].
/// Apply to a term via the [`Substitute`] trait.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Substitution(HashMap<usize, Term>);

impl Default for Substitution {
    fn default() -> Self {
        Substitution::empty()
    }
}

impl Substitution {
    /// Create an empty substitution.
    pub fn empty() -> Self {
        Self(HashMap::new())
    }

    /// Create a substitution from an iterator of `(Local, Term)` pairs.
    pub fn new(bindings: impl IntoIterator<Item = (Local, Term)>) -> Self {
        let map = bindings.into_iter().map(|(l, t)| (l.id, t)).collect();
        Substitution(map)
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

    /// Push a binding by raw local variable ID.
    pub(crate) fn push_with_id(&mut self, loc_id: usize, term: Term) {
        self.0.insert(loc_id, term);
    }

    /// Push multiple bindings by raw local variable IDs.
    pub(crate) fn extend_with_id(&mut self, bindings: impl IntoIterator<Item = (usize, Term)>) {
        for (id, term) in bindings {
            self.0.insert(id, term);
        }
    }
}

/// A backport support for using [SubstitutionV2]
pub type SubstitutionV2 = Substitution;

/// Apply a substitution to `Self`.
///
/// Note that it is the caller's responsibility to maintain well-sortedness invariance.
pub trait Substitute<E> {
    /// The type produced by the substitution.
    type Out;

    /// Apply the substitution, returning a new value with locals replaced.
    fn subst(&self, subst: &Substitution, env: &mut E) -> Self::Out;
}

/// A backport support for [SubstituteV2]
pub trait SubstituteV2<E> {
    type Out;

    fn subst(&self, subst: &Substitution, env: &mut E) -> Self::Out;
}

impl<E, X> SubstituteV2<E> for X
where
    X: Substitute<E>,
{
    type Out = <X as Substitute<E>>::Out;

    fn subst(&self, subst: &Substitution, env: &mut E) -> Self::Out {
        Substitute::subst(self, subst, env)
    }
}

impl<E> Substitute<E> for [Term]
where
    E: HasArena,
{
    type Out = Vec<Term>;

    fn subst(&self, subst: &Substitution, env: &mut E) -> Self::Out {
        let mut s = Substituter::create(env, subst);
        self.iter().map(|t| s.recurse_on_term_no_err(t)).collect()
    }
}

impl<E> Substitute<E> for Term
where
    E: HasArena,
{
    type Out = Self;

    fn subst(&self, subst: &Substitution, env: &mut E) -> Self::Out {
        Substituter::create(env, subst).recurse_on_term_no_err(self)
    }
}

/// Memoized, stack-safe local substituter. Use [`Substituter::create`] to construct.
pub type Substituter<'a, E> = Memoize<SubstituterInner<'a, E>, HashMap<Term, Term>>;

impl<'a, E> Substituter<'a, E>
where
    E: HasArena,
{
    /// Create a new memoized substituter backed by the given arena and substitution.
    pub fn create(env: &'a mut E, subst: &'a Substitution) -> Self {
        Memoize::new(SubstituterInner::new(env, subst))
    }
}

/// Stack-safe local substitution using [`TermRecursor`].
///
/// Replaces local variables by ID according to a [`Substitution`]. Binders (`let`, `forall`,
/// `exists`, `match`) shadow substitutions for re-bound variables.
pub struct SubstituterInner<'a, E> {
    inner: TypedBuilder<'a, E>,
    /// The base substitution (local id → replacement term).
    subst: &'a Substitution,
    /// Shadow stack: each frame maps a local variable id to a fresh id, blocking substitution in scoped bodies.
    shadows: Vec<HashMap<usize, usize>>,
}

impl<'a, E: HasArena> SubstituterInner<'a, E> {
    /// Create a new substituter backed by the given arena and substitution.
    pub fn new(arena: &'a mut E, subst: &'a Substitution) -> Self {
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
