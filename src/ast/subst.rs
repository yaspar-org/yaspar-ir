// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

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

use crate::allocator::TermAllocator;
use crate::ast::alg::VarBinding;
use crate::ast::{ATerm, Arena, Attribute, HasArena, HasArenaAlt, PatternArm, Str, Term};
use crate::containers::MemLinkedList;
use crate::raw::alg::rec::Bottom;
use crate::raw::alg::{Constant, Local, QualifiedIdentifier};
use crate::raw::instance;
use crate::traits::{AllocatableString, Repr};
use std::collections::HashMap;
use yaspar::ast::Keyword;

use crate::ast::{Sort, TermRecursor, TypedTermRecursor};

/// A mapping from variable names to replacement terms.
///
/// Create with [`Substitution::new`] (from name–term pairs) or [`Substitution::empty`].
/// Apply to a term via the [`Substitute`] trait.
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

/// Stack-safe local substitution using [`TermRecursor`].
///
/// Replaces local variables by name according to a [`Substitution`]. Binders (`let`, `forall`,
/// `exists`, `match`) shadow substitutions for re-bound names. Unlike [`LetEliminatorInner`],
/// let-bindings are preserved — only the RHS values are recursed and the body sees shadows.
pub struct Substituter<'a, E> {
    arena: &'a mut E,
    /// The base substitution (name → replacement term).
    subst: &'a Substitution,
    /// Shadow stack: each frame maps names to `None` to block substitution in scoped bodies.
    shadows: Vec<HashMap<Str, ()>>,
}

impl<'a, E: HasArena> Substituter<'a, E> {
    pub fn new(arena: &'a mut E, subst: &'a Substitution) -> Self {
        Self {
            arena,
            subst,
            shadows: Vec::new(),
        }
    }

    /// Look up a variable name. Returns `Some(term)` if substitution applies,
    /// `None` if shadowed or not in the substitution.
    fn lookup(&self, name: &Str) -> Option<Term> {
        // Check shadows from innermost to outermost
        for frame in self.shadows.iter().rev() {
            if frame.contains_key(name) {
                return None; // shadowed
            }
        }
        // Fall through to the base substitution
        self.subst.0.get(name).and_then(|v| v.clone())
    }

    fn push_shadow<T>(&mut self, names: impl Iterator<Item = T>, f: impl Fn(&T) -> Str) {
        self.shadows
            .push(names.map(|n| (f(&n), ())).collect());
    }
}

impl<E: HasArena> TermRecursor<Str, Sort, Term> for Substituter<'_, E> {
    type Out = Term;
    type Attr = instance::Attribute;
    type Binding = Term;
    type Pattern = ();
    type Arm = instance::PatternArm;
    type Err = Bottom;

    fn on_constant(
        &mut self,
        current: &Term,
        _: &Constant<Str>,
        _: &Option<Sort>,
    ) -> Result<Term, Bottom> {
        Ok(current.clone())
    }

    fn on_global(
        &mut self,
        current: &Term,
        _: &QualifiedIdentifier<Str, Sort>,
        _: &Option<Sort>,
    ) -> Result<Term, Bottom> {
        Ok(current.clone())
    }

    fn on_local(&mut self, current: &Term, id: &Local<Str, Sort>) -> Result<Term, Bottom> {
        Ok(self.lookup(&id.symbol).unwrap_or_else(|| current.clone()))
    }

    fn on_app(
        &mut self,
        _: &Term,
        id: &QualifiedIdentifier<Str, Sort>,
        _: &[Term],
        s: &Option<Sort>,
        recs: Vec<Term>,
    ) -> Result<Term, Bottom> {
        Ok(self.arena.arena().app(id.clone(), recs, s.clone()))
    }

    fn on_eq(&mut self, _: &Term, _: &Term, _: &Term, a: Term, b: Term) -> Result<Term, Bottom> {
        Ok(self.arena.arena().eq(a, b))
    }

    fn on_distinct(&mut self, _: &Term, _: &[Term], recs: Vec<Term>) -> Result<Term, Bottom> {
        Ok(self.arena.arena().distinct(recs))
    }

    fn on_and(&mut self, _: &Term, _: &[Term], recs: Vec<Term>) -> Result<Term, Bottom> {
        Ok(self.arena.arena().and(recs))
    }

    fn on_or(&mut self, _: &Term, _: &[Term], recs: Vec<Term>) -> Result<Term, Bottom> {
        Ok(self.arena.arena().or(recs))
    }

    fn on_xor(&mut self, _: &Term, _: &[Term], recs: Vec<Term>) -> Result<Term, Bottom> {
        Ok(self.arena.arena().xor(recs))
    }

    fn on_not(&mut self, _: &Term, _: &Term, r: Term) -> Result<Term, Bottom> {
        Ok(self.arena.arena().not(r))
    }

    fn on_implies(
        &mut self,
        _: &Term,
        _: &[Term],
        _: &Term,
        ps: Vec<Term>,
        c: Term,
    ) -> Result<Term, Bottom> {
        Ok(self.arena.arena().implies(ps, c))
    }

    fn on_ite(
        &mut self,
        _: &Term,
        _: &Term,
        _: &Term,
        _: &Term,
        b: Term,
        t: Term,
        e: Term,
    ) -> Result<Term, Bottom> {
        Ok(self.arena.arena().ite(b, t, e))
    }

    // --- Let: RHS is recursed normally, body gets shadows for bound names ---

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

    /// Shadow the let-bound variable names before entering the body.
    fn setup_let_scope(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Term>],
        _: &Term,
        _: &[Term],
    ) -> Result<(), Bottom> {
        self.push_shadow(vs.iter(), |v| v.0.clone());
        Ok(())
    }

    /// Rebuild the let with recursed bindings and body, then pop the shadow.
    fn on_let(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Term>],
        _: &Term,
        vs_rec: Vec<Term>,
        body: Term,
    ) -> Result<Term, Bottom> {
        self.shadows.pop();
        let nbindings = vs
            .iter()
            .zip(vs_rec)
            .map(|(v, r)| VarBinding(v.0.clone(), v.1, r))
            .collect();
        Ok(self.arena.arena().let_term(nbindings, body))
    }

    // --- Quantifiers: shadow bound names ---

    fn setup_quantifier_scope(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Sort>],
        _: &Term,
        _: bool,
    ) -> Result<(), Bottom> {
        self.push_shadow(vs.iter(), |v| v.0.clone());
        Ok(())
    }

    fn on_forall(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Sort>],
        _: &Term,
        body: Term,
    ) -> Result<Term, Bottom> {
        self.shadows.pop();
        Ok(self.arena.arena().forall(vs.to_vec(), body))
    }

    fn on_exists(
        &mut self,
        _: &Term,
        vs: &[VarBinding<Str, Sort>],
        _: &Term,
        body: Term,
    ) -> Result<Term, Bottom> {
        self.shadows.pop();
        Ok(self.arena.arena().exists(vs.to_vec(), body))
    }

    // --- Match: shadow pattern-bound names ---

    fn setup_match_case_scope(
        &mut self,
        _: &Term,
        _: &Term,
        cases: &[instance::PatternArm],
        _: &Term,
        idx: usize,
    ) -> Result<(), Bottom> {
        self.push_shadow(cases[idx].pattern.variables().into_iter(), |v| (*v).clone());
        Ok(())
    }

    fn on_match_arm(
        &mut self,
        _: &Term,
        _: &Term,
        cases: &[instance::PatternArm],
        idx: usize,
        _: (),
        body: Term,
    ) -> Result<instance::PatternArm, Bottom> {
        self.shadows.pop();
        Ok(instance::PatternArm {
            pattern: cases[idx].pattern.clone(),
            body,
        })
    }

    fn on_match(
        &mut self,
        _: &Term,
        _: &Term,
        _: &[instance::PatternArm],
        scrutinee: Term,
        arms: Vec<instance::PatternArm>,
    ) -> Result<Term, Bottom> {
        Ok(self.arena.arena().matching(scrutinee, arms))
    }

    // --- Annotated ---

    fn on_annotated(
        &mut self,
        _: &Term,
        _: &Term,
        _: &[instance::Attribute],
        r: Term,
        anns: Vec<instance::Attribute>,
    ) -> Result<Term, Bottom> {
        Ok(self.arena.arena().annotated(r, anns))
    }

    fn on_attribute_keyword(&mut self, kw: &Keyword) -> Result<instance::Attribute, Bottom> {
        Ok(instance::Attribute::Keyword(kw.clone()))
    }

    fn on_attribute_constant(
        &mut self,
        kw: &Keyword,
        c: &Constant<Str>,
    ) -> Result<instance::Attribute, Bottom> {
        Ok(instance::Attribute::Constant(kw.clone(), c.clone()))
    }

    fn on_attribute_symbol(
        &mut self,
        kw: &Keyword,
        s: &Str,
    ) -> Result<instance::Attribute, Bottom> {
        Ok(instance::Attribute::Symbol(kw.clone(), s.clone()))
    }

    fn on_attribute_named(&mut self, name: &Str) -> Result<instance::Attribute, Bottom> {
        Ok(instance::Attribute::Named(name.clone()))
    }

    fn on_attribute_pattern(
        &mut self,
        _: &[Term],
        recs: Vec<Term>,
    ) -> Result<instance::Attribute, Bottom> {
        Ok(instance::Attribute::Pattern(recs))
    }
}

impl<E: HasArena> TypedTermRecursor for Substituter<'_, E> {}
