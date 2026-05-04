// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::allocator::TermAllocator;
use crate::ast::alg::VarBinding;
use crate::ast::{
    Arena, Attribute, Bottom, Constant, HasArena, Local, Pattern, PatternArm, QualifiedIdentifier,
    Sort, Str, Term, TermRecursor, TypedTermRecursor,
};
use yaspar::ast::Keyword;

/// A default [`TermRecursor`] implementation that rebuilds typed terms unchanged.
///
/// `TypedBuilder` provides the boilerplate "identity rebuild" callbacks: leaves are cloned,
/// compound nodes are reconstructed from their recursed children via the arena. It is designed
/// to be embedded in custom recursors via the [`delegate`](https://crates.io/crates/delegate)
/// crate, so that only the callbacks with custom logic need to be implemented manually.
///
/// # Usage pattern
///
/// Embed a `TypedBuilder` as a field in your recursor, then use `delegate!` to forward
/// the boilerplate callbacks:
///
/// ```text
/// pub struct MyRecursor<'a, E> {
///     inner: TypedBuilder<'a, E>,
///     // ... custom state ...
/// }
///
/// impl<E: HasArena> TermRecursor<Str, Sort, Term> for MyRecursor<'_, E> {
///     type Out = Term;
///     type Attr = Attribute;
///     type Binding = Term;
///     type Pattern = ();
///     type Arm = PatternArm;
///     type Err = Bottom;
///
///     // Delegate boilerplate (on_eq, on_and, on_or, on_annotated, etc.)
///     delegate! {
///         to self.inner {
///             fn on_eq(...) -> ...;
///             fn on_and(...) -> ...;
///             // ... all other rebuild-only callbacks ...
///         }
///     }
///
///     // Override only the callbacks with custom logic
///     fn on_local(&mut self, current: &Term, id: &Local) -> Result<Term, Bottom> {
///         // custom logic here
///     }
/// }
/// ```
///
/// See [`LetEliminatorInner`](crate::ast::letelim::LetEliminatorInner) and
/// [`MonomorphizerInner`](crate::ast::mono::MonomorphizerInner) for real-world examples.
pub struct TypedBuilder<'a, E> {
    pub arena: &'a mut E,
}

impl<'a, E> TypedBuilder<'a, E>
where
    E: HasArena,
{
    pub fn new(arena: &'a mut E) -> Self {
        Self { arena }
    }
}

impl<'a, E> HasArena for TypedBuilder<'a, E>
where
    E: HasArena,
{
    #[inline]
    fn arena(&mut self) -> &mut Arena {
        self.arena.arena()
    }
}

impl<'a, E> TermRecursor<Str, Sort, Term> for TypedBuilder<'a, E>
where
    E: HasArena,
{
    type Out = Term;
    type Attr = Attribute;
    type Binding = VarBinding<Str, Term>;
    type Pattern = Pattern;
    type Arm = PatternArm;
    type Err = Bottom;

    fn on_constant(
        &mut self,
        current: &Term,
        _constant: &Constant,
        _sort: &Option<Sort>,
    ) -> Result<Term, Bottom> {
        Ok(current.clone())
    }

    fn on_global(
        &mut self,
        current: &Term,
        _id: &QualifiedIdentifier,
        _sort: &Option<Sort>,
    ) -> Result<Term, Bottom> {
        Ok(current.clone())
    }

    fn on_local(&mut self, current: &Term, _id: &Local) -> Result<Term, Bottom> {
        Ok(current.clone())
    }

    fn on_app(
        &mut self,
        _current: &Term,
        id: &QualifiedIdentifier,
        _ts: &[Term],
        s: &Option<Sort>,
        recs: Vec<Self::Out>,
    ) -> Result<Term, Bottom> {
        Ok(self.arena.arena().app(id.clone(), recs, s.clone()))
    }

    fn on_let_binding(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Term>],
        _body: &Term,
        binding_idx: usize,
        binding_rec: Self::Out,
    ) -> Result<Self::Binding, Bottom> {
        let v = &vs[binding_idx];
        Ok(VarBinding(v.0.clone(), v.1, binding_rec))
    }

    fn setup_let_scope(
        &mut self,
        _current: &Term,
        _vs: &[VarBinding<Str, Term>],
        _body: &Term,
        _vs_rec: &[Self::Binding],
    ) -> Result<(), Bottom> {
        Ok(())
    }

    fn on_let(
        &mut self,
        _current: &Term,
        _vs: &[VarBinding<Str, Term>],
        _body: &Term,
        vs_rec: Vec<Self::Binding>,
        body_rec: Self::Out,
    ) -> Result<Term, Bottom> {
        Ok(self.arena.arena().let_term(vs_rec, body_rec))
    }

    fn setup_quantifier_scope(
        &mut self,
        _current: &Term,
        _vs: &[VarBinding<Str, Sort>],
        _t: &Term,
        _is_forall: bool,
    ) -> Result<(), Bottom> {
        Ok(())
    }

    fn on_exists(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Sort>],
        _t: &Term,
        t_rec: Self::Out,
    ) -> Result<Term, Bottom> {
        Ok(self.arena.arena().exists(vs.to_vec(), t_rec))
    }

    fn on_forall(
        &mut self,
        _current: &Term,
        vs: &[VarBinding<Str, Sort>],
        _t: &Term,
        t_rec: Self::Out,
    ) -> Result<Term, Bottom> {
        Ok(self.arena.arena().forall(vs.to_vec(), t_rec))
    }

    fn setup_match_case_scope(
        &mut self,
        _current: &Term,
        _scrutinee: &Term,
        cases: &[PatternArm],
        _scrutinee_rec: &Self::Out,
        case_idx: usize,
    ) -> Result<Self::Pattern, Bottom> {
        Ok(cases[case_idx].pattern.clone())
    }

    fn on_match_arm(
        &mut self,
        _current: &Term,
        _scrutinee: &Term,
        _cases: &[PatternArm],
        _scrutinee_rec: &Self::Out,
        _case_idx: usize,
        current_pattern: Self::Pattern,
        arm: Self::Out,
    ) -> Result<Self::Arm, Bottom> {
        Ok(PatternArm {
            pattern: current_pattern,
            body: arm,
        })
    }

    fn on_match(
        &mut self,
        _current: &Term,
        _scrutinee: &Term,
        _cases: &[PatternArm],
        scrutinee_rec: Self::Out,
        cases_rec: Vec<Self::Arm>,
    ) -> Result<Term, Bottom> {
        Ok(self.arena.arena().matching(scrutinee_rec, cases_rec))
    }

    fn on_annotated(
        &mut self,
        _: &Term,
        _: &Term,
        _: &[Attribute],
        r: Term,
        anns: Vec<Attribute>,
    ) -> Result<Term, Bottom> {
        Ok(self.arena.arena().annotated(r, anns))
    }

    fn on_attribute_keyword(&mut self, kw: &Keyword) -> Result<Attribute, Bottom> {
        Ok(Attribute::Keyword(kw.clone()))
    }

    fn on_attribute_constant(
        &mut self,
        kw: &Keyword,
        c: &crate::ast::alg::Constant<Str>,
    ) -> Result<Attribute, Bottom> {
        Ok(Attribute::Constant(kw.clone(), c.clone()))
    }

    fn on_attribute_symbol(&mut self, kw: &Keyword, s: &Str) -> Result<Attribute, Bottom> {
        Ok(Attribute::Symbol(kw.clone(), s.clone()))
    }

    fn on_attribute_named(&mut self, name: &Str) -> Result<Attribute, Bottom> {
        Ok(Attribute::Named(name.clone()))
    }

    fn on_attribute_pattern(&mut self, _: &[Term], recs: Vec<Term>) -> Result<Attribute, Bottom> {
        Ok(Attribute::Pattern(recs))
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
}

impl<'a, E> TypedTermRecursor for TypedBuilder<'a, E> where E: HasArena {}
