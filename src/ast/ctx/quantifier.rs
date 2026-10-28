// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::allocator::TermAllocator;
use crate::ast::alg::VarBinding;
use crate::ast::ctx::bindings::LetContext;
use crate::ast::ctx::local::LocalContext;
use crate::ast::ctx::{Arena, CheckedApi, Context, Result, Sort, Str, TCEnv, Term};
use crate::ast::utils::is_term_bool;
use crate::ast::{Attribute, MatchContext, Theory};
use crate::containers::LocEnv;
use crate::raw::instance::HasArena;
use crate::raw::tc::TC;
use crate::traits::{AllocatableString, HasMutRef};

/// A builder context for constructing quantified terms (`forall` and `exists`).
///
/// Created via [`CheckedApi::build_quantifier`] or [`CheckedApi::build_quantifier_with_domain`].
/// Variables are introduced into scope either at creation time (with `build_quantifier_with_domain`)
/// or incrementally via [`extend`](Self::extend) / [`extend_many`](Self::extend_many).
///
/// Once the body is built, finalize with [`typed_forall`](Self::typed_forall) or
/// [`typed_exists`](Self::typed_exists), both of which consume the context and return the
/// quantified term. The body must be `Bool`-sorted. To give the quantifier patterns, finalize with
/// [`typed_forall_with_patterns`](Self::typed_forall_with_patterns) or
/// [`typed_exists_with_patterns`](Self::typed_exists_with_patterns) instead.
///
/// This context implements [`CheckedApi`], so all term-building methods are available inside it,
/// and nested builder contexts (let-bindings, inner quantifiers, match expressions) can be created.
///
/// # Example
///
/// ```rust
/// use yaspar_ir::ast::{CheckedApi, Context, ScopedSortApi};
///
/// let mut context = Context::new();
/// context.ensure_logic();
/// let int = context.wf_sort("Int").unwrap();
/// let mut q = context.build_quantifier_with_domain([("x", int)]).unwrap();
/// let x = q.typed_symbol("x").unwrap();
/// let zero = q.numeral(0u8.into()).unwrap();
/// let body = q.typed_simp_app(">", [x, zero]).unwrap();
/// let term = q.typed_forall(body).unwrap();
/// assert_eq!(term.to_string(), "(forall ((x Int)) (> x 0))");
/// ```
pub struct QuantifierContext<'a, 'b>(pub(crate) LocalContext<'a, 'b>);

impl<'a, 'b> QuantifierContext<'a, 'b> {
    pub(crate) fn new(context: &'a mut Context, tail: LocEnv<'b, Str, Sort>) -> TC<Self> {
        context.check_support_theory(Theory::Quantifiers)?;
        Ok(Self(LocalContext::new(context, tail)))
    }

    /// Extends a name-sort binding to the local environment
    pub fn extend<S>(&mut self, name: S, sort: Sort) -> Result<&mut Self>
    where
        S: AllocatableString<Arena>,
    {
        self.0.extend(name, sort)?;
        Ok(self)
    }

    /// Extends a vector of name-osrt bindings
    pub fn extend_many<T, S>(&mut self, tups: T) -> Result<&mut Self>
    where
        T: IntoIterator<Item = (S, Sort)>,
        S: AllocatableString<Arena>,
    {
        self.0.extend_many(tups)?;
        Ok(self)
    }

    /// Return the variable bindings introduced directly by this quantifier scope.
    pub fn get_direct_bindings(&self) -> &[VarBinding<Str, Sort>] {
        self.0.get_direct_bindings()
    }

    /// Build a forall
    ///
    /// Body is a term built in `self` context
    pub fn typed_forall(mut self, body: Term) -> TC<Term> {
        is_term_bool(&mut self, &body)?;
        Ok(self.0.context.forall(self.0.env, body))
    }

    /// Build an exists
    ///
    /// Body is a term built in `self` context
    pub fn typed_exists(mut self, body: Term) -> TC<Term> {
        is_term_bool(&mut self, &body)?;
        Ok(self.0.context.exists(self.0.env, body))
    }

    /// Build a forall whose body carries the given patterns, i.e.
    /// `(forall (…) (! body :pattern (p₁ …) :pattern (q₁ …) …))`.
    ///
    /// Body and patterns are terms built in `self` context. Each pattern is a multi-pattern, and
    /// must not be empty. With no patterns at all, this is [`typed_forall`](Self::typed_forall).
    pub fn typed_forall_with_patterns(mut self, body: Term, patterns: Vec<Vec<Term>>) -> TC<Term> {
        let body = self.annotate_with_patterns(body, patterns)?;
        self.typed_forall(body)
    }

    /// Build an exists whose body carries the given patterns, i.e.
    /// `(exists (…) (! body :pattern (p₁ …) :pattern (q₁ …) …))`.
    ///
    /// Body and patterns are terms built in `self` context. Each pattern is a multi-pattern, and
    /// must not be empty. With no patterns at all, this is [`typed_exists`](Self::typed_exists).
    pub fn typed_exists_with_patterns(mut self, body: Term, patterns: Vec<Vec<Term>>) -> TC<Term> {
        let body = self.annotate_with_patterns(body, patterns)?;
        self.typed_exists(body)
    }

    /// Put `patterns` on `body`, the one position a pattern may annotate (§3.6.5).
    fn annotate_with_patterns(&mut self, body: Term, patterns: Vec<Vec<Term>>) -> TC<Term> {
        is_term_bool(self, &body)?;
        if patterns.is_empty() {
            return Ok(body);
        }
        if patterns.iter().any(|p| p.is_empty()) {
            return Err("TC: a :pattern must contain at least one term!".into());
        }
        let anns = patterns.into_iter().map(Attribute::Pattern).collect();
        Ok(self.0.context.annotated(body, anns))
    }
}

impl HasArena for QuantifierContext<'_, '_> {
    #[inline]
    fn arena(&mut self) -> &mut Arena {
        self.0.arena()
    }
}

impl HasMutRef<Context> for QuantifierContext<'_, '_> {
    type RefMut<'a>
        = &'a mut Context
    where
        Self: 'a;

    #[inline]
    fn ref_mut(&mut self) -> Self::RefMut<'_> {
        self.0.context
    }
}

impl CheckedApi for QuantifierContext<'_, '_> {
    fn get_tcenv(&mut self) -> TCEnv<'_, '_, Sort> {
        self.0.get_tcenv()
    }

    fn build_quantifier(&mut self) -> TC<QuantifierContext<'_, '_>> {
        self.0.build_quantifier()
    }

    fn build_let<T, S>(&mut self, bindings: T) -> TC<LetContext<'_, '_>>
    where
        T: IntoIterator<Item = (S, Term)>,
        S: AllocatableString<Arena>,
    {
        self.0.build_let(bindings)
    }

    fn build_matching(&mut self, scrutinee: Term) -> TC<MatchContext<'_, '_>> {
        self.0.build_matching(scrutinee)
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{CheckedApi, Context, ScopedSortApi, Term, Typecheck};
    use crate::untyped::UntypedAst;

    fn context() -> Context {
        let mut context = Context::new();
        let decls = "(set-logic ALL)(declare-fun p (Int) Bool)(declare-fun f (Int) Int)";
        let cmds = UntypedAst.parse_script_str(decls).unwrap();
        cmds.type_check(&mut context).unwrap();
        context
    }

    /// `(p x)`, `(f x)` and `(p (f x))`, built in a quantifier over `x : Int`, and finalized by
    /// `finish` with the patterns `[[(p x)], [(f x), (p (f x))]]`.
    fn build(
        context: &mut Context,
        finish: impl FnOnce(super::QuantifierContext, Term, Vec<Vec<Term>>) -> crate::raw::tc::TC<Term>,
    ) -> crate::raw::tc::TC<Term> {
        let int = context.wf_sort("Int").unwrap();
        let mut q = context.build_quantifier_with_domain([("x", int)]).unwrap();
        let x = q.typed_symbol("x").unwrap();
        let px = q.typed_simp_app("p", [x.clone()]).unwrap();
        let fx = q.typed_simp_app("f", [x]).unwrap();
        let pfx = q.typed_simp_app("p", [fx.clone()]).unwrap();
        finish(q, px.clone(), vec![vec![px], vec![fx, pfx]])
    }

    #[test]
    fn patterns_go_on_the_body() {
        let mut context = context();
        let t = build(&mut context, |q, body, ps| {
            q.typed_forall_with_patterns(body, ps)
        })
        .unwrap();
        assert_eq!(
            t.to_string(),
            "(forall ((x Int)) (! (p x) :pattern ((p x)) :pattern ((f x) (p (f x)))))"
        );
        // and that is where the type checker accepts them
        assert!(t.type_check(&mut context).is_ok());

        let t = build(&mut context, |q, body, ps| {
            q.typed_exists_with_patterns(body, ps)
        })
        .unwrap();
        assert_eq!(
            t.to_string(),
            "(exists ((x Int)) (! (p x) :pattern ((p x)) :pattern ((f x) (p (f x)))))"
        );
        assert!(t.type_check(&mut context).is_ok());
    }

    #[test]
    fn no_patterns_is_a_plain_quantifier() {
        let mut context = context();
        let t = build(&mut context, |q, body, _| {
            q.typed_forall_with_patterns(body, vec![])
        })
        .unwrap();
        assert_eq!(t.to_string(), "(forall ((x Int)) (p x))");
    }

    #[test]
    fn an_empty_multi_pattern_is_rejected() {
        let mut context = context();
        let r = build(&mut context, |q, body, mut ps| {
            ps.push(vec![]);
            q.typed_forall_with_patterns(body, ps)
        });
        assert!(r.is_err_and(|e| e.contains(":pattern")));
    }

    #[test]
    fn the_body_must_be_bool() {
        let mut context = context();
        let r = build(&mut context, |q, _, mut ps| {
            let fx = ps[1].remove(0);
            q.typed_forall_with_patterns(fx, ps)
        });
        assert!(r.is_err());
    }
}
