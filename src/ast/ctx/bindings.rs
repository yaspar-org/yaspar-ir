// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::allocator::TermAllocator;
use crate::ast::alg::VarBinding;
use crate::ast::ctx::local::LocalContext;
use crate::ast::ctx::{Arena, CheckedApi, Context, FetchSort, Result, TCEnv};
use crate::ast::ctx::{Sort, Str, Term};
use crate::ast::{MatchContext, QuantifierContext, TC};
use crate::containers::LocEnv;
use crate::raw::instance::HasArena;
use crate::traits::AllocatableString;

/// A builder context for constructing `let` binding terms.
///
/// Created via [`CheckedApi::build_let`]. The bindings (name–term pairs) must be provided at
/// creation time because the bound terms are well-formed only in the *parent* scope — it would
/// be a scope-level error to bind a term that references variables introduced by this very let.
///
/// After creation, the bound names are available as local variables inside this context. Build
/// the body term using any [`CheckedApi`] method, then finalize with [`typed_let`](Self::typed_let),
/// which consumes the context and returns the `let` term.
///
/// Note: `typed_let` always succeeds (returns `Term`, not `TC<Term>`) because the bindings were
/// already validated at context creation.
///
/// # Example
///
/// ```rust
/// use yaspar_ir::ast::{CheckedApi, Context, Typecheck};
/// use yaspar_ir::untyped::UntypedAst;
///
/// let mut context = Context::new();
/// UntypedAst.parse_script_str("(set-logic ALL) (declare-const a Int) (declare-const b Int)")
///     .unwrap().type_check(&mut context).unwrap();
/// let a = context.typed_symbol("a").unwrap();
/// let b = context.typed_symbol("b").unwrap();
/// let sum = context.typed_simp_app("+", [a, b]).unwrap();
/// let mut l = context.build_let([("s", sum)]).unwrap();
/// let s = l.typed_symbol("s").unwrap();
/// let body = l.typed_simp_app("*", [s.clone(), s]).unwrap();
/// let term = l.typed_let(body);
/// assert_eq!(term.to_string(), "(let ((s (+ a b))) (* s s))");
/// ```
pub struct LetContext<'a, 'b> {
    // reuse LocalContext to reuse apis
    inner: LocalContext<'a, 'b>,
    bindings: Vec<VarBinding<Str, Term>>,
}

impl<'a, 'b> LetContext<'a, 'b> {
    pub(crate) fn new(context: &'a mut Context, tail: LocEnv<'b, Str, Sort>) -> Self {
        Self {
            inner: LocalContext::new(context, tail),
            bindings: vec![],
        }
    }

    pub(crate) fn new_with_bindings<T, S>(
        context: &'a mut Context,
        tail: LocEnv<'b, Str, Sort>,
        tups: T,
    ) -> Result<Self>
    where
        T: IntoIterator<Item = (S, Term)>,
        S: AllocatableString<Arena>,
    {
        let mut ctx = Self::new(context, tail);
        ctx.extend_many(tups)?;
        Ok(ctx)
    }

    /// This function is intended to be private to ensure well-scopedness
    fn extend_many<T, S>(&mut self, tups: T) -> Result<&mut Self>
    where
        T: IntoIterator<Item = (S, Term)>,
        S: AllocatableString<Arena>,
    {
        let mut names = vec![];
        let mut terms = vec![];
        let mut sorts = vec![];
        for (name, term) in tups {
            let name = name.allocate(self.arena());
            names.push(name);
            let s = term.get_sort(self);
            sorts.push(s);
            terms.push(term);
        }
        let ids = self
            .inner
            .extend_many(names.clone().into_iter().zip(sorts))?;
        for (name, (id, term)) in names.into_iter().zip(ids.into_iter().zip(terms)) {
            self.bindings.push(VarBinding(name, id, term));
        }
        Ok(self)
    }

    /// Consume the given context and produce a term of a let binding
    pub fn typed_let(mut self, body: Term) -> Term {
        self.inner.let_term(self.bindings, body)
    }
}

impl HasArena for LetContext<'_, '_> {
    #[inline]
    fn arena(&mut self) -> &mut Arena {
        self.inner.arena()
    }
}

impl CheckedApi for LetContext<'_, '_> {
    #[inline]
    fn get_tcenv(&mut self) -> TCEnv<'_, '_, Sort> {
        self.inner.get_tcenv()
    }

    #[inline]
    fn build_quantifier(&mut self) -> TC<QuantifierContext<'_, '_>> {
        self.inner.build_quantifier()
    }

    fn build_let<T, S>(&mut self, bindings: T) -> TC<LetContext<'_, '_>>
    where
        T: IntoIterator<Item = (S, Term)>,
        S: AllocatableString<Arena>,
    {
        self.inner.build_let(bindings)
    }

    fn build_matching(&mut self, scrutinee: Term) -> TC<MatchContext<'_, '_>> {
        self.inner.build_matching(scrutinee)
    }
}
