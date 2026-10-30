// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::allocator::TermAllocator;
use crate::ast::Theory;
use crate::ast::alg::VarBinding;
use crate::ast::ctx::Context;
use crate::ast::ctx::{
    Arena, CheckedApi, LetContext, Pattern, PatternArm, QuantifierContext, Sort, Str, TC, TCEnv,
    TCEnvGen, TCLocal, Term,
};
use crate::ast::ctx::{DEFAULT_DIALECT, Dialect};
use crate::containers::LocEnv;
use crate::raw::instance::HasArena;
use crate::raw::tc::matching::MatchChecker;
use crate::traits::{AllocatableString, HasMutRef};
use std::collections::HashSet;

/// A builder context for constructing `match` expressions over datatype values.
///
/// Created via [`CheckedApi::build_matching`]. The scrutinee must have a datatype sort.
///
/// Arms are added one at a time via [`build_arm`](Self::build_arm) (for constructors with
/// arguments), [`build_arm_nullary`](Self::build_arm_nullary) (for nullary constructors),
/// [`build_arm_wildcard`](Self::build_arm_wildcard) (for a named wildcard), or
/// [`build_arm_catchall`](Self::build_arm_catchall) (for `_`). Each returns an [`ArmContext`]
/// in which the pattern-bound variables are in scope; finalize each arm with
/// [`ArmContext::typed_arm`].
///
/// The context tracks constructor coverage. Once all constructors are covered (or a wildcard
/// arm is present), call [`typed_matching`](Self::typed_matching) to produce the match term.
/// It returns `Err` if coverage is incomplete. All arm bodies must have the same sort.
///
/// # Example
///
/// ```rust
/// use yaspar_ir::ast::{CheckedApi, Context, ScopedSortApi, Typecheck};
/// use yaspar_ir::untyped::UntypedAst;
///
/// let mut context = Context::new();
/// UntypedAst.parse_script_str(
///     "(set-logic ALL) \
///      (declare-datatype List (par (X) ((nil) (cons (car X) (cdr (List X)))))) \
///      (declare-const l (List Int))"
/// ).unwrap().type_check(&mut context).unwrap();
/// let l = context.typed_symbol("l").unwrap();
/// let zero = context.numeral(0u8.into()).unwrap();
/// let mut m = context.build_matching(l).unwrap();
/// // nil arm
/// let nil_arm = m.build_arm_nullary("nil").unwrap();
/// nil_arm.typed_arm(zero.clone()).unwrap();
/// // cons arm — use head element
/// let mut cons_arm = m.build_arm("cons", [Some("h"), Some("t")]).unwrap();
/// let h = cons_arm.typed_symbol("h").unwrap();
/// cons_arm.typed_arm(h).unwrap();
/// let term = m.typed_matching().unwrap();
/// assert_eq!(term.to_string(), "(match l ((nil 0) ((cons h t) h)))");
/// ```
pub struct MatchContext<'a, 'b, const D: Dialect = DEFAULT_DIALECT> {
    context: &'a mut Context<D>,
    tail: LocEnv<'b, Str, Sort>,
    scrutinee: Term,
    /// The constructors, their coverage, and the sort of the arms.
    checker: MatchChecker,
    arms: Vec<PatternArm>,
}

/// A builder context for an individual arm within a [`MatchContext`].
///
/// Created by [`MatchContext::build_arm`], [`MatchContext::build_arm_nullary`],
/// [`MatchContext::build_arm_wildcard`], or [`MatchContext::build_arm_catchall`].
///
/// Pattern-bound variables (e.g. `h` and `t` for a `cons` pattern) are in scope inside this
/// context. Build the arm body using any [`CheckedApi`] method, then finalize with
/// [`typed_arm`](Self::typed_arm), which validates that the body sort matches other arms and
/// returns control to the parent [`MatchContext`].
pub struct ArmContext<'a, 'b, 'c, const D: Dialect = DEFAULT_DIALECT> {
    parent: &'c mut MatchContext<'a, 'b, D>,
    env: Vec<VarBinding<Str, Sort>>,
    pattern: Pattern,
}

impl<'a, 'b, const D: Dialect> MatchContext<'a, 'b, D> {
    pub(crate) fn new(
        context: &'a mut Context<D>,
        tail: LocEnv<'b, Str, Sort>,
        scrutinee: Term,
    ) -> TC<Self> {
        context.check_support_theory(Theory::Datatypes)?;
        let checker = MatchChecker::new(&mut context.get_tcenv(), &scrutinee, "")?;
        Ok(Self {
            context,
            tail,
            scrutinee,
            checker,
            arms: vec![],
        })
    }

    /// Return a reference to the scrutinee
    pub fn scrutinee(&self) -> &Term {
        &self.scrutinee
    }

    /// Get the sort of the scrutinee
    pub fn scrutinee_sort(&mut self) -> Sort {
        self.checker.scrutinee_sort().clone()
    }

    /// Get the sorts of a given constructor, if it is one
    pub fn get_constructor_sorts<S>(&mut self, ctor: &S) -> Option<&[Sort]>
    where
        S: AllocatableString<Arena>,
    {
        let ctor = ctor.allocate(self.context.arena());
        self.checker.constructors().get(&ctor).map(|x| x.as_slice())
    }

    /// Get all constructors, including the unseen ones
    pub fn get_constructors(&self) -> Vec<Str> {
        self.checker.constructors().keys().cloned().collect()
    }

    /// Whether a name is a constructor
    //noinspection RsSelfConvention
    pub fn is_constructor<S>(&mut self, name: &S) -> bool
    where
        S: AllocatableString<Arena>,
    {
        self.get_constructor_sorts(name).is_some()
    }

    /// Get only the unseen constructors
    pub fn get_unseen_constructors(&self) -> &HashSet<Str> {
        self.checker.unseen()
    }

    /// Whether the current context is already covered
    pub fn is_covered(&self) -> bool {
        self.checker.is_covered()
    }

    /// Given a constructor name and a list of variables, return a builder context for the body
    /// of that arm.
    ///
    /// The list of variables must have the same length as required by the constructor.
    ///
    /// The sorts of the variables are inferred from the constructor.
    ///
    /// c.f. [Self::build_arm_wildcard], [Self::build_arm_nullary], [Self::build_arm_catchall]
    pub fn build_arm<'c, T, S>(&'c mut self, c: S, vars: T) -> TC<ArmContext<'a, 'b, 'c, D>>
    where
        T: IntoIterator<Item = Option<S>>,
        S: AllocatableString<Arena>,
    {
        let ctor = c.allocate(self.context.arena());
        let vars = vars
            .into_iter()
            .map(|v| v.map(|x| (x.allocate(self.context.arena()), x.display_meta_data())))
            .collect();
        let (pattern, env) = self.checker.ctor_arm(
            &mut self.context.get_tcenv(),
            ctor,
            &c.display_meta_data(),
            vars,
        )?;
        Ok(ArmContext {
            parent: self,
            env,
            pattern,
        })
    }

    /// Return a builder context for an arm of a nullary constructor
    ///
    /// c.f. [Self::build_arm]
    pub fn build_arm_nullary<'c, S>(&'c mut self, ctor: S) -> TC<ArmContext<'a, 'b, 'c, D>>
    where
        S: AllocatableString<Arena>,
    {
        self.build_arm(ctor, [])
    }

    /// Return a builder context for a wildcard arm
    ///
    /// The variable, if it's some, must not be the name of a constructor
    ///
    /// c.f. [Self::build_arm]
    pub fn build_arm_wildcard<'c, S>(&'c mut self, var: Option<S>) -> TC<ArmContext<'a, 'b, 'c, D>>
    where
        S: AllocatableString<Arena>,
    {
        let var = var.map(|v| (v.allocate(self.context.arena()), v.display_meta_data()));
        let (pattern, env) =
            self.checker
                .wildcard_arm(&mut self.context.get_tcenv(), var, false)?;
        Ok(ArmContext {
            parent: self,
            env,
            pattern,
        })
    }

    /// A case of `_`
    ///
    /// c.f. [Self::build_arm_wildcard] and [Self::build_arm]
    pub fn build_arm_catchall<'c>(&'c mut self) -> ArmContext<'a, 'b, 'c, D> {
        // we unwrap because we know it won't fail
        self.build_arm_wildcard::<String>(None).unwrap()
    }

    /// Build a match expression if the builder context is covered
    ///
    /// c.f. [Self::is_covered]
    pub fn typed_matching(self) -> TC<Term> {
        self.checker.finish("")?;
        Ok(self.context.matching(self.scrutinee, self.arms))
    }
}

impl<const D: Dialect> HasArena for MatchContext<'_, '_, D> {
    #[inline]
    fn arena(&mut self) -> &mut Arena {
        self.context.arena()
    }
}

impl<const D: Dialect> HasMutRef<Context<D>> for MatchContext<'_, '_, D> {
    type RefMut<'a>
        = &'a mut Context<D>
    where
        Self: 'a;

    #[inline]
    fn ref_mut(&mut self) -> Self::RefMut<'_> {
        self.context
    }
}

impl<const D: Dialect> ArmContext<'_, '_, '_, D> {
    /// finalize the arm by giving a body
    ///
    /// invoking this method will make the parent [MatchContext] available.
    pub fn typed_arm(self, body: Term) -> TC<()> {
        self.parent
            .checker
            .add_arm(self.parent.context, &self.pattern, &body, &body, "")?;
        let arm = PatternArm {
            pattern: self.pattern,
            body,
        };
        self.parent.arms.push(arm);
        Ok(())
    }
}

impl<const D: Dialect> HasArena for ArmContext<'_, '_, '_, D> {
    fn arena(&mut self) -> &mut Arena {
        self.parent.context.arena()
    }
}

impl<const D: Dialect> HasMutRef<Context<D>> for ArmContext<'_, '_, '_, D> {
    type RefMut<'a>
        = &'a mut Context<D>
    where
        Self: 'a;

    #[inline]
    fn ref_mut(&mut self) -> Self::RefMut<'_> {
        self.parent.context
    }
}

impl<const D: Dialect> CheckedApi<D> for ArmContext<'_, '_, '_, D> {
    fn get_tcenv(&mut self) -> TCEnv<'_, '_, Sort, D> {
        TCEnvGen {
            arena: &mut self.parent.context.arena,
            meta: &self.parent.context.meta,
            stack: &self.parent.context.stack,
            local: TCLocal {
                loc: LocEnv::Cons {
                    car: &self.env,
                    cdr: &self.parent.tail,
                },
                ..Default::default()
            },
        }
    }

    fn build_quantifier(&mut self) -> TC<QuantifierContext<'_, '_, D>> {
        QuantifierContext::new(
            self.parent.context,
            LocEnv::Cons {
                car: &self.env,
                cdr: &self.parent.tail,
            },
        )
    }

    fn build_let<T, S>(&mut self, bindings: T) -> TC<LetContext<'_, '_, D>>
    where
        T: IntoIterator<Item = (S, Term)>,
        S: AllocatableString<Arena>,
    {
        LetContext::new_with_bindings(
            self.parent.context,
            LocEnv::Cons {
                car: &self.env,
                cdr: &self.parent.tail,
            },
            bindings,
        )
    }

    fn build_matching(&mut self, scrutinee: Term) -> TC<MatchContext<'_, '_, D>> {
        MatchContext::new(
            self.parent.context,
            LocEnv::Cons {
                car: &self.env,
                cdr: &self.parent.tail,
            },
            scrutinee,
        )
    }
}
