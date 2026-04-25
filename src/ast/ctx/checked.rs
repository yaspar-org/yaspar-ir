// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Checked (well-formedness-preserving) APIs for building SMTLib terms, sorts, and commands.
//!
//! This module defines two core traits:
//!
//! - [`CheckedApi`]: term-building operations that validate well-formedness through the [`TC<T>`]
//!   monad (an alias for `Result<T, String>`). Every method checks scope, sort compatibility, and
//!   arity before constructing a term, returning a descriptive `Err` on failure.
//!
//! - [`ScopedSortApi`]: sort-building operations (automatically derived for any [`CheckedApi`]
//!   implementor) that validate sort existence and parameter counts.
//!
//! Both traits are implemented by [`Context`] (the global top-level environment) and by all
//! builder context types ([`QuantifierContext`], [`LetContext`], [`MatchContext`],
//! [`FunctionContext`], [`EachRecFunContext`](super::recs::EachRecFunContext),
//! [`ArmContext`](super::matching::ArmContext), and [`DefSortContext`]). This means
//! the same term-building vocabulary is available at every scope level.
//!
//! # Builder context pattern
//!
//! Scoped constructs (quantifiers, let-bindings, match expressions, function definitions) are
//! built through *builder contexts*. The typical workflow is:
//!
//! 1. Create a builder from the parent context (e.g. `context.build_quantifier()`).
//! 2. Build terms inside the builder — local bindings are in scope.
//! 3. Finalize the builder to produce the composite term or command (e.g. `q_ctx.typed_forall(body)`).
//!
//! Builder contexts borrow the parent mutably, so the parent cannot be used until the builder is
//! consumed or dropped. Builders can be nested arbitrarily.
//!
//! # Example
//!
//! ```rust
//! use yaspar_ir::ast::{CheckedApi, Context, ScopedSortApi, TC, Term};
//!
//! fn build_forall_gt(context: &mut Context) -> TC<Term> {
//!     let int = context.wf_sort("Int")?;
//!     let mut q = context.build_quantifier_with_domain([("x", int.clone()), ("y", int)])?;
//!     let x = q.typed_symbol("x")?;
//!     let y = q.typed_symbol("y")?;
//!     let body = q.typed_simp_app(">", [x, y])?;
//!     q.typed_forall(body)
//! }
//!
//! let mut context = Context::new();
//! context.ensure_logic();
//! let term = build_forall_gt(&mut context).unwrap();
//! assert_eq!(term.to_string(), "(forall ((x Int) (y Int)) (> x y))");
//! ```

use crate::allocator::{CommandAllocator, ObjectAllocatorExt, StrAllocator, TermAllocator};
use crate::ast::ctx::bindings::LetContext;
use crate::ast::ctx::ds::DefSortContext;
use crate::ast::ctx::dt::DatatypeContext;
use crate::ast::ctx::fun::FunctionContext;
use crate::ast::ctx::matching::MatchContext;
use crate::ast::ctx::quantifier::QuantifierContext;
use crate::ast::ctx::recs::RecFunsContext;
use crate::ast::utils::{is_term_bool, is_term_bool_alt};
use crate::ast::{
    ATerm, Arena, Attribute, Context, FetchSort, FunctionDef, HasArena, HasArenaAlt,
    IdentifierKind, Local, RecFunc, SymbolQuote, alg,
};
use crate::meta::WithMeta;
use crate::raw::instance::{Command, Constant, Identifier, QualifiedIdentifier, Sort, Str, Term};
use crate::raw::tc::{
    TC, TCEnv, Typecheck, sort_mismatch, tc_sort, typed_app, typed_constant, typed_distinct,
    typed_eq, typed_not, typed_qualified_identifier,
};
use crate::traits::{AllocatableString, Repr};
use dashu::integer::{IBig, Sign, UBig};
use std::collections::{HashMap, HashSet};
use yaspar::ast::Keyword;

/// The trait that represents checked APIs to construct terms.
///
/// Every method on this trait validates well-formedness before constructing a term, returning
/// `Err(message)` (via the [`TC`] monad) when an invariant is violated. This relieves callers
/// from manually maintaining sort compatibility, scope validity, and arity constraints.
///
/// `CheckedApi` is implemented by [`Context`] (the global environment) and by every builder
/// context type ([`QuantifierContext`], [`LetContext`], [`MatchContext`], [`FunctionContext`],
/// [`EachRecFunContext`](super::recs::EachRecFunContext), and
/// [`ArmContext`](super::matching::ArmContext)). This means the same set of term-building
/// functions is available at every scope level.
///
/// # Categories of methods
///
/// - **Symbols & identifiers** — [`typed_symbol`](Self::typed_symbol),
///   [`typed_symbol_with_sort`](Self::typed_symbol_with_sort),
///   [`typed_identifier`](Self::typed_identifier)
/// - **Function application** — [`typed_app`](Self::typed_app),
///   [`typed_simp_app`](Self::typed_simp_app),
///   [`typed_app_with_kind`](Self::typed_app_with_kind)
/// - **Literals** — [`numeral`](Self::numeral), [`integer`](Self::integer),
///   [`typed_constant`](Self::typed_constant)
/// - **Logical connectives** — [`typed_eq`](Self::typed_eq),
///   [`typed_distinct`](Self::typed_distinct), [`typed_and`](Self::typed_and),
///   [`typed_or`](Self::typed_or), [`typed_xor`](Self::typed_xor),
///   [`typed_not`](Self::typed_not), [`typed_implies`](Self::typed_implies),
///   [`typed_ite`](Self::typed_ite)
/// - **Builder contexts** — [`build_quantifier`](Self::build_quantifier),
///   [`build_quantifier_with_domain`](Self::build_quantifier_with_domain),
///   [`build_let`](Self::build_let), [`build_matching`](Self::build_matching)
///
/// See also [`ScopedSortApi`] for sort construction.
pub trait CheckedApi: HasArena {
    /// Obtain a type-checking environment
    ///
    /// This is used internally to implement other functions
    fn get_tcenv(&mut self) -> TCEnv<'_, '_, Sort>;

    /// Enter a builder context that builds a quantifier
    ///
    /// Invoke [QuantifierContext::typed_forall] or [QuantifierContext::typed_exists] to build a
    /// quantified term
    ///
    /// c.f. [Self::build_quantifier_with_domain]
    fn build_quantifier(&mut self) -> TC<QuantifierContext<'_, '_>>;

    /// Enter a context for building a let binding
    ///
    /// The binders must be provided at time of creating the builder context, because the bound
    /// terms can only be well-formed in the parent context.
    ///
    /// It is a scope-level mistake to bind a term only bound in the let context.
    ///
    /// Invoke [`LetContext::typed_let`] to finalize the let binding
    fn build_let<T, S>(&mut self, bindings: T) -> TC<LetContext<'_, '_>>
    where
        T: IntoIterator<Item = (S, Term)>,
        S: AllocatableString<Arena>;

    /// Enter a context for building a match expression
    ///
    /// Invoke [MatchContext::build_arm] for building an arm for a constructor, provided an exact number
    /// of variables, or [MatchContext::build_arm_wildcard] for building a wildcard arm.
    ///
    /// Invoke [MatchContext::typed_matching] to conclude the term of matching
    fn build_matching(&mut self, scrutinee: Term) -> TC<MatchContext<'_, '_>>;

    /// Build a typed [`Term`] from a [`Constant`] value.
    fn typed_constant(&mut self, c: Constant) -> TC<Term> {
        typed_constant(&mut self.get_tcenv(), c)
    }

    /// Build a numeral literal [`Term`] from a [`UBig`].
    fn numeral(&mut self, n: UBig) -> TC<Term> {
        self.typed_constant(Constant::Numeral(n))
    }

    /// Returns an integer as a term.
    ///
    /// It is possible that this function returns an [`Err`] when neither
    /// `Int` nor `Real` is supported.
    fn integer(&mut self, i: IBig) -> TC<Term> {
        let (s, n) = i.into_parts();
        let num = self.numeral(n)?;
        match s {
            Sign::Negative => self.typed_simp_app("-", vec![num]),
            _ => Ok(num),
        }
    }

    /// Return a typed identifier, if it is well-typed.
    fn typed_identifier(&mut self, identifier: QualifiedIdentifier) -> TC<Term> {
        let sort = identifier.1.clone();
        typed_qualified_identifier(&mut self.get_tcenv(), identifier, sort, "")
    }

    /// Return a typed representation of the symbol `name`, if `name` is a valid symbol.
    fn typed_symbol<S>(&mut self, name: S) -> TC<Term>
    where
        S: AllocatableString<Arena>,
    {
        let symb = name.allocate(self.arena());
        self.typed_identifier(QualifiedIdentifier::simple(symb))
    }

    /// Return a representation of a local variable with the name `name`, if exists.
    fn typed_local<S>(&mut self, name: S) -> TC<Local>
    where
        S: AllocatableString<Arena>,
    {
        match self.typed_symbol(name)?.repr() {
            ATerm::Local(loc) => Ok(loc.clone()),
            t => Err(format!("TC: symbol `{}` is not a local term", t)),
        }
    }

    /// Return a typed representation of the symbol `name` with a specific `sort`, if `name` is a
    /// valid symbol.
    fn typed_symbol_with_sort<S>(&mut self, name: S, sort: Sort) -> TC<Term>
    where
        S: AllocatableString<Arena>,
    {
        let symb = name.allocate(self.arena());
        typed_qualified_identifier(
            &mut self.get_tcenv(),
            QualifiedIdentifier::simple(symb),
            Some(sort),
            "",
        )
    }

    /// This function returns a typed term by applying `f` to `args`, if the resulting application
    /// type checks. It is more convenient than [`TermAllocator::app`] as it ensures the end term must
    /// be well-formed.
    fn typed_app<T>(&mut self, f: QualifiedIdentifier, args: T) -> TC<Term>
    where
        T: IntoIterator<Item = Term>,
    {
        typed_app(
            &mut self.get_tcenv(),
            f,
            args.into_iter().map(WithMeta::empty_meta).collect(),
            None,
            "",
            "",
        )
    }

    /// Similar to [Self::typed_app] but allow a string as the function name
    fn typed_simp_app<S, T>(&mut self, f: S, args: T) -> TC<Term>
    where
        S: AllocatableString<Arena>,
        T: IntoIterator<Item = Term>,
    {
        let f_symbol = f.allocate(self.arena());
        self.typed_app(QualifiedIdentifier::simple(f_symbol), args)
    }

    /// Convert an [IdentifierKind] to an [Identifier]
    fn kind_to_identifier(&mut self, kind: IdentifierKind) -> Identifier {
        let symbol = self.arena().allocate_symbol(kind.name());
        Identifier {
            symbol,
            indices: kind.indices(),
        }
    }

    /// Similar to [Self::typed_app], but use [IdentifierKind] as the function instead. This is
    /// useful for builtin functions.
    fn typed_app_with_kind<T>(&mut self, f: IdentifierKind, args: T) -> TC<Term>
    where
        T: IntoIterator<Item = Term>,
    {
        let id = self.kind_to_identifier(f);
        self.typed_app(id.into(), args)
    }

    /// Checked API for building equality (`= a b`). Both arguments must have the same [`Sort`].
    fn typed_eq(&mut self, a: Term, b: Term) -> TC<Term> {
        typed_eq(&mut self.get_tcenv(), a, b, "")
    }

    /// Checked API for building `(distinct ...)`. At least two arguments of the same [`Sort`] required.
    fn typed_distinct<T>(&mut self, ts: T) -> TC<Term>
    where
        T: IntoIterator<Item = Term>,
    {
        typed_distinct(
            &mut self.get_tcenv(),
            ts.into_iter().map(WithMeta::empty_meta).collect(),
        )
    }

    /// Checked API for building `(and ...)`. All arguments must be `Bool`-sorted [`Term`]s.
    fn typed_and<T>(&mut self, terms: T) -> TC<Term>
    where
        T: IntoIterator<Item = Term>,
    {
        let mut env = self.get_tcenv();
        let terms = check_all_bool_terms(terms, &mut env)?;
        if terms.is_empty() {
            return Err("TC: 'and' requires at least one argument!".into());
        }
        Ok(env.arena_alt().and(terms))
    }

    /// Checked API for building `(or ...)`. All arguments must be `Bool`-sorted [`Term`]s.
    fn typed_or<T>(&mut self, terms: T) -> TC<Term>
    where
        T: IntoIterator<Item = Term>,
    {
        let mut env = self.get_tcenv();
        let terms = check_all_bool_terms(terms, &mut env)?;
        if terms.is_empty() {
            return Err("TC: 'or' requires at least one argument!".into());
        }
        Ok(env.arena_alt().or(terms))
    }

    /// Checked API for building `(xor ...)`. All arguments must be `Bool`-sorted [`Term`]s.
    fn typed_xor<T>(&mut self, terms: T) -> TC<Term>
    where
        T: IntoIterator<Item = Term>,
    {
        let mut env = self.get_tcenv();
        let terms = check_all_bool_terms(terms, &mut env)?;
        if terms.len() < 2 {
            return Err("TC: 'xor' requires at least two arguments!".into());
        }
        Ok(env.arena_alt().xor(terms))
    }

    /// Checked API for building `(not t)`. The argument must be a `Bool`-sorted [`Term`].
    fn typed_not(&mut self, t: Term) -> TC<Term> {
        typed_not(&mut self.get_tcenv(), t, "")
    }

    /// Checked API for building `(=> p1 p2 ... concl)`. All arguments must be `Bool`-sorted [`Term`]s.
    fn typed_implies<T>(&mut self, premises: T, concl: Term) -> TC<Term>
    where
        T: IntoIterator<Item = Term>,
    {
        let mut env = self.get_tcenv();
        let premises = check_all_bool_terms(premises, &mut env)?;
        is_term_bool_alt(&mut env, &concl, "")?;
        Ok(env.arena_alt().implies(premises, concl))
    }

    /// Checked API for building `(ite c t e)`. Condition must be `Bool`; branches must have the same [`Sort`].
    fn typed_ite(&mut self, condition: Term, then: Term, els: Term) -> TC<Term> {
        let mut env = self.get_tcenv();
        is_term_bool_alt(&mut env, &condition, "")?;
        let then_sort = then.get_sort(&mut env);
        let else_sort = els.get_sort(&mut env);
        if then_sort != else_sort {
            return sort_mismatch(&then_sort, &else_sort, els, "");
        }
        Ok(env.arena_alt().ite(condition, then, els))
    }

    /// Create a builder context for a quantifier with a given domain
    ///
    /// c.f. [Self::build_quantifier]
    fn build_quantifier_with_domain<T, S>(&mut self, domain: T) -> TC<QuantifierContext<'_, '_>>
    where
        T: IntoIterator<Item = (S, Sort)>,
        S: AllocatableString<Arena>,
    {
        let mut context = self.build_quantifier()?;
        context.extend_many(domain)?;
        Ok(context)
    }
}

fn check_all_bool_terms<T, E>(terms: T, e: &mut E) -> TC<Vec<Term>>
where
    T: IntoIterator<Item = Term>,
    E: HasArenaAlt,
{
    let mut results = vec![];
    for t in terms {
        is_term_bool_alt(e, &t, "")?;
        results.push(t);
    }
    Ok(results)
}

/// The trait that represents checked APIs to construct sorts.
///
/// This trait provides well-formedness-checked sort construction. It validates that the sort
/// exists in the current logic, has the correct number of parameters, and that bitvector
/// lengths are within bounds.
///
/// `ScopedSortApi` is automatically implemented for any type that implements [`CheckedApi`]
/// (plus the required allocator traits), so all builder contexts inherit these methods.
///
/// # Methods
///
/// - [`wf_sort(name)`](Self::wf_sort) — look up a sort by name (e.g. `"Int"`, `"Bool"`, a user-defined sort).
/// - [`wf_sort_n(name, params)`](Self::wf_sort_n) — parameterized sort (e.g. `wf_sort_n("List", [int])` for `(List Int)`).
/// - [`wf_sort_id(id, params)`](Self::wf_sort_id) — sort from an [`Identifier`] and parameters.
/// - [`wf_bv_sort(len)`](Self::wf_bv_sort) — bitvector sort `(_ BitVec len)`. Validates length > 0 and within bounds.
///
/// See also [`CheckedApi`] for term construction.
pub trait ScopedSortApi: HasArena {
    /// Obtain a type-checking environment
    ///
    /// This is used internally to implement other functions
    fn get_sort_tcenv(&mut self) -> TCEnv<'_, '_, ()>;

    /// Return a well-formed sort given an identifier and parameters
    fn wf_sort_id<T>(&mut self, id: &Identifier, params: T) -> TC<Sort>
    where
        T: IntoIterator<Item = Sort>,
    {
        let mut env = self.get_sort_tcenv();
        tc_sort(&mut env, id, params)
    }

    /// Return a well-formed sort given a name and parameters
    fn wf_sort_n<S, T>(&mut self, name: S, params: T) -> TC<Sort>
    where
        S: AllocatableString<Arena>,
        T: IntoIterator<Item = Sort>,
    {
        let sym = name.allocate(self.arena());
        self.wf_sort_id(&Identifier::simple(sym), params)
    }

    /// Return a well-formed sort with a given name
    fn wf_sort<S>(&mut self, name: S) -> TC<Sort>
    where
        S: AllocatableString<Arena>,
    {
        self.wf_sort_n(name, [])
    }

    /// Return a well-formed bit vector sort
    fn wf_bv_sort(&mut self, len: UBig) -> TC<Sort> {
        let mut env = self.get_sort_tcenv();
        let sort = env.arena_alt().bv_sort(len);
        sort.type_check(&mut env)
    }
}

impl<X> ScopedSortApi for X
where
    X: StrAllocator<Str = Str> + TermAllocator<Str, Sort, Term> + CheckedApi,
{
    fn get_sort_tcenv(&mut self) -> TCEnv<'_, '_, ()> {
        self.get_tcenv().convert_to_empty_local()
    }
}

impl Context {
    /// Create a context for building `define-fun` with a given output sort
    ///
    /// c.f. [Self::build_fun]
    pub fn build_fun_out_sort<T, S>(
        &mut self,
        name: S,
        inputs: T,
        output: Sort,
    ) -> TC<FunctionContext<'_>>
    where
        T: IntoIterator<Item = (S, Sort)>,
        S: AllocatableString<Arena>,
    {
        FunctionContext::new(self, name, inputs, Some(output))
    }

    /// Create a context for building `define-fun` without a given output sort
    ///
    /// c.f. [Self::build_fun_out_sort]
    pub fn build_fun<T, S>(&mut self, name: S, inputs: T) -> TC<FunctionContext<'_>>
    where
        T: IntoIterator<Item = (S, Sort)>,
        S: AllocatableString<Arena>,
    {
        FunctionContext::new(self, name, inputs, None)
    }

    /// Create a context for building [`define-fun-rec`](RecFunsContext) and `define-fun-recs`
    pub fn build_rec_funs<T, S>(&mut self, funs: T) -> TC<RecFunsContext<'_>>
    where
        T: IntoIterator<Item = RecFunc<S, Sort>>,
        S: AllocatableString<Arena>,
    {
        RecFunsContext::new(self, funs)
    }

    /// Create a context for defining a sort, i.e. [`define-sort`](DefSortContext)
    pub fn build_sort_alias<S>(
        &mut self,
        name: S,
        params: impl IntoIterator<Item = S>,
    ) -> TC<DefSortContext<'_>>
    where
        S: AllocatableString<Arena>,
    {
        DefSortContext::new(self, name, params)
    }

    /// Create a context for building datatypes
    ///
    /// Use [Self::typed_enum] to build simple enum datatypes
    pub fn build_datatypes<T, P, S>(&mut self, dt_names_and_sorts: T) -> TC<DatatypeContext<'_>>
    where
        T: IntoIterator<Item = (S, P)>,
        P: IntoIterator<Item = S>,
        S: AllocatableString<Arena>,
    {
        DatatypeContext::new(self, dt_names_and_sorts)
    }

    /// A simpler API to build a simple enum datatype with simple cases.
    ///
    /// Use [Self::build_datatypes] for building more complex datatypes
    pub fn typed_enum<S>(&mut self, dt_name: S, cases: impl IntoIterator<Item = S>) -> TC<Command>
    where
        S: AllocatableString<Arena>,
    {
        let dt_name = dt_name.allocate(self.arena());
        let mut dt_ctx = self.build_datatypes([(dt_name.clone(), [])])?;
        let mut d_ctx = dt_ctx.build_datatype(dt_name)?;
        for case in cases {
            d_ctx.build_datatype_constructor_nullary(case)?;
        }
        d_ctx.typed_datatype()?;
        dt_ctx.typed_declare_datatypes()
    }

    /// Handle top-level named annotations in assertions
    fn scan_named(&mut self, t: &Term, acc: &mut HashMap<Str, Term>) -> TC<()> {
        if let ATerm::Annotated(t, annos) = t.repr() {
            for anno in annos {
                if let Attribute::Named(name) = anno {
                    if self.can_add_symbol(name).is_ok() && !acc.contains_key(name) {
                        acc.insert(name.clone(), t.clone());
                    } else {
                        return Err(format!(
                            "TC: named annotation {} cannot be added to the symbol table!",
                            name.sym_quote()
                        ));
                    }
                }
            }
            self.scan_named(t, acc)
        } else {
            Ok(())
        }
    }

    /// Checked API for building an assertion [`Command`]
    pub fn typed_assert(&mut self, t: Term) -> TC<Command> {
        self.check_logic()?;
        is_term_bool(self, &t)?;
        let mut acc = HashMap::new();
        self.scan_named(&t, &mut acc)?;
        for (n, t) in acc {
            // add below should always work
            let s = t.get_sort(self);
            self.insert_symbol_with_def(
                HashSet::new(),
                FunctionDef {
                    name: n,
                    sort_params: vec![],
                    vars: vec![],
                    out_sort: s,
                    body: t,
                },
            );
        }
        Ok(self.assert(t))
    }

    /// Checked API for building a [`set-option`](Command) command
    pub fn typed_set_option<S, T>(&mut self, opt: &alg::Attribute<S, T>) -> TC<Command>
    where
        alg::Attribute<S, T>: Typecheck<Self, Out = Attribute>,
    {
        let opt = opt.type_check(self)?;
        match &opt {
            Attribute::Keyword(_) => {}
            Attribute::Constant(kw, c) => match kw {
                Keyword::DiagnosticOutputChannel | Keyword::RegularOutputChannel
                    if !matches!(c, alg::Constant::String(_)) =>
                {
                    return Err(format!("TC: keyword {kw} expected a string!"));
                }
                Keyword::GlobalDeclarations
                | Keyword::InteractiveMode
                | Keyword::PrintSuccess
                | Keyword::ProduceAssertions
                | Keyword::ProduceAssignments
                | Keyword::ProduceModels
                | Keyword::ProduceProofs
                | Keyword::ProduceUnsatAssumptions
                | Keyword::ProduceUnsatCores
                    if !matches!(c, alg::Constant::Bool(_)) =>
                {
                    return Err(format!("TC: keyword {kw} expected a bool!"));
                }
                Keyword::RandomSeed | Keyword::ReproducibleResourceLimit | Keyword::Verbosity
                    if !matches!(c, alg::Constant::Numeral(_)) =>
                {
                    return Err(format!("TC: keyword {kw} expected a number!"));
                }
                _ => {}
            },
            _ => {}
        }
        Ok(self.set_option(opt))
    }

    /// Makes sure assumptions are boolean.
    ///
    /// Returns a [`check-sat-assuming`](Command) command.
    pub fn typed_check_sat_assuming(
        &mut self,
        assumptions: impl IntoIterator<Item = Term>,
    ) -> TC<Command> {
        let mut ts = vec![];
        for assumption in assumptions {
            is_term_bool(self, &assumption)?;
            ts.push(assumption);
        }
        Ok(self.check_sat_assuming(ts))
    }

    /// Return a typed [`Command`] for `define-const`
    ///
    /// c.f. [`Self::typed_define_const_sorted`]
    pub fn typed_define_const<S>(&mut self, name: S, body: Term) -> TC<Command>
    where
        S: AllocatableString<Arena>,
    {
        let name = name.allocate(self.arena());
        let sort = body.get_sort(self);
        let def = FunctionDef {
            name: name.clone(),
            sort_params: vec![],
            vars: vec![],
            out_sort: sort.clone(),
            body: body.clone(),
        };
        self.def_symbol(def)?;
        Ok(self.define_const(name, sort, body))
    }

    /// Return a typed [`Command`] for `define-const` with an explicit sort
    ///
    /// c.f. [`Self::typed_define_const`]
    pub fn typed_define_const_sorted<S>(&mut self, name: S, s: Sort, body: Term) -> TC<Command>
    where
        S: AllocatableString<Arena>,
    {
        let name = name.allocate(self.arena());
        let sort = body.get_sort(self);
        if sort != s {
            return Err(format!(
                "TC: const {} is declared to have sort {s} but is checked to have sort {sort}!",
                name.sym_quote(),
            ));
        }
        let def = FunctionDef {
            name: name.clone(),
            sort_params: vec![],
            vars: vec![],
            out_sort: sort.clone(),
            body: body.clone(),
        };
        self.def_symbol(def)?;
        Ok(self.define_const(name, sort, body))
    }
}
