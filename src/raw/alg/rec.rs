// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Stack-safe recursion over [`Term`] trees using a Vec-based traversal stack.
//!
//! Deeply nested terms can overflow the call stack when traversed with ordinary recursion.
//! This module provides [`TermRecursor`], a visitor-style trait whose default method
//! [`recurse_on_term`](TermRecursor::recurse_on_term) drives an iterative traversal
//! using a `Vec<Frame>` as an explicit stack.
//!
//! # How it works
//!
//! The traversal is a standard left-to-right, depth-first walk:
//!
//! 1. **Expand & Resolve** – [`expand_and_resolve`] descends from a term into its
//!    leftmost leaf, pushing a [`Frame`] for every intermediate node onto the stack
//!    `Vec`. It loops over [`expand_and_resolve_once`], which either pushes a frame
//!    and returns the next child to descend into, or directly resolves a leaf by
//!    calling the appropriate leaf callback (`on_constant`, `on_global`, or
//!    `on_local`) to produce a result.
//!
//! 2. **Push** – [`push_result`] propagates a result upward through the stack. At each
//!    frame it either:
//!    - accumulates the result and returns so the next child can be expanded, or
//!    - invokes the `on_*` callback when all children are ready and continues upward.
//!
//! 3. **Next** – [`next_child`] peeks at the top frame to determine the next child term
//!    to expand. For scoped constructs (`Let`, `Quantifier`, `Match`) it also invokes
//!    the appropriate `setup_*` callback.
//!
//! The main loop in [`term_recursion`] alternates between these phases until the stack
//! is empty, at which point the final result is returned.

use crate::ast::Repr;
use crate::raw::alg::*;
use either::Either;

/// Use this type as the `Err` type in [TermRecursor] if no error is expected.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Bottom {}

/// A trait witnessing that a type is uninhabited (isomorphic to [`Bottom`]).
///
/// This is used as a bound on [`TermRecursor::recurse_on_term_no_err`] to statically
/// guarantee that the recursor cannot fail, allowing the result to be unwrapped safely.
pub trait IsBottom {
    /// Convert `self` into [`Bottom`]. Since both types are uninhabited, this is
    /// a vacuously true identity — it can never actually be called at runtime.
    fn bottom(self) -> Bottom;
}

impl IsBottom for Bottom {
    fn bottom(self) -> Bottom {
        self
    }
}

/// A visitor trait for performing stack-safe, bottom-up recursion over [`Term`] trees.
///
/// Implementors define one callback per `Term` variant. Leaf callbacks (`on_constant`,
/// `on_global`, `on_local`) receive only the original node data. Compound callbacks
/// additionally receive the already-computed recursive results for their children.
///
/// Every callback receives a `current: &T` parameter as its first argument (after `&mut self`).
/// This is a reference to the original term node being recursed on — i.e. the `T` whose
/// internal representation was destructured to produce the other arguments. For example,
/// in `on_app(current, id, ts, s, recs)`, `current` is the `T` that wraps the
/// `Term::App(id, ts, s)` variant. This allows callbacks to inspect the original node
/// (e.g. for hash-consing identity, location information, or metadata).
///
/// Three special `setup_*` hooks are called *before* descending into a scoped body, giving
/// the implementor a chance to extend its environment with the new bindings:
///
/// - [`setup_let_scope`](TermRecursor::setup_let_scope) – called after all let-binding
///   right-hand sides have been recursed, before entering the body.
/// - [`setup_quantifier_scope`](TermRecursor::setup_quantifier_scope) – called before
///   entering the body of a `Forall` or `Exists`.
/// - [`setup_match_case_scope`](TermRecursor::setup_match_case_scope) – called before
///   entering each match arm body.
#[allow(clippy::too_many_arguments)]
pub trait TermRecursor<Str, So, T> {
    /// The type produced by each recursive step.
    type Out;
    /// The type produced by each attribute callback.
    type Attr;
    /// The type produced by a let binding.
    type Binding;
    /// The type produced by a pattern in a match expression.
    type Pattern;
    /// The type produced by an arm in a match expression.
    type Arm;
    /// The error type returned when a callback fails.
    ///
    /// Set to [Bottom] to enable [Self::recurse_on_term_no_err].
    type Err;

    /// Entry point: recursively process `t` using the stack-based traversal.
    fn recurse_on_term(&mut self, t: &T) -> Result<Self::Out, Self::Err>
    where
        Self: Sized,
        T: Contains<T: Repr<T = Term<Str, So, T>>>,
    {
        term_recursion(self, t)
    }

    /// Convenience entry point for infallible recursors (where `Err = Bottom`).
    ///
    /// Equivalent to [`recurse_on_term`](Self::recurse_on_term) but returns `Self::Out`
    /// directly instead of `Result`, since the error branch is statically unreachable.
    fn recurse_on_term_no_err(&mut self, t: &T) -> Self::Out
    where
        Self: Sized,
        T: Contains<T: Repr<T = Term<Str, So, T>>>,
        Self::Err: IsBottom,
    {
        self.recurse_on_term(t)
            .unwrap_or_else(|b| match b.bottom() {})
    }

    // --- Leaf callbacks ---

    /// Called for a constant literal.
    fn on_constant(
        &mut self,
        current: &T,
        constant: &Constant<Str>,
        sort: &Option<So>,
    ) -> Result<Self::Out, Self::Err>;
    /// Called for a globally declared/defined identifier.
    fn on_global(
        &mut self,
        current: &T,
        id: &QualifiedIdentifier<Str, So>,
        sort: &Option<So>,
    ) -> Result<Self::Out, Self::Err>;
    /// Called for a locally bound variable.
    fn on_local(&mut self, current: &T, id: &Local<Str, So>) -> Result<Self::Out, Self::Err>;

    // --- Compound callbacks ---

    /// Called for a function application after all arguments have been recursed.
    fn on_app(
        &mut self,
        current: &T,
        id: &QualifiedIdentifier<Str, So>,
        ts: &[T],
        s: &Option<So>,
        recs: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err>;

    // --- Scoped constructs ---

    /// Called after a let binding term has been recursed.
    fn on_let_binding(
        &mut self,
        current: &T,
        vs: &[VarBinding<Str, T>],
        body: &T,
        binding_idx: usize,
        binding_rec: Self::Out,
    ) -> Result<Self::Binding, Self::Err>;

    /// Called after all let-binding RHS values have been recursed, before entering the body.
    /// Use this to extend the environment with the new bindings.
    fn setup_let_scope(
        &mut self,
        current: &T,
        vs: &[VarBinding<Str, T>],
        body: &T,
        vs_rec: &[Self::Binding],
    ) -> Result<(), Self::Err>;

    fn cleanup_let_scope_on_error(
        &mut self,
        _current: &T,
        _vs: &[VarBinding<Str, T>],
        _body: &T,
        _vs_rec: Vec<Self::Binding>,
    ) {
    }

    /// Called after all let-binding RHS and the body have been recursed.
    fn on_let(
        &mut self,
        current: &T,
        vs: &[VarBinding<Str, T>],
        body: &T,
        vs_rec: Vec<Self::Binding>,
        body_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err>;

    /// Called before descending into the body of a `Forall` or `Exists`.
    fn setup_quantifier_scope(
        &mut self,
        current: &T,
        vs: &[VarBinding<Str, So>],
        t: &T,
        is_forall: bool,
    ) -> Result<(), Self::Err>;

    fn cleanup_quantifier_scope_on_error(
        &mut self,
        _current: &T,
        _vs: &[VarBinding<Str, So>],
        _t: &T,
        _is_forall: bool,
    ) {
    }

    /// Called for `exists` after the body has been recursed.
    fn on_exists(
        &mut self,
        current: &T,
        vs: &[VarBinding<Str, So>],
        t: &T,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err>;
    /// Called for `forall` after the body has been recursed.
    fn on_forall(
        &mut self,
        current: &T,
        vs: &[VarBinding<Str, So>],
        t: &T,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err>;

    /// Called before descending into each match arm body.
    fn setup_match_case_scope(
        &mut self,
        current: &T,
        scrutinee: &T,
        cases: &[PatternArm<Str, T>],
        scrutinee_rec: &Self::Out,
        case_idx: usize,
    ) -> Result<Self::Pattern, Self::Err>;

    fn cleanup_match_case_scope_on_error(
        &mut self,
        _current: &T,
        _scrutinee: &T,
        _cases: &[PatternArm<Str, T>],
        _scrutinee_rec: Self::Out,
        _case_idx: usize,
    ) {
    }

    /// Called after each match arm body has been recursed.
    fn on_match_arm(
        &mut self,
        current: &T,
        scrutinee: &T,
        cases: &[PatternArm<Str, T>],
        scrutinee_rec: &Self::Out,
        case_idx: usize,
        current_pattern: Self::Pattern,
        arm: Self::Out,
    ) -> Result<Self::Arm, Self::Err>;
    /// Called after all match arms and the scrutinee have been recursed.
    fn on_match(
        &mut self,
        current: &T,
        scrutinee: &T,
        cases: &[PatternArm<Str, T>],
        scrutinee_rec: Self::Out,
        cases_rec: Vec<Self::Arm>,
    ) -> Result<Self::Out, Self::Err>;
    /// Called for an annotated term after the inner term and all attributes
    /// have been processed via their respective `on_attribute_*` callbacks.
    fn on_annotated(
        &mut self,
        current: &T,
        t: &T,
        anns: &[Attribute<Str, T>],
        t_rec: Self::Out,
        anns_rec: Vec<Self::Attr>,
    ) -> Result<Self::Out, Self::Err>;

    // --- Attribute callbacks ---

    /// Called for a keyword-only attribute (e.g. `:keyword`).
    fn on_attribute_keyword(&mut self, keyword: &Keyword) -> Result<Self::Attr, Self::Err>;
    /// Called for a keyword attribute with a constant value (e.g. `:keyword 42`).
    fn on_attribute_constant(
        &mut self,
        keyword: &Keyword,
        constant: &Constant<Str>,
    ) -> Result<Self::Attr, Self::Err>;
    /// Called for a keyword attribute with a symbol value (e.g. `:keyword sym`).
    fn on_attribute_symbol(
        &mut self,
        keyword: &Keyword,
        symbol: &Str,
    ) -> Result<Self::Attr, Self::Err>;
    /// Called for a `:named` attribute.
    fn on_attribute_named(&mut self, name: &Str) -> Result<Self::Attr, Self::Err>;
    /// Called for a `:pattern` attribute after all pattern sub-terms have been recursed.
    fn on_attribute_pattern(
        &mut self,
        patterns: &[T],
        patterns_rec: Vec<Self::Out>,
    ) -> Result<Self::Attr, Self::Err>;

    // --- Binary / n-ary connectives ---

    /// Called for `(= a b)` after both sides have been recursed.
    fn on_eq(
        &mut self,
        current: &T,
        a: &T,
        b: &T,
        a_rec: Self::Out,
        b_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err>;
    /// Called for `(distinct ...)` after all children have been recursed.
    fn on_distinct(
        &mut self,
        current: &T,
        ts: &[T],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err>;
    /// Called for `(and ...)`.
    fn on_and(
        &mut self,
        current: &T,
        ts: &[T],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err>;
    /// Called for `(or ...)`.
    fn on_or(
        &mut self,
        current: &T,
        ts: &[T],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err>;
    /// Called for `(xor ...)`.
    fn on_xor(
        &mut self,
        current: &T,
        ts: &[T],
        ts_rec: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err>;
    /// Called for `(not t)`.
    fn on_not(&mut self, current: &T, t: &T, t_rec: Self::Out) -> Result<Self::Out, Self::Err>;
    /// Called for `(=> p1 ... pn concl)`.
    fn on_implies(
        &mut self,
        current: &T,
        ts: &[T],
        t: &T,
        ts_rec: Vec<Self::Out>,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err>;
    /// Called for `(ite cond then else)`.
    fn on_ite(
        &mut self,
        current: &T,
        b: &T,
        t: &T,
        e: &T,
        b_rec: Self::Out,
        t_rec: Self::Out,
        e_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err>;
}

/// A stack frame for iterative traversal of a [`Term`] tree.
///
/// Each variant represents a pending computation. Frames are stored in a `Vec` (the
/// traversal stack).
///
/// Multi-child nodes are split into sequential phases. For example, `Let` uses two frames:
/// `LetBindings` (processing binding RHS values left-to-right) then `LetBody` (processing
/// the body after the scope callback). Similarly, `Ite` uses three frames (`IteB` → `IteT`
/// → `IteE`) and `Implies` uses two (`ImpliesPremises` → `ImpliesConclusion`).
pub(crate) enum Frame<'a, Str, So, T, R: TermRecursor<Str, So, T>> {
    /// Function application: collecting argument results left-to-right.
    App {
        current: &'a T,
        id: &'a QualifiedIdentifier<Str, So>,
        args: &'a [T],
        sort: &'a Option<So>,
        rec: Vec<R::Out>,
    },
    /// Let-binding phase 1: recursing on binding RHS values left-to-right.
    LetBindings {
        current: &'a T,
        vs: &'a [VarBinding<Str, T>],
        body: &'a T,
        vs_rec: Vec<R::Binding>,
    },
    /// Let-binding phase 2: recursing on the body (after `setup_let_scope`).
    LetBody {
        current: &'a T,
        vs: &'a [VarBinding<Str, T>],
        body: &'a T,
        vs_rec: Vec<R::Binding>,
    },
    /// `Forall` / `Exists`: recursing on the body (after `setup_quantifier_scope`).
    Quantifier {
        current: &'a T,
        vs: &'a [VarBinding<Str, So>],
        body: &'a T,
        is_forall: bool,
    },
    /// Match phase 1: recursing on the scrutinee.
    MatchScrutinee {
        current: &'a T,
        scrutinee: &'a T,
        cases: &'a [PatternArm<Str, T>],
    },
    /// Match phase 2: recursing on arm bodies left-to-right (after `setup_match_case_scope`).
    MatchCases {
        current: &'a T,
        scrutinee: &'a T,
        cases: &'a [PatternArm<Str, T>],
        scrutinee_rec: R::Out,
        case_rec: Vec<R::Arm>,
        current_pattern: Option<R::Pattern>,
    },
    /// Equality phase 1: recursing on the left operand.
    EqL { current: &'a T, l: &'a T, r: &'a T },
    /// Equality phase 2: recursing on the right operand.
    EqR {
        current: &'a T,
        l: &'a T,
        r: &'a T,
        l_rec: R::Out,
    },
    /// Annotated phase 1: recursing on the inner term.
    AnnotatedBody {
        current: &'a T,
        body: &'a T,
        anns: &'a [Attribute<Str, T>],
    },
    /// Annotated phase 2: recursing on `Attribute::Pattern` sub-terms.
    AnnotatedAttrs {
        current: &'a T,
        body: &'a T,
        anns: &'a [Attribute<Str, T>],
        t_rec: R::Out,
        anns_rec: Vec<R::Attr>,
        cur_pattern_rec: Vec<R::Out>,
    },
    /// `Distinct`, `And`, `Or`, or `Xor`: collecting child results left-to-right.
    Nary {
        current: &'a T,
        kind: NaryKind,
        ts: &'a [T],
        rec: Vec<R::Out>,
    },
    /// `Not`: single child.
    Not { current: &'a T, t: &'a T },
    /// `Implies` phase 1: collecting premise results left-to-right.
    ImpliesPremises {
        current: &'a T,
        ts: &'a [T],
        t: &'a T,
        rec: Vec<R::Out>,
    },
    /// `Implies` phase 2: recursing on the conclusion.
    ImpliesConclusion {
        current: &'a T,
        ts: &'a [T],
        t: &'a T,
        ts_rec: Vec<R::Out>,
    },
    /// `Ite` phase 1: recursing on the condition.
    IteB {
        current: &'a T,
        b: &'a T,
        t: &'a T,
        e: &'a T,
    },
    /// `Ite` phase 2: recursing on the then-branch.
    IteT {
        current: &'a T,
        b: &'a T,
        t: &'a T,
        e: &'a T,
        b_rec: R::Out,
    },
    /// `Ite` phase 3: recursing on the else-branch.
    IteE {
        current: &'a T,
        b: &'a T,
        t: &'a T,
        e: &'a T,
        b_rec: R::Out,
        t_rec: R::Out,
    },
}

/// Discriminant for the [`Nary`](Frame::Nary) variant.
#[derive(Clone, Copy)]
pub(crate) enum NaryKind {
    Distinct,
    And,
    Or,
    Xor,
}

/// The traversal stack: a `Vec` of frames.
pub(crate) type RStack<'a, R, Str, So, T> = Vec<Frame<'a, Str, So, T, R>>;

/// Advance `anns_rec` past consecutive non-`Pattern` attributes starting at
/// `anns[anns_rec.len()]`. Stops when a `Pattern` is encountered or all attributes
/// are consumed. Non-`Pattern` attributes are processed via the recursor's
/// `on_attribute_*` callbacks.
fn advance_attributes_until_pattern<R, Str, So, T>(
    recursor: &mut R,
    anns: &[Attribute<Str, T>],
    anns_rec: &mut Vec<R::Attr>,
) -> Result<(), R::Err>
where
    R: TermRecursor<Str, So, T>,
{
    while anns_rec.len() < anns.len() {
        match &anns[anns_rec.len()] {
            Attribute::Pattern(ts) => {
                if ts.is_empty() {
                    anns_rec.push(recursor.on_attribute_pattern(ts, vec![])?);
                } else {
                    break;
                }
            }
            Attribute::Keyword(k) => anns_rec.push(recursor.on_attribute_keyword(k)?),
            Attribute::Constant(k, c) => anns_rec.push(recursor.on_attribute_constant(k, c)?),
            Attribute::Symbol(k, s) => anns_rec.push(recursor.on_attribute_symbol(k, s)?),
            Attribute::Named(s) => anns_rec.push(recursor.on_attribute_named(s)?),
        }
    }
    Ok(())
}

/// Result of [`push_result`]: either the final value or a frame needing more children.
type PushResult<'a, R, Str, So, T> = Result<
    Either<<R as TermRecursor<Str, So, T>>::Out, Frame<'a, Str, So, T, R>>,
    <R as TermRecursor<Str, So, T>>::Err,
>;

/// Propagate a freshly computed `result` upward through the stack.
///
/// Pops frames and invokes callbacks as children complete. When a frame still has
/// unprocessed children, it returns `Either::Right(frame)`, where `frame` is the top of the stack,
/// so the main loop can push the frame back and expand the next child. Returns `Either::Left(result)`
/// when the stack is empty (traversal complete).
pub(crate) fn push_result<'a, R, Str, So, T>(
    recursor: &mut R,
    stack: &mut RStack<'a, R, Str, So, T>,
    mut result: R::Out,
) -> PushResult<'a, R, Str, So, T>
where
    R: TermRecursor<Str, So, T>,
{
    loop {
        let frame = match stack.pop() {
            Some(f) => f,
            None => return Ok(Either::Left(result)),
        };
        match frame {
            Frame::App {
                current,
                id,
                args,
                sort,
                mut rec,
            } => {
                rec.push(result);
                if rec.len() >= args.len() {
                    result = recursor.on_app(current, id, args, sort, rec)?;
                } else {
                    return Ok(Either::Right(Frame::App {
                        current,
                        id,
                        args,
                        sort,
                        rec,
                    }));
                }
            }
            Frame::LetBindings {
                current,
                vs,
                body,
                mut vs_rec,
            } => {
                vs_rec.push(recursor.on_let_binding(current, vs, body, vs_rec.len(), result)?);
                let frame = if vs_rec.len() >= vs.len() {
                    Frame::LetBody {
                        current,
                        vs,
                        vs_rec,
                        body,
                    }
                } else {
                    Frame::LetBindings {
                        current,
                        vs,
                        body,
                        vs_rec,
                    }
                };
                return Ok(Either::Right(frame));
            }
            Frame::LetBody {
                current,
                vs,
                vs_rec,
                body,
            } => {
                result = recursor.on_let(current, vs, body, vs_rec, result)?;
            }
            Frame::Quantifier {
                current,
                vs,
                body,
                is_forall,
            } => {
                result = if is_forall {
                    recursor.on_forall(current, vs, body, result)
                } else {
                    recursor.on_exists(current, vs, body, result)
                }?;
            }
            Frame::MatchScrutinee {
                current,
                scrutinee,
                cases,
            } => {
                if cases.is_empty() {
                    result = recursor.on_match(current, scrutinee, cases, result, vec![])?;
                } else {
                    return Ok(Either::Right(Frame::MatchCases {
                        current,
                        scrutinee,
                        cases,
                        scrutinee_rec: result,
                        case_rec: vec![],
                        current_pattern: None,
                    }));
                }
            }
            Frame::MatchCases {
                current,
                scrutinee,
                cases,
                scrutinee_rec,
                mut case_rec,
                current_pattern,
            } => {
                let arm = recursor.on_match_arm(
                    current,
                    scrutinee,
                    cases,
                    &scrutinee_rec,
                    case_rec.len(),
                    current_pattern.unwrap(),
                    result,
                )?;
                case_rec.push(arm);
                if case_rec.len() >= cases.len() {
                    result =
                        recursor.on_match(current, scrutinee, cases, scrutinee_rec, case_rec)?;
                } else {
                    return Ok(Either::Right(Frame::MatchCases {
                        current,
                        scrutinee,
                        cases,
                        scrutinee_rec,
                        case_rec,
                        current_pattern: None,
                    }));
                }
            }
            Frame::EqL { current, l, r } => {
                return Ok(Either::Right(Frame::EqR {
                    current,
                    l,
                    r,
                    l_rec: result,
                }));
            }
            Frame::EqR {
                current,
                l,
                r,
                l_rec,
            } => {
                result = recursor.on_eq(current, l, r, l_rec, result)?;
            }
            Frame::AnnotatedBody {
                current,
                body,
                anns,
            } => {
                let mut anns_rec: Vec<R::Attr> = vec![];
                advance_attributes_until_pattern(recursor, anns, &mut anns_rec)?;
                if anns_rec.len() >= anns.len() {
                    result = recursor.on_annotated(current, body, anns, result, anns_rec)?;
                } else {
                    return Ok(Either::Right(Frame::AnnotatedAttrs {
                        current,
                        body,
                        anns,
                        t_rec: result,
                        anns_rec,
                        cur_pattern_rec: vec![],
                    }));
                }
            }
            Frame::AnnotatedAttrs {
                current,
                body,
                anns,
                t_rec,
                mut anns_rec,
                mut cur_pattern_rec,
            } => {
                cur_pattern_rec.push(result);
                let pat_ts = match &anns[anns_rec.len()] {
                    Attribute::Pattern(ts) => ts,
                    _ => unreachable!(),
                };
                if cur_pattern_rec.len() >= pat_ts.len() {
                    anns_rec.push(recursor.on_attribute_pattern(pat_ts, cur_pattern_rec)?);
                    cur_pattern_rec = vec![];
                    advance_attributes_until_pattern(recursor, anns, &mut anns_rec)?;
                    if anns_rec.len() >= anns.len() {
                        result = recursor.on_annotated(current, body, anns, t_rec, anns_rec)?;
                    } else {
                        return Ok(Either::Right(Frame::AnnotatedAttrs {
                            current,
                            body,
                            anns,
                            t_rec,
                            anns_rec,
                            cur_pattern_rec,
                        }));
                    }
                } else {
                    return Ok(Either::Right(Frame::AnnotatedAttrs {
                        current,
                        body,
                        anns,
                        t_rec,
                        anns_rec,
                        cur_pattern_rec,
                    }));
                }
            }
            Frame::Nary {
                current,
                kind,
                ts,
                mut rec,
            } => {
                rec.push(result);
                if rec.len() >= ts.len() {
                    result = match kind {
                        NaryKind::Distinct => recursor.on_distinct(current, ts, rec)?,
                        NaryKind::And => recursor.on_and(current, ts, rec)?,
                        NaryKind::Or => recursor.on_or(current, ts, rec)?,
                        NaryKind::Xor => recursor.on_xor(current, ts, rec)?,
                    };
                } else {
                    return Ok(Either::Right(Frame::Nary {
                        current,
                        kind,
                        ts,
                        rec,
                    }));
                }
            }
            Frame::Not { current, t } => {
                result = recursor.on_not(current, t, result)?;
            }
            Frame::ImpliesPremises {
                current,
                ts,
                t,
                mut rec,
            } => {
                rec.push(result);
                let frame = if rec.len() >= ts.len() {
                    Frame::ImpliesConclusion {
                        current,
                        ts,
                        t,
                        ts_rec: rec,
                    }
                } else {
                    Frame::ImpliesPremises {
                        current,
                        ts,
                        t,
                        rec,
                    }
                };
                return Ok(Either::Right(frame));
            }
            Frame::ImpliesConclusion {
                current,
                ts,
                t,
                ts_rec,
            } => {
                result = recursor.on_implies(current, ts, t, ts_rec, result)?;
            }
            Frame::IteB { current, b, t, e } => {
                return Ok(Either::Right(Frame::IteT {
                    current,
                    b,
                    t,
                    e,
                    b_rec: result,
                }));
            }
            Frame::IteT {
                current,
                b,
                t,
                e,
                b_rec,
            } => {
                return Ok(Either::Right(Frame::IteE {
                    current,
                    b,
                    t,
                    e,
                    b_rec,
                    t_rec: result,
                }));
            }
            Frame::IteE {
                current,
                b,
                t,
                e,
                b_rec,
                t_rec,
            } => {
                result = recursor.on_ite(current, b, t, e, b_rec, t_rec, result)?;
            }
        }
    }
}

pub(crate) fn next_child<'a, R, Str, So, T>(
    recursor: &mut R,
    frame: &mut Frame<'a, Str, So, T, R>,
) -> Result<&'a T, R::Err>
where
    R: TermRecursor<Str, So, T>,
{
    match frame {
        Frame::App { args, rec, .. } => Ok(&args[rec.len()]),
        Frame::LetBindings { vs, vs_rec, .. } => Ok(&vs[vs_rec.len()].2),
        Frame::LetBody {
            current,
            vs,
            vs_rec,
            body,
            ..
        } => {
            recursor.setup_let_scope(current, vs, body, vs_rec)?;
            Ok(body)
        }
        Frame::Quantifier {
            current,
            vs,
            body,
            is_forall,
            ..
        } => {
            recursor.setup_quantifier_scope(current, vs, body, *is_forall)?;
            Ok(body)
        }
        Frame::MatchScrutinee { scrutinee, .. } => Ok(scrutinee),
        Frame::MatchCases {
            current,
            scrutinee,
            cases,
            scrutinee_rec,
            case_rec,
            current_pattern,
        } => {
            let pat = recursor.setup_match_case_scope(
                current,
                scrutinee,
                cases,
                scrutinee_rec,
                case_rec.len(),
            )?;
            *current_pattern = Some(pat);
            Ok(&cases[case_rec.len()].body)
        }
        Frame::EqL { l, .. } => Ok(l),
        Frame::EqR { r, .. } => Ok(r),
        Frame::AnnotatedBody { body, .. } => Ok(body),
        Frame::AnnotatedAttrs {
            anns,
            anns_rec,
            cur_pattern_rec,
            ..
        } => match &anns[anns_rec.len()] {
            Attribute::Pattern(ts) => Ok(&ts[cur_pattern_rec.len()]),
            _ => unreachable!(),
        },
        Frame::Nary { ts, rec, .. } => Ok(&ts[rec.len()]),
        Frame::Not { t, .. } => Ok(t),
        Frame::ImpliesPremises { ts, rec, .. } => Ok(&ts[rec.len()]),
        Frame::ImpliesConclusion { t, .. } => Ok(t),
        Frame::IteB { b, .. } => Ok(b),
        Frame::IteT { t, .. } => Ok(t),
        Frame::IteE { e, .. } => Ok(e),
    }
}

/// Descend from `current` into its leftmost leaf, pushing [`Frame`]s for
/// intermediate nodes, then resolve the leaf via the appropriate callback.
///
/// Loops over [`expand_and_resolve_once`] until a leaf is reached.
pub(crate) fn expand_and_resolve<'a, R, Str: 'a, So: 'a, T>(
    recursor: &mut R,
    stack: &mut RStack<'a, R, Str, So, T>,
    mut current: &'a T,
) -> Result<R::Out, R::Err>
where
    R: TermRecursor<Str, So, T>,
    T: Contains<T: Repr<T = Term<Str, So, T>>>,
{
    loop {
        match expand_and_resolve_once(recursor, stack, current)? {
            Either::Left(r) => {
                current = r;
            }
            Either::Right(result) => {
                return Ok(result);
            }
        }
    }
}

/// Process a single term node: either push a [`Frame`] and return the next
/// child to descend into (`Either::Left`), or resolve a leaf directly via
/// its callback (`Either::Right`).
#[inline]
pub(crate) fn expand_and_resolve_once<'a, R, Str: 'a, So: 'a, T>(
    recursor: &mut R,
    stack: &mut RStack<'a, R, Str, So, T>,
    current: &'a T,
) -> Result<Either<&'a T, R::Out>, R::Err>
where
    R: TermRecursor<Str, So, T>,
    T: Contains<T: Repr<T = Term<Str, So, T>>>,
{
    match current.inner().repr() {
        Term::Constant(constant, sort) => recursor
            .on_constant(current, constant, sort)
            .map(Either::Right),
        Term::Global(id, sort) => recursor.on_global(current, id, sort).map(Either::Right),
        Term::Local(id) => recursor.on_local(current, id).map(Either::Right),
        Term::App(id, args, sort) => {
            if args.is_empty() {
                recursor
                    .on_app(current, id, args, sort, vec![])
                    .map(Either::Right)
            } else {
                stack.push(Frame::App {
                    current,
                    id,
                    args,
                    sort,
                    rec: Vec::with_capacity(args.len()),
                });
                Ok(Either::Left(&args[0]))
            }
        }
        Term::Let(vs, body) => {
            if vs.is_empty() {
                let vc = vec![];
                recursor.setup_let_scope(current, vs, body, &vc)?;
                stack.push(Frame::LetBody {
                    current,
                    vs,
                    body,
                    vs_rec: vc,
                });
                Ok(Either::Left(body))
            } else {
                stack.push(Frame::LetBindings {
                    current,
                    vs,
                    body,
                    vs_rec: Vec::with_capacity(vs.len()),
                });
                Ok(Either::Left(&vs[0].2))
            }
        }
        Term::Exists(vs, body) => {
            recursor.setup_quantifier_scope(current, vs, body, false)?;
            stack.push(Frame::Quantifier {
                current,
                vs,
                body,
                is_forall: false,
            });
            Ok(Either::Left(body))
        }
        Term::Forall(vs, body) => {
            recursor.setup_quantifier_scope(current, vs, body, true)?;
            stack.push(Frame::Quantifier {
                current,
                vs,
                body,
                is_forall: true,
            });
            Ok(Either::Left(body))
        }
        Term::Matching(scrutinee, cases) => {
            stack.push(Frame::MatchScrutinee {
                current,
                scrutinee,
                cases,
            });
            Ok(Either::Left(scrutinee))
        }
        Term::Annotated(body, anns) => {
            stack.push(Frame::AnnotatedBody {
                current,
                body,
                anns,
            });
            Ok(Either::Left(body))
        }
        Term::Eq(l, r) => {
            stack.push(Frame::EqL { current, l, r });
            Ok(Either::Left(l))
        }
        Term::Distinct(ts) => {
            if ts.is_empty() {
                recursor.on_distinct(current, ts, vec![]).map(Either::Right)
            } else {
                stack.push(Frame::Nary {
                    current,
                    kind: NaryKind::Distinct,
                    ts,
                    rec: Vec::with_capacity(ts.len()),
                });
                Ok(Either::Left(&ts[0]))
            }
        }
        Term::And(ts) => {
            if ts.is_empty() {
                recursor.on_and(current, ts, vec![]).map(Either::Right)
            } else {
                stack.push(Frame::Nary {
                    current,
                    kind: NaryKind::And,
                    ts,
                    rec: Vec::with_capacity(ts.len()),
                });
                Ok(Either::Left(&ts[0]))
            }
        }
        Term::Or(ts) => {
            if ts.is_empty() {
                recursor.on_or(current, ts, vec![]).map(Either::Right)
            } else {
                stack.push(Frame::Nary {
                    current,
                    kind: NaryKind::Or,
                    ts,
                    rec: Vec::with_capacity(ts.len()),
                });
                Ok(Either::Left(&ts[0]))
            }
        }
        Term::Xor(ts) => {
            if ts.is_empty() {
                recursor.on_xor(current, ts, vec![]).map(Either::Right)
            } else {
                stack.push(Frame::Nary {
                    current,
                    kind: NaryKind::Xor,
                    ts,
                    rec: Vec::with_capacity(ts.len()),
                });
                Ok(Either::Left(&ts[0]))
            }
        }
        Term::Implies(ts, concl) => {
            if ts.is_empty() {
                stack.push(Frame::ImpliesConclusion {
                    current,
                    ts,
                    t: concl,
                    ts_rec: vec![],
                });
                Ok(Either::Left(concl))
            } else {
                stack.push(Frame::ImpliesPremises {
                    current,
                    ts,
                    t: concl,
                    rec: Vec::with_capacity(ts.len()),
                });
                Ok(Either::Left(&ts[0]))
            }
        }
        Term::Not(inner) => {
            stack.push(Frame::Not { current, t: inner });
            Ok(Either::Left(inner))
        }
        Term::Ite(b, th, e) => {
            stack.push(Frame::IteB {
                current,
                b,
                t: th,
                e,
            });
            Ok(Either::Left(b))
        }
    }
}

pub(crate) fn rewind_stack_for_error<R, Str, So, T>(
    recursor: &mut R,
    stack: &mut RStack<'_, R, Str, So, T>,
) where
    R: TermRecursor<Str, So, T>,
{
    while let Some(frame) = stack.pop() {
        match frame {
            Frame::LetBody {
                current,
                vs,
                body,
                vs_rec,
            } => {
                recursor.cleanup_let_scope_on_error(current, vs, body, vs_rec);
            }
            Frame::Quantifier {
                current,
                vs,
                body,
                is_forall,
            } => {
                recursor.cleanup_quantifier_scope_on_error(current, vs, body, is_forall);
            }
            Frame::MatchCases {
                current,
                scrutinee,
                cases,
                scrutinee_rec,
                case_rec,
                current_pattern: _,
            } => {
                recursor.cleanup_match_case_scope_on_error(
                    current,
                    scrutinee,
                    scrutinee_rec,
                    cases,
                    case_rec.len(),
                );
            }
            _ => {}
        }
    }
}

pub(crate) fn term_recursion_inner<R, Str, So, T>(
    recursor: &mut R,
    term: &T,
    stack: &mut RStack<'_, R, Str, So, T>,
) -> Result<R::Out, R::Err>
where
    R: TermRecursor<Str, So, T>,
    T: Contains<T: Repr<T = Term<Str, So, T>>>,
{
    let mut result = expand_and_resolve(recursor, stack, term)?;
    loop {
        match push_result(recursor, stack, result)? {
            Either::Left(final_result) => return Ok(final_result),
            Either::Right(mut frame) => {
                let child = next_child(recursor, &mut frame)?;
                stack.push(frame);
                result = expand_and_resolve(recursor, stack, child)?;
            }
        }
    }
}

pub(crate) fn term_recursion<R, Str, So, T>(recursor: &mut R, term: &T) -> Result<R::Out, R::Err>
where
    R: TermRecursor<Str, So, T>,
    T: Contains<T: Repr<T = Term<Str, So, T>>>,
{
    let mut stack: RStack<'_, R, Str, So, T> = Vec::new();
    let result = term_recursion_inner(recursor, term, &mut stack);
    if result.is_err() {
        rewind_stack_for_error(recursor, &mut stack);
    }
    result
}
