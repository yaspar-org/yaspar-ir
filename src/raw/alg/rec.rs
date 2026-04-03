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
//! 1. **Expand** – [`expand`] descends from a term into its leftmost leaf, pushing a
//!    [`Frame`] for every intermediate node onto the stack `Vec`.
//!
//! 2. **Resolve** – [`resolve_leaf`] calls the appropriate leaf callback (`on_constant`,
//!    `on_global`, or `on_local`) to produce a result.
//!
//! 3. **Push** – [`push_result`] propagates a result upward through the stack. At each
//!    frame it either:
//!    - accumulates the result and returns so the next child can be expanded, or
//!    - invokes the `on_*` callback when all children are ready and continues upward.
//!
//! 4. **Next** – [`next_child`] peeks at the top frame to determine the next child term
//!    to expand. For scoped constructs (`Let`, `Quantifier`, `Match`) it also invokes
//!    the appropriate `setup_*` callback.
//!
//! The main loop in [`term_recursion`] alternates between these phases until the stack
//! is empty, at which point the final result is returned.

use crate::ast::Repr;
use crate::raw::alg::*;

/// A visitor trait for performing stack-safe, bottom-up recursion over [`Term`] trees.
///
/// Implementors define one callback per `Term` variant. Leaf callbacks (`on_constant`,
/// `on_global`, `on_local`) receive only the original node data. Compound callbacks
/// additionally receive the already-computed recursive results for their children.
///
/// Two special `setup_*` hooks are called *before* descending into a scoped body, giving
/// the implementor a chance to extend its environment with the new bindings:
///
/// - [`setup_let_scope`](TermRecursor::setup_let_scope) – called after all let-binding
///   right-hand sides have been recursed, before entering the body.
/// - [`setup_quantifier_scope`](TermRecursor::setup_quantifier_scope) – called before
///   entering the body of a `Forall` or `Exists`.
/// - [`setup_match_case_scope`](TermRecursor::setup_match_case_scope) – called before
///   entering each match arm body.
pub trait TermRecursor<Str, So, T> {
    /// The type produced by each recursive step.
    type Out;
    /// The type produced by each attribute callback.
    type Attr;
    /// The error type returned when a callback fails.
    type Err;

    /// Entry point: recursively process `t` using the zipper-based traversal.
    fn recurse_on_term(&mut self, t: &T) -> Result<Self::Out, Self::Err>
    where
        Self: Sized,
        T: Contains<T: Repr<T = Term<Str, So, T>>>,
    {
        term_recursion(self, t)
    }

    // --- Leaf callbacks ---

    /// Called for a constant literal.
    fn on_constant(
        &mut self,
        constant: &Constant<Str>,
        sort: &Option<So>,
    ) -> Result<Self::Out, Self::Err>;
    /// Called for a globally declared/defined identifier.
    fn on_global(
        &mut self,
        id: &QualifiedIdentifier<Str, So>,
        sort: &Option<So>,
    ) -> Result<Self::Out, Self::Err>;
    /// Called for a locally bound variable.
    fn on_local(&mut self, id: &Local<Str, So>) -> Result<Self::Out, Self::Err>;

    // --- Compound callbacks ---

    /// Called for a function application after all arguments have been recursed.
    fn on_app(
        &mut self,
        id: &QualifiedIdentifier<Str, So>,
        ts: &[T],
        s: &Option<So>,
        recs: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err>;

    // --- Scoped constructs ---

    /// Called after all let-binding RHS values have been recursed, before entering the body.
    /// Use this to extend the environment with the new bindings.
    fn setup_let_scope(
        &mut self,
        vs: &[VarBinding<Str, T>],
        body: &T,
        vs_rec: &[VarBinding<&Str, Self::Out>],
    ) -> Result<(), Self::Err>;

    /// Called after all let-binding RHS and the body have been recursed.
    fn on_let(
        &mut self,
        vs: &[VarBinding<Str, T>],
        body: &T,
        vs_rec: Vec<VarBinding<&Str, Self::Out>>,
        body_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err>;

    /// Called before descending into the body of a `Forall` or `Exists`.
    fn setup_quantifier_scope(
        &mut self,
        vs: &[VarBinding<Str, So>],
        t: &T,
        is_forall: bool,
    ) -> Result<(), Self::Err>;
    /// Called for `exists` after the body has been recursed.
    fn on_exists(
        &mut self,
        vs: &[VarBinding<Str, So>],
        t: &T,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err>;
    /// Called for `forall` after the body has been recursed.
    fn on_forall(
        &mut self,
        vs: &[VarBinding<Str, So>],
        t: &T,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err>;

    /// Called before descending into each match arm body.
    fn setup_match_case_scope(
        &mut self,
        scrutinee: &T,
        cases: &[PatternArm<Str, T>],
        scrutinee_rec: &Self::Out,
        case_idx: usize,
    ) -> Result<(), Self::Err>;
    /// Called after each match arm body has been recursed.
    fn on_match_arm(
        &mut self,
        scrutinee: &T,
        cases: &[PatternArm<Str, T>],
        case_idx: usize,
        arm: Self::Out,
    ) -> Result<PatternArm<Str, Self::Out>, Self::Err>;
    /// Called after all match arms and the scrutinee have been recursed.
    fn on_match(
        &mut self,
        scrutinee: &T,
        cases: &[PatternArm<Str, T>],
        scrutinee_rec: Self::Out,
        cases_rec: Vec<PatternArm<Str, Self::Out>>,
    ) -> Result<Self::Out, Self::Err>;
    /// Called for an annotated term after the inner term and all attributes
    /// have been processed via their respective `on_attribute_*` callbacks.
    fn on_annotated(
        &mut self,
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
        a: &T,
        b: &T,
        a_rec: Self::Out,
        b_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err>;
    /// Called for `(distinct ...)` after all children have been recursed.
    fn on_distinct(&mut self, ts: &[T], ts_rec: Vec<Self::Out>) -> Result<Self::Out, Self::Err>;
    /// Called for `(and ...)`.
    fn on_and(&mut self, ts: &[T], ts_rec: Vec<Self::Out>) -> Result<Self::Out, Self::Err>;
    /// Called for `(or ...)`.
    fn on_or(&mut self, ts: &[T], ts_rec: Vec<Self::Out>) -> Result<Self::Out, Self::Err>;
    /// Called for `(xor ...)`.
    fn on_xor(&mut self, ts: &[T], ts_rec: Vec<Self::Out>) -> Result<Self::Out, Self::Err>;
    /// Called for `(not t)`.
    fn on_not(&mut self, t: &T, t_rec: Self::Out) -> Result<Self::Out, Self::Err>;
    /// Called for `(=> p1 ... pn concl)`.
    fn on_implies(
        &mut self,
        ts: &[T],
        t: &T,
        ts_rec: Vec<Self::Out>,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err>;
    /// Called for `(ite cond then else)`.
    fn on_ite(
        &mut self,
        b: &T,
        t: &T,
        e: &T,
        b_rec: Self::Out,
        t_rec: Self::Out,
        e_rec: &Self::Out,
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
enum Frame<'a, Str, So, T, Out, Attr> {
    /// Function application: collecting argument results left-to-right.
    App {
        id: &'a QualifiedIdentifier<Str, So>,
        args: &'a [T],
        sort: &'a Option<So>,
        rec: Vec<Out>,
    },
    /// Let-binding phase 1: recursing on binding RHS values left-to-right.
    LetBindings {
        vs: &'a [VarBinding<Str, T>],
        body: &'a T,
        vs_rec: Vec<VarBinding<&'a Str, Out>>,
    },
    /// Let-binding phase 2: recursing on the body (after `setup_let_scope`).
    LetBody {
        vs: &'a [VarBinding<Str, T>],
        vs_rec: Vec<VarBinding<&'a Str, Out>>,
        body: &'a T,
    },
    /// `Forall` / `Exists`: recursing on the body (after `setup_quantifier_scope`).
    Quantifier {
        vs: &'a [VarBinding<Str, So>],
        body: &'a T,
        is_forall: bool,
    },
    /// Match phase 1: recursing on the scrutinee.
    MatchScrutinee {
        scrutinee: &'a T,
        cases: &'a [PatternArm<Str, T>],
    },
    /// Match phase 2: recursing on arm bodies left-to-right (after `setup_match_case_scope`).
    MatchCases {
        scrutinee: &'a T,
        cases: &'a [PatternArm<Str, T>],
        scrutinee_rec: Out,
        case_rec: Vec<PatternArm<Str, Out>>,
    },
    /// Equality phase 1: recursing on the left operand.
    EqL { l: &'a T, r: &'a T },
    /// Equality phase 2: recursing on the right operand.
    EqR { l: &'a T, r: &'a T, l_rec: Out },
    /// Annotated phase 1: recursing on the inner term.
    AnnotatedBody {
        body: &'a T,
        anns: &'a [Attribute<Str, T>],
    },
    /// Annotated phase 2: recursing on `Attribute::Pattern` sub-terms.
    AnnotatedAttrs {
        body: &'a T,
        anns: &'a [Attribute<Str, T>],
        t_rec: Out,
        anns_rec: Vec<Attr>,
        cur_pattern_rec: Vec<Out>,
    },
    /// `Distinct`, `And`, `Or`, or `Xor`: collecting child results left-to-right.
    Nary {
        kind: NaryKind,
        ts: &'a [T],
        rec: Vec<Out>,
    },
    /// `Not`: single child.
    Not { t: &'a T },
    /// `Implies` phase 1: collecting premise results left-to-right.
    ImpliesPremises {
        ts: &'a [T],
        t: &'a T,
        rec: Vec<Out>,
    },
    /// `Implies` phase 2: recursing on the conclusion.
    ImpliesConclusion {
        ts: &'a [T],
        t: &'a T,
        ts_rec: Vec<Out>,
    },
    /// `Ite` phase 1: recursing on the condition.
    IteB { b: &'a T, t: &'a T, e: &'a T },
    /// `Ite` phase 2: recursing on the then-branch.
    IteT {
        b: &'a T,
        t: &'a T,
        e: &'a T,
        b_rec: Out,
    },
    /// `Ite` phase 3: recursing on the else-branch.
    IteE {
        b: &'a T,
        t: &'a T,
        e: &'a T,
        b_rec: Out,
        t_rec: Out,
    },
}

/// Discriminant for the [`Nary`](Frame::Nary) variant.
#[derive(Clone, Copy)]
enum NaryKind {
    Distinct,
    And,
    Or,
    Xor,
}

/// The leaf information returned by [`expand`] when a leaf node is reached.
enum Leaf<'a, Str, So> {
    Constant {
        constant: &'a Constant<Str>,
        sort: &'a Option<So>,
    },
    Global {
        id: &'a QualifiedIdentifier<Str, So>,
        sort: &'a Option<So>,
    },
    Local {
        id: &'a Local<Str, So>,
    },
}

/// The traversal stack: a `Vec` of frames.
type Stack<'a, Str, So, T, Out, Attr> = Vec<Frame<'a, Str, So, T, Out, Attr>>;

/// A [`Stack`] specialized to a particular [`TermRecursor`].
type RStack<'a, R, Str, So, T> = Stack<
    'a,
    Str,
    So,
    T,
    <R as TermRecursor<Str, So, T>>::Out,
    <R as TermRecursor<Str, So, T>>::Attr,
>;

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
            Attribute::Pattern(_) => break,
            Attribute::Keyword(k) => anns_rec.push(recursor.on_attribute_keyword(k)?),
            Attribute::Constant(k, c) => anns_rec.push(recursor.on_attribute_constant(k, c)?),
            Attribute::Symbol(k, s) => anns_rec.push(recursor.on_attribute_symbol(k, s)?),
            Attribute::Named(s) => anns_rec.push(recursor.on_attribute_named(s)?),
        }
    }
    Ok(())
}

/// Propagate a freshly computed `result` upward through the stack.
///
/// Pops frames and invokes callbacks as children complete. When a frame still has
/// unprocessed children, it is pushed back (possibly in a new phase) and the function
/// returns `None` so the main loop can expand the next child. Returns `Some(result)`
/// when the stack is empty (traversal complete).
fn push_result<'a, R, Str, So, T>(
    recursor: &mut R,
    stack: &mut RStack<'a, R, Str, So, T>,
    mut result: R::Out,
) -> Result<Option<R::Out>, R::Err>
where
    R: TermRecursor<Str, So, T>,
{
    loop {
        let frame = match stack.pop() {
            Some(f) => f,
            None => return Ok(Some(result)),
        };
        match frame {
            Frame::App {
                id,
                args,
                sort,
                mut rec,
            } => {
                rec.push(result);
                if rec.len() >= args.len() {
                    result = recursor.on_app(id, args, sort, rec)?;
                } else {
                    stack.push(Frame::App {
                        id,
                        args,
                        sort,
                        rec,
                    });
                    return Ok(None);
                }
            }
            Frame::LetBindings {
                vs,
                body,
                mut vs_rec,
            } => {
                let v = &vs[vs_rec.len()];
                vs_rec.push(VarBinding(&v.0, v.1, result));
                if vs_rec.len() >= vs.len() {
                    stack.push(Frame::LetBody { vs, vs_rec, body });
                } else {
                    stack.push(Frame::LetBindings { vs, body, vs_rec });
                }
                return Ok(None);
            }
            Frame::LetBody { vs, vs_rec, body } => {
                result = recursor.on_let(vs, body, vs_rec, result)?;
            }
            Frame::Quantifier {
                vs,
                body,
                is_forall,
            } => {
                result = if is_forall {
                    recursor.on_forall(vs, body, result)
                } else {
                    recursor.on_exists(vs, body, result)
                }?;
            }
            Frame::MatchScrutinee { scrutinee, cases } => {
                stack.push(Frame::MatchCases {
                    scrutinee,
                    cases,
                    scrutinee_rec: result,
                    case_rec: vec![],
                });
                return Ok(None);
            }
            Frame::MatchCases {
                scrutinee,
                cases,
                scrutinee_rec,
                mut case_rec,
            } => {
                let arm = recursor.on_match_arm(scrutinee, cases, case_rec.len(), result)?;
                case_rec.push(arm);
                if case_rec.len() >= cases.len() {
                    result = recursor.on_match(scrutinee, cases, scrutinee_rec, case_rec)?;
                } else {
                    stack.push(Frame::MatchCases {
                        scrutinee,
                        cases,
                        scrutinee_rec,
                        case_rec,
                    });
                    return Ok(None);
                }
            }
            Frame::EqL { l, r } => {
                stack.push(Frame::EqR {
                    l,
                    r,
                    l_rec: result,
                });
                return Ok(None);
            }
            Frame::EqR { l, r, l_rec } => {
                result = recursor.on_eq(l, r, l_rec, result)?;
            }
            Frame::AnnotatedBody { body, anns } => {
                let mut anns_rec: Vec<R::Attr> = vec![];
                advance_attributes_until_pattern(recursor, anns, &mut anns_rec)?;
                if anns_rec.len() >= anns.len() {
                    result = recursor.on_annotated(body, anns, result, anns_rec)?;
                } else {
                    stack.push(Frame::AnnotatedAttrs {
                        body,
                        anns,
                        t_rec: result,
                        anns_rec,
                        cur_pattern_rec: vec![],
                    });
                    return Ok(None);
                }
            }
            Frame::AnnotatedAttrs {
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
                        result = recursor.on_annotated(body, anns, t_rec, anns_rec)?;
                    } else {
                        stack.push(Frame::AnnotatedAttrs {
                            body,
                            anns,
                            t_rec,
                            anns_rec,
                            cur_pattern_rec,
                        });
                        return Ok(None);
                    }
                } else {
                    stack.push(Frame::AnnotatedAttrs {
                        body,
                        anns,
                        t_rec,
                        anns_rec,
                        cur_pattern_rec,
                    });
                    return Ok(None);
                }
            }
            Frame::Nary { kind, ts, mut rec } => {
                rec.push(result);
                if rec.len() >= ts.len() {
                    result = match kind {
                        NaryKind::Distinct => recursor.on_distinct(ts, rec)?,
                        NaryKind::And => recursor.on_and(ts, rec)?,
                        NaryKind::Or => recursor.on_or(ts, rec)?,
                        NaryKind::Xor => recursor.on_xor(ts, rec)?,
                    };
                } else {
                    stack.push(Frame::Nary { kind, ts, rec });
                    return Ok(None);
                }
            }
            Frame::Not { t } => {
                result = recursor.on_not(t, result)?;
            }
            Frame::ImpliesPremises { ts, t, mut rec } => {
                rec.push(result);
                if rec.len() >= ts.len() {
                    stack.push(Frame::ImpliesConclusion { ts, t, ts_rec: rec });
                } else {
                    stack.push(Frame::ImpliesPremises { ts, t, rec });
                }
                return Ok(None);
            }
            Frame::ImpliesConclusion { ts, t, ts_rec } => {
                result = recursor.on_implies(ts, t, ts_rec, result)?;
            }
            Frame::IteB { b, t, e } => {
                stack.push(Frame::IteT {
                    b,
                    t,
                    e,
                    b_rec: result,
                });
                return Ok(None);
            }
            Frame::IteT { b, t, e, b_rec } => {
                stack.push(Frame::IteE {
                    b,
                    t,
                    e,
                    b_rec,
                    t_rec: result,
                });
                return Ok(None);
            }
            Frame::IteE {
                b,
                t,
                e,
                b_rec,
                t_rec,
            } => {
                result = recursor.on_ite(b, t, e, b_rec, t_rec, &result)?;
            }
        }
    }
}

/// Determine the next child term to descend into.
///
/// Peeks at the top frame to find the next unprocessed child, invoking `setup_*`
/// callbacks for scoped constructs before returning the child reference.
fn next_child<'a, R, Str, So, T>(
    recursor: &mut R,
    stack: &RStack<'a, R, Str, So, T>,
) -> Result<Option<&'a T>, R::Err>
where
    R: TermRecursor<Str, So, T>,
{
    match stack.last() {
        None => Ok(None),
        Some(frame) => match frame {
            Frame::App { args, rec, .. } => Ok(Some(&args[rec.len()])),
            Frame::LetBindings { vs, vs_rec, .. } => Ok(Some(&vs[vs_rec.len()].2)),
            Frame::LetBody {
                vs, vs_rec, body, ..
            } => {
                recursor.setup_let_scope(vs, body, vs_rec)?;
                Ok(Some(body))
            }
            Frame::Quantifier {
                vs,
                body,
                is_forall,
                ..
            } => {
                recursor.setup_quantifier_scope(vs, body, *is_forall)?;
                Ok(Some(body))
            }
            Frame::MatchScrutinee { scrutinee, .. } => Ok(Some(scrutinee)),
            Frame::MatchCases {
                scrutinee,
                cases,
                scrutinee_rec,
                case_rec,
                ..
            } => {
                recursor.setup_match_case_scope(scrutinee, cases, scrutinee_rec, case_rec.len())?;
                Ok(Some(&cases[case_rec.len()].body))
            }
            Frame::EqL { l, .. } => Ok(Some(l)),
            Frame::EqR { r, .. } => Ok(Some(r)),
            Frame::AnnotatedBody { body, .. } => Ok(Some(body)),
            Frame::AnnotatedAttrs {
                anns,
                anns_rec,
                cur_pattern_rec,
                ..
            } => match &anns[anns_rec.len()] {
                Attribute::Pattern(ts) => Ok(Some(&ts[cur_pattern_rec.len()])),
                _ => unreachable!(),
            },
            Frame::Nary { ts, rec, .. } => Ok(Some(&ts[rec.len()])),
            Frame::Not { t, .. } => Ok(Some(t)),
            Frame::ImpliesPremises { ts, rec, .. } => Ok(Some(&ts[rec.len()])),
            Frame::ImpliesConclusion { t, .. } => Ok(Some(t)),
            Frame::IteB { b, .. } => Ok(Some(b)),
            Frame::IteT { t, .. } => Ok(Some(t)),
            Frame::IteE { e, .. } => Ok(Some(e)),
        },
    }
}

/// Descend from `t` to its leftmost leaf, pushing a frame for each intermediate node.
fn expand<'a, R, Str: 'a, So: 'a, T>(
    recursor: &mut R,
    stack: &mut RStack<'a, R, Str, So, T>,
    mut t: &'a T,
) -> Result<Leaf<'a, Str, So>, R::Err>
where
    R: TermRecursor<Str, So, T>,
    T: Contains<T: Repr<T = Term<Str, So, T>>>,
{
    loop {
        match t.inner().repr() {
            Term::Constant(constant, sort) => return Ok(Leaf::Constant { constant, sort }),
            Term::Global(id, sort) => return Ok(Leaf::Global { id, sort }),
            Term::Local(id) => return Ok(Leaf::Local { id }),
            Term::App(id, args, sort) => {
                stack.push(Frame::App {
                    id,
                    args,
                    sort,
                    rec: vec![],
                });
                t = &args[0];
            }
            Term::Let(vs, body) => {
                stack.push(Frame::LetBindings {
                    vs,
                    body,
                    vs_rec: vec![],
                });
                t = &vs[0].2;
            }
            Term::Exists(vs, body) => {
                recursor.setup_quantifier_scope(vs, body, false)?;
                stack.push(Frame::Quantifier {
                    vs,
                    body,
                    is_forall: false,
                });
                t = body;
            }
            Term::Forall(vs, body) => {
                recursor.setup_quantifier_scope(vs, body, true)?;
                stack.push(Frame::Quantifier {
                    vs,
                    body,
                    is_forall: true,
                });
                t = body;
            }
            Term::Matching(scrutinee, cases) => {
                stack.push(Frame::MatchScrutinee { scrutinee, cases });
                t = scrutinee;
            }
            Term::Annotated(body, anns) => {
                stack.push(Frame::AnnotatedBody { body, anns });
                t = body;
            }
            Term::Eq(l, r) => {
                stack.push(Frame::EqL { l, r });
                t = l;
            }
            Term::Distinct(ts) => {
                stack.push(Frame::Nary {
                    kind: NaryKind::Distinct,
                    ts,
                    rec: vec![],
                });
                t = &ts[0];
            }
            Term::And(ts) => {
                stack.push(Frame::Nary {
                    kind: NaryKind::And,
                    ts,
                    rec: vec![],
                });
                t = &ts[0];
            }
            Term::Or(ts) => {
                stack.push(Frame::Nary {
                    kind: NaryKind::Or,
                    ts,
                    rec: vec![],
                });
                t = &ts[0];
            }
            Term::Xor(ts) => {
                stack.push(Frame::Nary {
                    kind: NaryKind::Xor,
                    ts,
                    rec: vec![],
                });
                t = &ts[0];
            }
            Term::Implies(ts, concl) => {
                stack.push(Frame::ImpliesPremises {
                    ts,
                    t: concl,
                    rec: vec![],
                });
                t = &ts[0];
            }
            Term::Not(inner) => {
                stack.push(Frame::Not { t: inner });
                t = inner;
            }
            Term::Ite(b, th, e) => {
                stack.push(Frame::IteB { b, t: th, e });
                t = b;
            }
        }
    }
}

/// Resolve a leaf node into a result by calling the appropriate callback.
fn resolve_leaf<R, Str, So, T>(recursor: &mut R, leaf: Leaf<'_, Str, So>) -> Result<R::Out, R::Err>
where
    R: TermRecursor<Str, So, T>,
{
    match leaf {
        Leaf::Constant { constant, sort } => recursor.on_constant(constant, sort),
        Leaf::Global { id, sort } => recursor.on_global(id, sort),
        Leaf::Local { id } => recursor.on_local(id),
    }
}

/// Main entry point: iteratively traverse `term` using a Vec-based stack and return the
/// final result.
fn term_recursion<R, Str, So, T>(recursor: &mut R, term: &T) -> Result<R::Out, R::Err>
where
    R: TermRecursor<Str, So, T>,
    T: Contains<T: Repr<T = Term<Str, So, T>>>,
{
    let mut stack: RStack<'_, R, Str, So, T> = Vec::new();
    let leaf = expand(recursor, &mut stack, term)?;
    let mut result = resolve_leaf(recursor, leaf)?;
    loop {
        match push_result(recursor, &mut stack, result)? {
            Some(final_result) => return Ok(final_result),
            None => {
                // unwrap is safe below, as an empy stack should return Some in push_result and
                // hit the previous case.
                let child = next_child(recursor, &stack)?.unwrap();
                let leaf = expand(recursor, &mut stack, child)?;
                result = resolve_leaf(recursor, leaf)?;
            }
        }
    }
}
