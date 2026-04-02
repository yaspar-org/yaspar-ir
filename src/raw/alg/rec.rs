// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Stack-safe recursion over [`Term`] trees using a zipper-based traversal.
//!
//! Deeply nested terms can overflow the call stack when traversed with ordinary recursion.
//! This module provides [`TermRecursor`], a visitor-style trait whose default method
//! [`recurse_on_term`](TermRecursor::recurse_on_term) drives an iterative, heap-allocated
//! traversal via [`TermZipper`].
//!
//! # How it works
//!
//! The traversal is a standard left-to-right, depth-first walk:
//!
//! 1. **Expand** – [`term_recursion_zipper_expand`] descends from a term into its leftmost
//!    leaf, pushing a zipper frame for every intermediate node onto a linked list of
//!    heap-allocated boxes.
//!
//! 2. **Step** – [`term_recursion_zip_one_step`] resolves the current leaf (always a
//!    `Constant`, `Global`, or `Local`) by calling the corresponding `on_*` callback,
//!    then pushes the result upward.
//!
//! 3. **Push** – [`term_recursion_zipper_push`] propagates a result toward the root.
//!    At each frame it either:
//!    - accumulates the result and yields back to the main loop so the next child can be
//!      expanded, or
//!    - invokes the `on_*` callback when all children are ready and continues upward.
//!
//! 4. **Next** – [`term_recursion_zipper_next`] is called at the start of each step to
//!    determine the next child term to expand. For scoped constructs (`Let`, `Quantifier`,
//!    `Match`) it also invokes the appropriate `setup_*` callback so the recursor can
//!    update its environment before descending.
//!
//! The main loop in [`term_recursion`] alternates between next and push until the `Root`
//! frame is reached, at which point the final result is returned.

use crate::ast::Repr;
use crate::raw::alg::*;

/// Result of a single push step: either a zipper to continue from, or the final value.
enum Either<A, B> {
    Left(A),
    Right(B),
}

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
    /// The error type returned when a callback fails.
    type Err;

    /// Entry point: recursively process `t` using the zipper-based traversal.
    fn recurse_on_term(&mut self, t: &T) -> Result<Self::Out, Self::Err>
    where
        Self: Sized,
        Str: Clone,
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
        vs_rec: &[VarBinding<Str, Self::Out>],
    ) -> Result<(), Self::Err>;

    /// Called after all let-binding RHS and the body have been recursed.
    fn on_let(
        &mut self,
        vs: &[VarBinding<Str, T>],
        body: &T,
        vs_rec: Vec<VarBinding<Str, Self::Out>>,
        body_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err>;

    /// Called before descending into the body of a `Forall` or `Exists`.
    fn setup_quantifier_scope(
        &mut self,
        vs: &[VarBinding<Str, So>],
        t: &T,
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
    /// Called for an annotated term after the inner term and all `Pattern` sub-terms
    /// have been recursed. Non-`Pattern` attributes are cloned as-is.
    fn on_annotated(
        &mut self,
        t: &T,
        anns: &[Attribute<Str, T>],
        t_rec: Self::Out,
        anns_rec: Vec<Attribute<Str, Self::Out>>,
    ) -> Result<Self::Out, Self::Err>;

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
    /// Called for `(=> p1 ... pn concl)`. Premise results are passed by shared reference.
    fn on_implies(
        &mut self,
        ts: &[T],
        t: &T,
        ts_rec: &[Self::Out],
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err>;
    /// Called for `(ite cond then else)`. The else result is passed by shared reference.
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

/// A zipper (one-hole context) for iterative traversal of a [`Term`] tree.
///
/// Each variant represents a "frame" in the traversal stack. The `parent` field links to
/// the enclosing frame, forming a singly-linked list on the heap. Leaf variants (`Constant`,
/// `Global`, `Local`) are transient — they are immediately resolved and never stored across
/// loop iterations.
///
/// Multi-child nodes are split into sequential phases. For example, `Let` uses two frames:
/// `LetBindings` (processing binding RHS values left-to-right) then `LetBody` (processing
/// the body after the scope callback). Similarly, `Ite` uses three frames (`IteB` → `IteT`
/// → `IteE`) and `Implies` uses two (`ImpliesPremises` → `ImpliesConclusion`).
enum TermZipper<'a, Str, So, T, Out> {
    /// Sentinel: the traversal has returned to the top level.
    Root,
    // --- Leaf frames (resolved immediately, never stored across iterations) ---
    Constant {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        constant: &'a Constant<Str>,
        sort: &'a Option<So>,
    },
    Global {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        id: &'a QualifiedIdentifier<Str, So>,
        sort: &'a Option<So>,
    },
    Local {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        id: &'a Local<Str, So>,
    },
    // --- Multi-child compound frames ---
    /// Function application: collecting argument results left-to-right.
    App {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        id: &'a QualifiedIdentifier<Str, So>,
        args: &'a [T],
        sort: &'a Option<So>,
        rec: Vec<Out>,
    },
    /// Let-binding phase 1: recursing on binding RHS values left-to-right.
    LetBindings {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        vs: &'a [VarBinding<Str, T>],
        body: &'a T,
        vs_rec: Vec<VarBinding<Str, Out>>,
    },
    /// Let-binding phase 2: recursing on the body (after `setup_let_scope`).
    LetBody {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        vs: &'a [VarBinding<Str, T>],
        vs_rec: Vec<VarBinding<Str, Out>>,
        body: &'a T,
    },
    /// `Forall` / `Exists`: recursing on the body (after `setup_quantifier_scope`).
    Quantifier {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        vs: &'a [VarBinding<Str, So>],
        body: &'a T,
        is_forall: bool,
    },
    /// Match phase 1: recursing on the scrutinee.
    MatchScrutinee {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        scrutinee: &'a T,
        cases: &'a [PatternArm<Str, T>],
    },
    /// Match phase 2: recursing on arm bodies left-to-right (after `setup_match_case_scope`).
    MatchCases {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        scrutinee: &'a T,
        cases: &'a [PatternArm<Str, T>],
        scrutinee_rec: Out,
        case_rec: Vec<PatternArm<Str, Out>>,
    },
    /// Equality phase 1: recursing on the left operand.
    EqL {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        l: &'a T,
        r: &'a T,
    },
    /// Equality phase 2: recursing on the right operand.
    EqR {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        l: &'a T,
        r: &'a T,
        l_rec: Out,
    },
    /// Annotated phase 1: recursing on the inner term.
    AnnotatedBody {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        t: &'a T,
        anns: &'a [Attribute<Str, T>],
    },
    /// Annotated phase 2: recursing on `Attribute::Pattern` sub-terms.
    /// `anns_rec` tracks fully-processed attributes; `cur_pattern_rec` accumulates
    /// results for the `Pattern` attribute currently at `anns[anns_rec.len()]`.
    AnnotatedAttrs {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        t: &'a T,
        anns: &'a [Attribute<Str, T>],
        t_rec: Out,
        /// Fully-processed attributes so far.
        anns_rec: Vec<Attribute<Str, Out>>,
        /// Within the current `Pattern` attribute, the terms processed so far.
        cur_pattern_rec: Vec<Out>,
    },
    /// `Distinct`, `And`, `Or`, or `Xor`: collecting child results left-to-right.
    Nary {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        kind: NaryKind,
        ts: &'a [T],
        rec: Vec<Out>,
    },
    /// `Not`: single child.
    Not {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        t: &'a T,
    },
    /// `Implies` phase 1: collecting premise results left-to-right.
    ImpliesPremises {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        ts: &'a [T],
        t: &'a T,
        rec: Vec<Out>,
    },
    /// `Implies` phase 2: recursing on the conclusion.
    ImpliesConclusion {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        ts: &'a [T],
        t: &'a T,
        ts_rec: Vec<Out>,
    },
    /// `Ite` phase 1: recursing on the condition.
    IteB {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        b: &'a T,
        t: &'a T,
        e: &'a T,
    },
    /// `Ite` phase 2: recursing on the then-branch.
    IteT {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        b: &'a T,
        t: &'a T,
        e: &'a T,
        b_rec: Out,
    },
    /// `Ite` phase 3: recursing on the else-branch.
    IteE {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        b: &'a T,
        t: &'a T,
        e: &'a T,
        b_rec: Out,
        t_rec: Out,
    },
}

/// Discriminant for the [`Nary`](TermZipper::Nary) zipper variant.
#[derive(Clone, Copy)]
enum NaryKind {
    Distinct,
    And,
    Or,
    Xor,
}

/// Advance `anns_rec` past consecutive non-`Pattern` attributes starting at
/// `anns[anns_rec.len()]`. Stops when a `Pattern` is encountered or all attributes
/// are consumed. Non-`Pattern` attributes are cloned with their `T` parameter erased
/// (they contain no sub-terms).
fn advance_attributes_until_pattern<Str: Clone, T, Out>(
    anns: &[Attribute<Str, T>],
    anns_rec: &mut Vec<Attribute<Str, Out>>,
) {
    while anns_rec.len() < anns.len() {
        match &anns[anns_rec.len()] {
            Attribute::Pattern(_) => break,
            Attribute::Keyword(k) => anns_rec.push(Attribute::Keyword(k.clone())),
            Attribute::Constant(k, c) => anns_rec.push(Attribute::Constant(k.clone(), c.clone())),
            Attribute::Symbol(k, s) => anns_rec.push(Attribute::Symbol(k.clone(), s.clone())),
            Attribute::Named(s) => anns_rec.push(Attribute::Named(s.clone())),
        }
    }
}

/// Propagate a freshly computed `result` upward through the zipper toward the root.
///
/// Returns `Right(value)` when the root is reached, or `Left(zipper)` when the current
/// frame still has unprocessed children and the main loop should expand the next one.
///
/// For frames that accumulate children (e.g. `App`, `Nary`, `LetBindings`), the result
/// is appended to the accumulator. If all children are now ready, the corresponding
/// `on_*` callback is invoked and propagation continues upward in the same call (the
/// inner `loop`). Otherwise the updated frame is returned for the next expansion.
fn term_recursion_zipper_push<'a, R, Str, So, T>(
    recursor: &mut R,
    mut zipper: Box<TermZipper<'a, Str, So, T, R::Out>>,
    mut result: R::Out,
) -> Result<Either<Box<TermZipper<'a, Str, So, T, R::Out>>, R::Out>, R::Err>
where
    Str: Clone,
    R: TermRecursor<Str, So, T>,
{
    loop {
        match *zipper {
            TermZipper::Root => return Ok(Either::Right(result)),
            TermZipper::Constant { .. } | TermZipper::Global { .. } | TermZipper::Local { .. } => {
                unreachable!()
            }
            TermZipper::App {
                parent,
                id,
                args,
                sort,
                mut rec,
            } => {
                rec.push(result);
                if rec.len() >= args.len() {
                    // at this point, all recursions are ready, and therefore we should invoke the recursor
                    result = recursor.on_app(id, args, sort, rec)?;
                    zipper = parent;
                } else {
                    return Ok(Either::Left(Box::new(TermZipper::App {
                        parent,
                        id,
                        args,
                        sort,
                        rec,
                    })));
                }
            }
            TermZipper::LetBindings {
                parent,
                vs,
                body,
                mut vs_rec,
            } => {
                // we are still working on the binder
                let v = &vs[vs_rec.len()];
                let binding = VarBinding(v.0.clone(), v.1, result);
                vs_rec.push(binding);
                if vs_rec.len() >= vs.len() {
                    // now we should swap to the body
                    return Ok(Either::Left(Box::new(TermZipper::LetBody {
                        parent,
                        vs,
                        body,
                        vs_rec,
                    })));
                } else {
                    return Ok(Either::Left(Box::new(TermZipper::LetBindings {
                        parent,
                        vs,
                        body,
                        vs_rec,
                    })));
                }
            }
            TermZipper::LetBody {
                parent,
                vs,
                vs_rec,
                body,
            } => {
                result = recursor.on_let(vs, body, vs_rec, result)?;
                zipper = parent;
            }
            TermZipper::Quantifier {
                parent,
                vs,
                body,
                is_forall,
            } => {
                result = if is_forall {
                    recursor.on_forall(vs, body, result)
                } else {
                    recursor.on_exists(vs, body, result)
                }?;
                zipper = parent;
            }
            TermZipper::MatchScrutinee {
                parent,
                scrutinee,
                cases,
            } => {
                return Ok(Either::Left(Box::new(TermZipper::MatchCases {
                    parent,
                    scrutinee,
                    cases,
                    scrutinee_rec: result,
                    case_rec: vec![],
                })));
            }
            TermZipper::MatchCases {
                parent,
                scrutinee,
                cases,
                scrutinee_rec,
                mut case_rec,
            } => {
                let arm = recursor.on_match_arm(scrutinee, cases, case_rec.len(), result)?;
                case_rec.push(arm);
                if case_rec.len() >= cases.len() {
                    result = recursor.on_match(scrutinee, cases, scrutinee_rec, case_rec)?;
                    zipper = parent;
                } else {
                    return Ok(Either::Left(Box::new(TermZipper::MatchCases {
                        parent,
                        scrutinee,
                        cases,
                        scrutinee_rec,
                        case_rec,
                    })));
                }
            }
            TermZipper::EqL { parent, l, r } => {
                return Ok(Either::Left(Box::new(TermZipper::EqR {
                    parent,
                    l,
                    r,
                    l_rec: result,
                })));
            }
            TermZipper::EqR {
                parent,
                l,
                r,
                l_rec,
            } => {
                result = recursor.on_eq(l, r, l_rec, result)?;
                zipper = parent;
            }
            TermZipper::AnnotatedBody { parent, t, anns } => {
                // Skip leading non-Pattern attributes.
                let mut anns_rec: Vec<Attribute<Str, R::Out>> = vec![];
                advance_attributes_until_pattern(anns, &mut anns_rec);
                if anns_rec.len() >= anns.len() {
                    // No Pattern attributes at all — finalize immediately.
                    result = recursor.on_annotated(t, anns, result, anns_rec)?;
                    zipper = parent;
                } else {
                    return Ok(Either::Left(Box::new(TermZipper::AnnotatedAttrs {
                        parent,
                        t,
                        anns,
                        t_rec: result,
                        anns_rec,
                        cur_pattern_rec: vec![],
                    })));
                }
            }
            TermZipper::AnnotatedAttrs {
                parent,
                t,
                anns,
                t_rec,
                mut anns_rec,
                mut cur_pattern_rec,
            } => {
                // A result just came back from a Pattern sub-term.
                cur_pattern_rec.push(result);
                // Find the current Pattern attribute we're working on.
                let cur_attr = &anns[anns_rec.len()];
                let pat_ts = match cur_attr {
                    Attribute::Pattern(ts) => ts,
                    _ => unreachable!(),
                };
                if cur_pattern_rec.len() >= pat_ts.len() {
                    // This Pattern attribute is done.
                    anns_rec.push(Attribute::Pattern(cur_pattern_rec));
                    cur_pattern_rec = vec![];
                    // Advance through any remaining non-Pattern attributes.
                    advance_attributes_until_pattern(anns, &mut anns_rec);
                    if anns_rec.len() >= anns.len() {
                        result = recursor.on_annotated(t, anns, t_rec, anns_rec)?;
                        zipper = parent;
                    } else {
                        // More Pattern attributes to process.
                        return Ok(Either::Left(Box::new(TermZipper::AnnotatedAttrs {
                            parent,
                            t,
                            anns,
                            t_rec,
                            anns_rec,
                            cur_pattern_rec,
                        })));
                    }
                } else {
                    // More terms in the current Pattern.
                    return Ok(Either::Left(Box::new(TermZipper::AnnotatedAttrs {
                        parent,
                        t,
                        anns,
                        t_rec,
                        anns_rec,
                        cur_pattern_rec,
                    })));
                }
            }
            TermZipper::Nary {
                parent,
                kind,
                ts,
                mut rec,
            } => {
                rec.push(result);
                if rec.len() >= ts.len() {
                    result = match kind {
                        NaryKind::Distinct => recursor.on_distinct(ts, rec)?,
                        NaryKind::And => recursor.on_and(ts, rec)?,
                        NaryKind::Or => recursor.on_or(ts, rec)?,
                        NaryKind::Xor => recursor.on_xor(ts, rec)?,
                    };
                    zipper = parent;
                } else {
                    return Ok(Either::Left(Box::new(TermZipper::Nary {
                        parent,
                        kind,
                        ts,
                        rec,
                    })));
                }
            }
            TermZipper::Not { parent, t } => {
                result = recursor.on_not(t, result)?;
                zipper = parent;
            }
            TermZipper::ImpliesPremises {
                parent,
                ts,
                t,
                mut rec,
            } => {
                rec.push(result);
                if rec.len() >= ts.len() {
                    return Ok(Either::Left(Box::new(TermZipper::ImpliesConclusion {
                        parent,
                        ts,
                        t,
                        ts_rec: rec,
                    })));
                } else {
                    return Ok(Either::Left(Box::new(TermZipper::ImpliesPremises {
                        parent,
                        ts,
                        t,
                        rec,
                    })));
                }
            }
            TermZipper::ImpliesConclusion {
                parent,
                ts,
                t,
                ts_rec,
            } => {
                result = recursor.on_implies(ts, t, &ts_rec, result)?;
                zipper = parent;
            }
            TermZipper::IteB { parent, b, t, e } => {
                return Ok(Either::Left(Box::new(TermZipper::IteT {
                    parent,
                    b,
                    t,
                    e,
                    b_rec: result,
                })));
            }
            TermZipper::IteT {
                parent,
                b,
                t,
                e,
                b_rec,
            } => {
                return Ok(Either::Left(Box::new(TermZipper::IteE {
                    parent,
                    b,
                    t,
                    e,
                    b_rec,
                    t_rec: result,
                })));
            }
            TermZipper::IteE {
                parent,
                b,
                t,
                e,
                b_rec,
                t_rec,
            } => {
                result = recursor.on_ite(b, t, e, b_rec, t_rec, &result)?;
                zipper = parent;
            }
        }
    }
}

/// Determine the next child term to descend into and expand it.
///
/// This is called at the beginning of each step. It inspects the current zipper frame
/// to find the next unprocessed child, invoking `setup_*` callbacks for scoped constructs
/// (`LetBody`, `Quantifier`, `MatchCases`) before descending. The returned zipper will
/// be at a leaf (`Constant`, `Global`, or `Local`), ready for resolution.
fn term_recursion_zipper_next<'a, R, Str, So, T>(
    recursor: &mut R,
    zipper: Box<TermZipper<'a, Str, So, T, R::Out>>,
) -> Result<Box<TermZipper<'a, Str, So, T, R::Out>>, R::Err>
where
    R: TermRecursor<Str, So, T>,
    T: Contains<T: Repr<T = Term<Str, So, T>>>,
{
    let t: Option<&T> = match zipper.as_ref() {
        TermZipper::Root
        | TermZipper::Constant { .. }
        | TermZipper::Global { .. }
        | TermZipper::Local { .. } => None,
        TermZipper::App { args, rec, .. } => Some(&args[rec.len()]),
        TermZipper::LetBindings { vs, vs_rec, .. } => Some(&vs[vs_rec.len()].2),
        TermZipper::LetBody {
            vs, vs_rec, body, ..
        } => {
            recursor.setup_let_scope(vs, body, vs_rec)?;
            Some(body)
        }
        TermZipper::Quantifier { vs, body, .. } => {
            // this branch is not expected to get hit
            recursor.setup_quantifier_scope(vs, body)?;
            Some(body)
        }
        TermZipper::MatchScrutinee { scrutinee, .. } => Some(&scrutinee),
        TermZipper::MatchCases {
            scrutinee,
            cases,
            case_rec,
            scrutinee_rec,
            ..
        } => {
            recursor.setup_match_case_scope(scrutinee, cases, scrutinee_rec, case_rec.len())?;
            Some(&cases[case_rec.len()].body)
        }
        TermZipper::EqL { l, .. } => Some(&l),
        TermZipper::EqR { r, .. } => Some(&r),
        TermZipper::AnnotatedBody { t, .. } => Some(t),
        TermZipper::AnnotatedAttrs {
            anns,
            anns_rec,
            cur_pattern_rec,
            ..
        } => {
            // Find the current Pattern attribute and the next sub-term within it.
            match &anns[anns_rec.len()] {
                Attribute::Pattern(ts) => Some(&ts[cur_pattern_rec.len()]),
                _ => unreachable!(),
            }
        }
        TermZipper::Nary { ts, rec, .. } => Some(&ts[rec.len()]),
        TermZipper::Not { t, .. } => Some(t),
        TermZipper::ImpliesPremises { ts, rec, .. } => Some(&ts[rec.len()]),
        TermZipper::ImpliesConclusion { t, .. } => Some(t),
        TermZipper::IteB { b, .. } => Some(b),
        TermZipper::IteT { t, .. } => Some(t),
        TermZipper::IteE { e, .. } => Some(e),
    };
    if let Some(t) = t {
        term_recursion_zipper_expand(recursor, zipper, t)
    } else {
        Ok(zipper)
    }
}

/// Descend from `t` to its leftmost leaf, pushing a zipper frame for each intermediate node.
///
/// This is a tail-recursive loop: for compound nodes it pushes a frame onto `parent` and
/// moves `t` to the first child. For scoped constructs (`Exists`, `Forall`) it calls
/// `setup_quantifier_scope` before descending. The loop terminates when a leaf is reached,
/// returning a zipper positioned at that leaf.
fn term_recursion_zipper_expand<'a, R, Str: 'a, So: 'a, T>(
    recursor: &mut R,
    mut parent: Box<TermZipper<'a, Str, So, T, R::Out>>,
    mut t: &'a T,
) -> Result<Box<TermZipper<'a, Str, So, T, R::Out>>, R::Err>
where
    R: TermRecursor<Str, So, T>,
    T: Contains<T: Repr<T = Term<Str, So, T>>>,
{
    loop {
        match t.inner().repr() {
            Term::Constant(constant, sort) => {
                return Ok(Box::new(TermZipper::Constant {
                    parent,
                    constant,
                    sort,
                }));
            }
            Term::Global(id, sort) => return Ok(Box::new(TermZipper::Global { parent, id, sort })),
            Term::Local(id) => return Ok(Box::new(TermZipper::Local { parent, id })),
            Term::App(id, args, sort) => {
                parent = Box::new(TermZipper::App {
                    parent,
                    id,
                    args,
                    sort,
                    rec: vec![],
                });
                t = &args[0];
            }
            Term::Let(vs, body) => {
                parent = Box::new(TermZipper::LetBindings {
                    parent,
                    vs,
                    body,
                    vs_rec: vec![],
                });
                t = &vs[0].2;
            }
            Term::Exists(vs, body) => {
                recursor.setup_quantifier_scope(vs, body)?;
                parent = Box::new(TermZipper::Quantifier {
                    parent,
                    vs,
                    body,
                    is_forall: false,
                });
                t = body;
            }
            Term::Forall(vs, body) => {
                recursor.setup_quantifier_scope(vs, body)?;
                parent = Box::new(TermZipper::Quantifier {
                    parent,
                    vs,
                    body,
                    is_forall: true,
                });
                t = body;
            }
            Term::Matching(scrutinee, cases) => {
                parent = Box::new(TermZipper::MatchScrutinee {
                    parent,
                    scrutinee,
                    cases,
                });
                t = &scrutinee;
            }
            Term::Annotated(inner, anns) => {
                parent = Box::new(TermZipper::AnnotatedBody {
                    parent,
                    t: inner,
                    anns,
                });
                t = inner;
            }
            Term::Eq(l, r) => {
                parent = Box::new(TermZipper::EqL { parent, l, r });
                t = l;
            }
            Term::Distinct(ts) => {
                parent = Box::new(TermZipper::Nary {
                    parent,
                    kind: NaryKind::Distinct,
                    ts,
                    rec: vec![],
                });
                t = &ts[0];
            }
            Term::And(ts) => {
                parent = Box::new(TermZipper::Nary {
                    parent,
                    kind: NaryKind::And,
                    ts,
                    rec: vec![],
                });
                t = &ts[0];
            }
            Term::Or(ts) => {
                parent = Box::new(TermZipper::Nary {
                    parent,
                    kind: NaryKind::Or,
                    ts,
                    rec: vec![],
                });
                t = &ts[0];
            }
            Term::Xor(ts) => {
                parent = Box::new(TermZipper::Nary {
                    parent,
                    kind: NaryKind::Xor,
                    ts,
                    rec: vec![],
                });
                t = &ts[0];
            }
            Term::Implies(ts, concl) => {
                parent = Box::new(TermZipper::ImpliesPremises {
                    parent,
                    ts,
                    t: concl,
                    rec: vec![],
                });
                t = &ts[0];
            }
            Term::Not(inner) => {
                parent = Box::new(TermZipper::Not { parent, t: inner });
                t = inner;
            }
            Term::Ite(b, th, e) => {
                parent = Box::new(TermZipper::IteB {
                    parent,
                    b,
                    t: th,
                    e,
                });
                t = b;
            }
        }
    }
}
/// Perform one atomic step: find the next child, expand to a leaf, resolve it, and push.
///
/// Returns `Right(value)` if the entire traversal is complete, or `Left(zipper)` if more
/// children remain to be processed.
fn term_recursion_zip_one_step<'a, R, Str, So, T>(
    recursor: &mut R,
    mut zipper: Box<TermZipper<'a, Str, So, T, R::Out>>,
) -> Result<Either<Box<TermZipper<'a, Str, So, T, R::Out>>, R::Out>, R::Err>
where
    Str: Clone,
    R: TermRecursor<Str, So, T>,
    T: Contains<T: Repr<T = Term<Str, So, T>>>,
{
    zipper = term_recursion_zipper_next(recursor, zipper)?;

    match *zipper {
        TermZipper::Constant {
            parent,
            constant,
            sort,
        } => {
            let result = recursor.on_constant(constant, sort)?;
            term_recursion_zipper_push(recursor, parent, result)
        }
        TermZipper::Global { parent, id, sort } => {
            let result = recursor.on_global(id, sort)?;
            term_recursion_zipper_push(recursor, parent, result)
        }
        TermZipper::Local { parent, id } => {
            let result = recursor.on_local(id)?;
            term_recursion_zipper_push(recursor, parent, result)
        }
        _ => {
            unreachable!()
        }
    }
}

/// Main entry point: iteratively traverse `term` using the zipper and return the final result.
///
/// Initializes the zipper at `Root`, expands to the leftmost leaf, then loops over
/// [`term_recursion_zip_one_step`] until the traversal completes.
fn term_recursion<R, Str, So, T>(recursor: &mut R, term: &T) -> Result<R::Out, R::Err>
where
    Str: Clone,
    R: TermRecursor<Str, So, T>,
    T: Contains<T: Repr<T = Term<Str, So, T>>>,
{
    let mut zipper = Box::new(TermZipper::Root);
    zipper = term_recursion_zipper_expand(recursor, zipper, term)?;
    loop {
        let result = term_recursion_zip_one_step(recursor, zipper)?;
        match result {
            Either::Left(l) => {
                zipper = l;
            }
            Either::Right(r) => {
                return Ok(r);
            }
        }
    }
}
