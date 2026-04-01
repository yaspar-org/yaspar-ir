// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::ast::Repr;
use crate::raw::alg::*;

enum Either<A, B> {
    Left(A),
    Right(B),
}

pub trait TermRecursor<Str, So, T> {
    type Out;
    type Err;

    fn on_constant(
        &mut self,
        constant: &Constant<Str>,
        sort: &Option<So>,
    ) -> Result<Self::Out, Self::Err>;
    fn on_global(
        &mut self,
        id: &QualifiedIdentifier<Str, So>,
        sort: &Option<So>,
    ) -> Result<Self::Out, Self::Err>;
    fn on_local(&mut self, id: &Local<Str, So>) -> Result<Self::Out, Self::Err>;
    fn on_app(
        &mut self,
        id: &QualifiedIdentifier<Str, So>,
        ts: &[T],
        s: &Option<So>,
        recs: Vec<Self::Out>,
    ) -> Result<Self::Out, Self::Err>;

    fn setup_let_scope(
        &mut self,
        vs: &[VarBinding<Str, T>],
        body: &T,
        vs_rec: Vec<VarBinding<Str, Self::Out>>,
    ) -> Result<(), Self::Err>;

    fn on_let(
        &mut self,
        vs: &[VarBinding<Str, T>],
        body: &T,
        body_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err>;

    fn setup_quantifier_scope(
        &mut self,
        vs: &[VarBinding<Str, So>],
        t: &T,
    ) -> Result<(), Self::Err>;
    fn on_exists(
        &mut self,
        vs: &[VarBinding<Str, So>],
        t: &T,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err>;
    fn on_forall(
        &mut self,
        vs: &[VarBinding<Str, So>],
        t: &T,
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err>;

    fn setup_match_case_scope(
        &mut self,
        scrutinee: &T,
        cases: &[PatternArm<Str, T>],
        case_idx: usize,
    ) -> Result<(), Self::Err>;
    fn on_match_arm(
        &mut self,
        scrutinee: &T,
        cases: &[PatternArm<Str, T>],
        case_idx: usize,
        arm: Self::Out,
    ) -> Result<Self::Out, Self::Err>;
    fn on_match(
        &mut self,
        scrutinee: &T,
        cases: &[PatternArm<Str, T>],
        scrutinee_rec: Self::Out,
        cases_rec: Vec<PatternArm<Str, Self::Out>>,
    ) -> Result<Self::Out, Self::Err>;
    fn on_annotated(
        &mut self,
        t: &T,
        anns: &[Attribute<Str, T>],
        t_rec: Self::Out,
        anns_rec: Vec<Attribute<Str, Self::Out>>,
    ) -> Result<Self::Out, Self::Err>;
    fn on_eq(
        &mut self,
        a: &T,
        b: &T,
        a_rec: Self::Out,
        b_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err>;
    fn on_distinct(&mut self, ts: &[T], ts_rec: Vec<Self::Out>) -> Result<Self::Out, Self::Err>;
    fn on_and(&mut self, ts: &[T], ts_rec: Vec<Self::Out>) -> Result<Self::Out, Self::Err>;
    fn on_or(&mut self, ts: &[T], ts_rec: Vec<Self::Out>) -> Result<Self::Out, Self::Err>;
    fn on_xor(&mut self, ts: &[T], ts_rec: Vec<Self::Out>) -> Result<Self::Out, Self::Err>;
    fn on_not(&mut self, t: &T, t_rec: Self::Out) -> Result<Self::Out, Self::Err>;
    fn on_implies(
        &mut self,
        ts: &[T],
        t: &T,
        ts_rec: &[Self::Out],
        t_rec: Self::Out,
    ) -> Result<Self::Out, Self::Err>;
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

enum TermZipper<'a, Str, So, T, Out> {
    Root,
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
    App {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        id: &'a QualifiedIdentifier<Str, So>,
        args: &'a [T],
        sort: &'a Option<So>,
        rec: Vec<Out>,
    },
    LetBindings {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        vs: &'a [VarBinding<Str, T>],
        body: &'a T,
        vs_rec: Vec<VarBinding<Str, Out>>,
    },
    LetBody {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        vs: &'a [VarBinding<Str, T>],
        body: &'a T,
    },
    Quantifier {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        vs: &'a [VarBinding<Str, So>],
        body: &'a T,
        is_forall: bool,
    },
}

impl<'a, Str, So, T, Out> TermZipper<'a, Str, So, T, Out> {
    fn next_term(&self) -> Option<&Term<Str, So, T>> {
        match self {
            TermZipper::Root
            | TermZipper::Constant { .. }
            | TermZipper::Global { .. }
            | TermZipper::Local { .. } => None,
            TermZipper::App { args, rec, .. } => Some(&args[rec.len()]),
            TermZipper::LetBindings { vs, vs_rec, .. } => Some(&vs[vs_rec.len()]),
            TermZipper::LetBody { body, .. } => Some(body),
            TermZipper::Quantifier { body, .. } => Some(body),
        }
    }
}

fn term_recursion_zipper_push<'a, R, Str, So, T>(
    r: &mut R,
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
                    result = r.on_app(id, args, sort, rec)?;
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
                    r.setup_let_scope(vs, body, vs_rec)?;
                    return Ok(Either::Left(Box::new(TermZipper::LetBody {
                        parent,
                        vs,
                        body,
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
            TermZipper::LetBody { parent, vs, body } => {
                zipper = parent;
                result = r.on_let(vs, body, result)?;
            }
            TermZipper::Quantifier {
                parent,
                vs,
                body,
                is_forall,
            } => {
                r.setup_quantifier_scope(vs, body)?;
                result = if is_forall {
                    r.on_forall(vs, body, result)
                } else {
                    r.on_exists(vs, body, result)
                }?;
                zipper = parent;
            }
        }
    }
}

fn term_recursion_zipper_expand<'a, R, Str, So, T>(
    mut parent: Box<TermZipper<'a, Str, So, T, R::Out>>,
    mut t: &T,
) -> Box<TermZipper<'a, Str, So, T, R::Out>>
where
    // Str: Clone,
    R: TermRecursor<Str, So, T>,
    T: Contains<T: Repr<T = Term<Str, So, T>>>,
{
    loop {
        match t.inner().repr() {
            Term::Constant(constant, sort) => {
                return Box::new(TermZipper::Constant {
                    parent,
                    constant,
                    sort,
                });
            }
            Term::Global(id, sort) => return Box::new(TermZipper::Global { parent, id, sort }),
            Term::Local(id) => return Box::new(TermZipper::Local { parent, id }),
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
                parent = Box::new(TermZipper::Quantifier {
                    parent,
                    vs,
                    body,
                    is_forall: false,
                });
                t = body;
            }
            Term::Forall(vs, body) => {
                parent = Box::new(TermZipper::Quantifier {
                    parent,
                    vs,
                    body,
                    is_forall: true,
                });
                t = body;
            }
            Term::Matching(_, _) => {}
            Term::Annotated(_, _) => {}
            Term::Eq(_, _) => {}
            Term::Distinct(_) => {}
            Term::And(_) => {}
            Term::Or(_) => {}
            Term::Xor(_) => {}
            Term::Implies(_, _) => {}
            Term::Not(_) => {}
            Term::Ite(_, _, _) => {}
        }
    }
}
fn term_recursion_zip_one_step<'a, R, Str, So, T>(
    r: &mut R,
    mut zipper: Box<TermZipper<'a, Str, So, T, R::Out>>,
) -> Result<Either<Box<TermZipper<'a, Str, So, T, R::Out>>, R::Out>, R::Err>
where
    Str: Clone,
    R: TermRecursor<Str, So, T>,
    T: Contains<T: Repr<T = Term<Str, So, T>>>,
{
    let next = zipper.next_term();
    if let Some(t) = next {
        zipper = term_recursion_zipper_expand(zipper, t);
    }

    match *zipper {
        TermZipper::Constant {
            parent,
            constant,
            sort,
        } => {
            let result = r.on_constant(constant, sort)?;
            term_recursion_zipper_push(r, parent, result)
        }
        TermZipper::Global { parent, id, sort } => {
            let result = r.on_global(id, sort)?;
            term_recursion_zipper_push(r, parent, result)
        }
        TermZipper::Local { parent, id } => {
            let result = r.on_local(id)?;
            term_recursion_zipper_push(r, parent, result)
        }
        _ => {
            unreachable!()
        }
    }
}

fn term_recursion<R, Str, So, T>(r: &mut R, term: &T) -> Result<R::Out, R::Err>
where
    Str: Clone,
    R: TermRecursor<Str, So, T>,
    T: Contains<T: Repr<T = Term<Str, So, T>>>,
{
    let mut zipper = Box::new(TermZipper::Root);
    zipper = term_recursion_zipper_expand(zipper, term);
    loop {
        let result = term_recursion_zip_one_step(r, zipper)?;
        match result {
            Either::Left(l) => {
                zipper = l;
            }
            Either::Right(r) => {
                return r;
            }
        }
    }
}
