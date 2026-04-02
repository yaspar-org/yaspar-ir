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

    fn recurse_on_term(&mut self, t: &T) -> Result<Self::Out, Self::Err>
    where
        Self: Sized,
        Str: Clone,
        T: Contains<T: Repr<T = Term<Str, So, T>>>,
    {
        term_recursion(self, t)
    }

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
        vs_rec: &[VarBinding<Str, Self::Out>],
    ) -> Result<(), Self::Err>;

    fn on_let(
        &mut self,
        vs: &[VarBinding<Str, T>],
        body: &T,
        vs_rec: Vec<VarBinding<Str, Self::Out>>,
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
        scrutinee_rec: &Self::Out,
        case_idx: usize,
    ) -> Result<(), Self::Err>;
    fn on_match_arm(
        &mut self,
        scrutinee: &T,
        cases: &[PatternArm<Str, T>],
        case_idx: usize,
        arm: Self::Out,
    ) -> Result<PatternArm<Str, Self::Out>, Self::Err>;
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
        vs_rec: Vec<VarBinding<Str, Out>>,
        body: &'a T,
    },
    Quantifier {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        vs: &'a [VarBinding<Str, So>],
        body: &'a T,
        is_forall: bool,
    },
    MatchScrutinee {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        scrutinee: &'a T,
        cases: &'a [PatternArm<Str, T>],
    },
    MatchCases {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        scrutinee: &'a T,
        cases: &'a [PatternArm<Str, T>],
        scrutinee_rec: Out,
        case_rec: Vec<PatternArm<Str, Out>>,
    },
    EqL {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        l: &'a T,
        r: &'a T,
    },
    EqR {
        parent: Box<TermZipper<'a, Str, So, T, Out>>,
        l: &'a T,
        r: &'a T,
        l_rec: Out,
    },
}

impl<'a, Str, So, T, Out> TermZipper<'a, Str, So, T, Out> {
    fn next_term(&self) -> Option<&T> {
        match self {
            TermZipper::Root
            | TermZipper::Constant { .. }
            | TermZipper::Global { .. }
            | TermZipper::Local { .. } => None,
            TermZipper::App { args, rec, .. } => Some(&args[rec.len()]),
            TermZipper::LetBindings { vs, vs_rec, .. } => Some(&vs[vs_rec.len()].2),
            TermZipper::LetBody { body, .. } => Some(body),
            TermZipper::Quantifier { body, .. } => Some(body),
            TermZipper::MatchScrutinee { scrutinee, .. } => Some(&scrutinee),
            TermZipper::MatchCases {
                cases, case_rec, ..
            } => Some(&cases[case_rec.len()].body),
            TermZipper::EqL { l, .. } => Some(&l),
            TermZipper::EqR { r, .. } => Some(&r),
        }
    }
}

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
        }
    }
}

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
    };
    if let Some(t) = t {
        term_recursion_zipper_expand(recursor, zipper, t)
    } else {
        Ok(zipper)
    }
}

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
            Term::Annotated(_, _) => {}
            Term::Eq(l, r) => {
                parent = Box::new(TermZipper::EqL { parent, l, r });
                t = l;
            }
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
