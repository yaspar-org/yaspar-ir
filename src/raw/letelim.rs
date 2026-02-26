// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Let-elimination
//!
//! Let-elimination expands all local variables with their bodies if they are introduced by let-bindings.
//!
//! After let-elimination, the resulting term must contain no let-bindings.

use super::alg;
use super::instance::{Arena, Attribute, Pattern, Str, Term};
use crate::allocator::TermAllocator;
use crate::locenv::LocEnv;
use crate::raw::alg::VarBinding;
use crate::traits::Repr;
use std::collections::HashMap;

/// Eliminates all let-bindings by applying substitutions properly
///
/// This trait assumes that the given object has been type-checked.
pub trait LetElim<Env> {
    fn let_elim(&self, env: &mut Env) -> Self;
}

struct LetEnv<'a, 'b> {
    arena: &'a mut Arena,
    cache: &'b mut HashMap<Term, Term>,
    local: &'b LocEnv<'b, Str, Option<Term>>,
    // local env remembers an optional term, because we must consider quantifiers, which do not bind any term
}

impl LetElim<Arena> for Term {
    fn let_elim(&self, env: &mut Arena) -> Self {
        let mut env = LetEnv {
            arena: env,
            cache: &mut HashMap::new(),
            local: &LocEnv::Nil,
        };
        self.let_elim(&mut env)
    }
}

impl<T> LetElim<LetEnv<'_, '_>> for Vec<T>
where
    T: for<'a, 'b> LetElim<LetEnv<'a, 'b>>,
{
    fn let_elim(&self, env: &mut LetEnv<'_, '_>) -> Self {
        self.iter().map(|t| t.let_elim(env)).collect()
    }
}

impl LetElim<LetEnv<'_, '_>> for Attribute {
    fn let_elim(&self, env: &mut LetEnv<'_, '_>) -> Self {
        match self {
            Attribute::Pattern(ts) => Attribute::Pattern(ts.let_elim(env)),
            _ => self.clone(),
        }
    }
}

fn pattern_var_bindings(p: &Pattern) -> Vec<VarBinding<Str, ()>> {
    match p {
        Pattern::Wildcard(head) => head
            .iter()
            .map(|(n, id)| VarBinding(n.clone(), *id, ()))
            .collect(),
        Pattern::Ctor(_) => vec![],
        Pattern::Applied { ctor: _, arguments } => arguments
            .iter()
            .filter_map(|o| o.as_ref().map(|(n, id)| VarBinding(n.clone(), *id, ())))
            .collect(),
    }
}

impl LetElim<LetEnv<'_, '_>> for Term {
    fn let_elim(&self, env: &mut LetEnv) -> Self {
        fn le_binder_body<T>(vs: &[VarBinding<Str, T>], t: &Term, env: &mut LetEnv) -> Term {
            let wrapped = vs
                .iter()
                .map(|v| VarBinding(v.0.clone(), v.1, None))
                .collect::<Vec<_>>();
            let mut ext = LetEnv {
                arena: env.arena,
                cache: env.cache,
                local: &env.local.insert(&wrapped).unwrap(),
            };
            t.let_elim(&mut ext)
        }

        if let Some(r) = env.cache.get(self) {
            return r.clone();
        }

        let r = match self.repr() {
            alg::Term::Constant(_, _) => self.clone(),
            alg::Term::Global(_, _) => self.clone(),
            alg::Term::Local(id) => match env.local.lookup(id.id_str()) {
                None => self.clone(), // when we see None, we know this variable is from a quantifier
                Some((_, None)) => self.clone(),
                Some((_, Some(t))) => t,
            },
            alg::Term::App(qid, ts, s) => {
                let nts = ts.let_elim(env);
                env.arena.app(qid.clone(), nts, s.clone())
            }
            alg::Term::Let(vs, t) => {
                // in this case,
                // 1. we first recurse on the terms bound to variables,
                // 2. then we remember bindings in the local env stack,
                // 3. recuse on the body

                let wrapped = vs
                    .iter()
                    .map(|v| VarBinding(v.0.clone(), v.1, Some(v.2.let_elim(env))))
                    .collect::<Vec<_>>();
                let mut ext = LetEnv {
                    arena: env.arena,
                    cache: env.cache,
                    // it's fine to unwrap here as we assume type-checking has been done
                    local: &env.local.insert(&wrapped).unwrap(),
                };
                t.let_elim(&mut ext)
            }
            alg::Term::Exists(vs, t) => {
                // with quantifiers, we
                // 1. bind each variable to `None`;
                // 2. recurse on the body;
                // 3. rewrap the whole term in the right quantifier.

                let nt = le_binder_body(vs, t, env);
                env.arena.exists(vs.clone(), nt)
            }
            alg::Term::Forall(vs, t) => {
                // same as above

                let nt = le_binder_body(vs, t, env);
                env.arena.forall(vs.clone(), nt)
            }
            alg::Term::Annotated(t, ans) => {
                let nt = t.let_elim(env);
                let nans = ans.let_elim(env);
                env.arena.annotated(nt, nans)
            }
            alg::Term::Eq(a, b) => {
                let na = a.let_elim(env);
                let nb = b.let_elim(env);
                env.arena.eq(na, nb)
            }
            alg::Term::Distinct(ts) => {
                let nts = ts.let_elim(env);
                env.arena.distinct(nts)
            }
            alg::Term::And(ts) => {
                let nts = ts.let_elim(env);
                env.arena.and(nts)
            }
            alg::Term::Or(ts) => {
                let nts = ts.let_elim(env);
                env.arena.or(nts)
            }
            alg::Term::Xor(ts) => {
                let nts = ts.let_elim(env);
                env.arena.xor(nts)
            }
            alg::Term::Not(t) => {
                let nt = t.let_elim(env);
                env.arena.not(nt)
            }
            alg::Term::Implies(ts, rt) => {
                let nts = ts.let_elim(env);
                let nrt = rt.let_elim(env);
                env.arena.implies(nts, nrt)
            }
            alg::Term::Ite(b, t, e) => {
                let nb = b.let_elim(env);
                let nt = t.let_elim(env);
                let ne = e.let_elim(env);
                env.arena.ite(nb, nt, ne)
            }
            alg::Term::Matching(t, cases) => {
                let nt = t.let_elim(env);
                let ncases = cases
                    .iter()
                    .map(|c| alg::PatternArm {
                        pattern: c.pattern.clone(),
                        body: le_binder_body(&pattern_var_bindings(&c.pattern), &c.body, env),
                    })
                    .collect();
                env.arena.matching(nt, ncases)
            }
        };
        env.cache.insert(self.clone(), r.clone());

        r
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Context, Typecheck};
    use crate::untyped::UntypedAst;

    #[test]
    fn test_let_elim1() {
        let mut context = Context::default();
        context.ensure_logic();
        let t = UntypedAst
            .parse_term_str("(let ((x (+ 1 2))) (* x x))")
            .unwrap()
            .type_check(&mut context)
            .unwrap()
            .let_elim(&mut context);
        let equiv = UntypedAst
            .parse_term_str("(* (+ 1 2) (+ 1 2))")
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        assert_eq!(t, equiv);
    }

    #[test]
    fn test_let_elim2() {
        let mut context = Context::default();
        context.ensure_logic();
        let t = UntypedAst
            .parse_term_str("(let ((x (+ 1 2))) (! (* x x) :pattern (x)))")
            .unwrap()
            .type_check(&mut context)
            .unwrap()
            .let_elim(&mut context);
        let equiv = UntypedAst
            .parse_term_str("(! (* (+ 1 2) (+ 1 2)) :pattern ((+ 1 2)))")
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        assert_eq!(t, equiv);
    }

    #[test]
    fn test_let_elim_xor() {
        let mut context = Context::default();
        context.ensure_logic();
        let t = UntypedAst
            .parse_term_str("(let ((p true) (q false)) (xor p q))")
            .unwrap()
            .type_check(&mut context)
            .unwrap()
            .let_elim(&mut context);
        let equiv = UntypedAst
            .parse_term_str("(xor true false)")
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        assert_eq!(t, equiv);
    }
}
