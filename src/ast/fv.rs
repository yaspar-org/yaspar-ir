//! This module compute the set of free variables of a term

use crate::ast::{ATerm, Pattern, Str, Term};
use crate::traits::Repr;
use std::collections::HashSet;

/// obtain the free variables of a term
pub trait FreeLocalVars {
    fn free_loc_vars(&self) -> HashSet<Str>;
}

impl FreeLocalVars for Term {
    fn free_loc_vars(&self) -> HashSet<Str> {
        match self.repr() {
            ATerm::Constant(_, _) | ATerm::Global(_, _) => HashSet::new(),
            ATerm::Local(l) => {
                let mut set = HashSet::new();
                set.insert(l.symbol.clone());
                set
            }
            ATerm::App(_, ts, _) | ATerm::Distinct(ts) | ATerm::And(ts) | ATerm::Or(ts) => {
                ts.iter().flat_map(|t| t.free_loc_vars()).collect()
            }
            ATerm::Let(vs, t) => free_loc_vars_handle_binders(vs, t, |v| &v.0),
            ATerm::Exists(vs, t) | ATerm::Forall(vs, t) => {
                free_loc_vars_handle_binders(vs, t, |v| &v.0)
            }
            ATerm::Annotated(t, _) | ATerm::Not(t) => t.free_loc_vars(),
            ATerm::Eq(a, b) => {
                let mut s = a.free_loc_vars();
                s.extend(b.free_loc_vars());
                s
            }
            ATerm::Implies(ts, r) => {
                let mut s1 = ts
                    .iter()
                    .flat_map(|t| t.free_loc_vars())
                    .collect::<HashSet<_>>();
                let s2 = r.free_loc_vars();
                s1.extend(s2);
                s1
            }
            ATerm::Ite(b, t, e) => {
                let mut s = b.free_loc_vars();
                s.extend(e.free_loc_vars());
                s.extend(t.free_loc_vars());
                s
            }
            ATerm::Matching(t, cases) => {
                let mut s1 = t.free_loc_vars();
                for case in cases {
                    let s2 = free_loc_vars_handle_binders(
                        &pattern_vars(&case.pattern),
                        &case.body,
                        |x| x,
                    );
                    s1.extend(s2);
                }
                s1
            }
        }
    }
}

fn pattern_vars(pat: &Pattern) -> Vec<Str> {
    pat.variables().into_iter().cloned().collect()
}

fn free_loc_vars_handle_binders<T>(vs: &[T], t: &Term, f: impl Fn(&T) -> &Str) -> HashSet<Str> {
    let mut free_vars = t.free_loc_vars();
    for v in vs {
        free_vars.remove(f(v));
    }
    free_vars
}

/// check whether a term is closed; i.e. no open local variables
pub fn is_closed(t: &Term) -> bool {
    t.free_loc_vars().is_empty()
}
