use crate::allocator::{LocalVarAllocator, TermAllocator};
use crate::ast::alg::VarBinding;
use crate::ast::ctx::Context;
use crate::ast::ctx::{
    Arena, LetContext, Pattern, PatternArm, QuantifierContext, Sort, Str, TCEnv, Term, TypedApi, TC,
};
use crate::ast::{SymbolQuote, Theory};
use crate::locenv::LocEnv;
use crate::raw::instance::{FetchSort, HasArena};
use crate::raw::tc::{sort_mismatch, tc_determine_datatype_sort_map};
use crate::traits::AllocatableString;
use std::collections::{HashMap, HashSet};

/// It's a builder context for building a match expression
///
/// c.f. [MatchContext::build_arm] and [MatchContext::typed_matching]
pub struct MatchContext<'a, 'b> {
    context: &'a mut Context,
    tail: LocEnv<'b, Str, Sort>,
    scrutinee: Term,
    constructors: HashMap<Str, Vec<Sort>>,
    unseen_constructors: HashSet<Str>,
    covered: bool,
    arms: Vec<PatternArm>,
    arm_sort: Option<Sort>,
}

/// It's a builder context for building an individual arm in a match expression
///
/// c.f. [ArmContext::typed_arm]
pub struct ArmContext<'a, 'b, 'c> {
    parent: &'c mut MatchContext<'a, 'b>,
    env: Vec<VarBinding<Str, Sort>>,
    pattern: Pattern,
}

impl<'a, 'b> MatchContext<'a, 'b> {
    pub(crate) fn new(
        context: &'a mut Context,
        tail: LocEnv<'b, Str, Sort>,
        scrutinee: Term,
    ) -> TC<Self> {
        context.check_support_theory(Theory::Datatypes)?;
        let mut env = context.get_tcenv();
        let constructors = tc_determine_datatype_sort_map(&mut env, &scrutinee, "")?;
        let unseen_constructors: HashSet<Str> = constructors.keys().cloned().collect();

        Ok(Self {
            context,
            tail,
            scrutinee,
            constructors,
            unseen_constructors,
            covered: false,
            arms: vec![],
            arm_sort: None,
        })
    }

    /// Return a reference to the scrutinee
    pub fn scrutinee(&self) -> &Term {
        &self.scrutinee
    }

    /// Get the sort of the scrutinee
    pub fn scrutinee_sort(&mut self) -> Sort {
        self.scrutinee.get_sort(self.context)
    }

    /// Get the sorts of a given constructor, if it is one
    pub fn get_constructor_sorts<S>(&mut self, ctor: &S) -> Option<&[Sort]>
    where
        S: AllocatableString<Arena>,
    {
        let ctor = ctor.allocate(self.context.arena());
        self.constructors.get(&ctor).map(|x| x.as_slice())
    }

    /// Get all constructors, including the unseen ones
    pub fn get_constructors(&self) -> Vec<Str> {
        self.constructors.keys().cloned().collect()
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
        &self.unseen_constructors
    }

    /// Whether the current context is already covered
    pub fn is_covered(&self) -> bool {
        self.covered
    }

    /// Given a constructor name and a list of variables, return a builder context for the body
    /// of that arm.
    ///
    /// The list of variables must have the same length as required by the constructor.
    ///
    /// The sorts of the variables are inferred from the constructor.
    ///
    /// c.f. [Self::build_arm_wildcard], [Self::build_arm_nullary], [Self::build_arm_catchall]
    pub fn build_arm<'c, T, S>(&'c mut self, c: S, vars: T) -> TC<ArmContext<'a, 'b, 'c>>
    where
        T: IntoIterator<Item = Option<S>>,
        S: AllocatableString<Arena>,
    {
        let ctor = c.allocate(self.context.arena());
        let sorts = match self.constructors.get(&ctor) {
            None => {
                let sort = self.scrutinee_sort();
                return Err(format!(
                    "TC: given name {}{} is not a constructor of sort {sort}",
                    ctor.sym_quote(),
                    c.display_meta_data(),
                ));
            }
            Some(ss) => ss,
        };
        let expected_num_args = sorts.len();
        let mut idx = 0;
        let mut env = vec![];

        let mut arguments = vec![];
        let mut existing_vars = HashSet::new();
        for v in vars {
            if idx == expected_num_args {
                return Err(format!(
                    "TC: constructor {}{} expects {expected_num_args} argument(s) but more are given!",
                    ctor.sym_quote(),
                    c.display_meta_data()
                ));
            }
            if let Some(x) = v {
                let v = x.allocate(self.context.arena());
                if !existing_vars.insert(v.clone()) {
                    return Err(format!(
                        "duplicate name in binding: {}{} is already used",
                        v.sym_quote(),
                        x.display_meta_data()
                    ));
                }
                let new_id = self.context.new_local();
                arguments.push(Some((v.clone(), new_id)));
                env.push(VarBinding(v, new_id, sorts[idx].clone()));
            } else {
                arguments.push(None);
            }
            idx += 1;
        }
        if idx != expected_num_args {
            return Err(format!(
                "TC: constructor {}{} expects {expected_num_args} argument(s) but only {idx} are given!",
                ctor.sym_quote(),
                c.display_meta_data(),
            ));
        }
        Ok(ArmContext {
            parent: self,
            env,
            pattern: if arguments.is_empty() {
                Pattern::Ctor(ctor)
            } else {
                Pattern::Applied { ctor, arguments }
            },
        })
    }

    /// Return a builder context for an arm of a nullary constructor
    ///
    /// c.f. [Self::build_arm]
    pub fn build_arm_nullary<'c, S>(&'c mut self, ctor: S) -> TC<ArmContext<'a, 'b, 'c>>
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
    pub fn build_arm_wildcard<'c, S>(&'c mut self, var: Option<S>) -> TC<ArmContext<'a, 'b, 'c>>
    where
        S: AllocatableString<Arena>,
    {
        if let Some(var) = var {
            let v = var.allocate(self.context.arena());
            if self.constructors.contains_key(&v) {
                Err(format!(
                    "TC: variable {}{} is a constructor; it cannot be used as a wildcard variable for matching a term of sort {}!",
                    v.sym_quote(),
                    var.display_meta_data(),
                    self.scrutinee_sort()
                ))
            } else {
                let id = self.context.new_local();
                let sort = self.scrutinee_sort();
                Ok(ArmContext {
                    parent: self,
                    env: vec![VarBinding(v.clone(), id, sort)],
                    pattern: Pattern::Wildcard(Some((v, id))),
                })
            }
        } else {
            Ok(ArmContext {
                parent: self,
                env: vec![],
                pattern: Pattern::Wildcard(None),
            })
        }
    }

    /// A case of `_`
    ///
    /// c.f. [Self::build_arm_wildcard] and [Self::build_arm]
    pub fn build_arm_catchall<'c>(&'c mut self) -> ArmContext<'a, 'b, 'c> {
        // we unwrap because we know it won't fail
        self.build_arm_wildcard::<String>(None).unwrap()
    }

    /// Build a match expression if the builder context is covered
    ///
    /// c.f. [Self::is_covered]
    pub fn typed_matching(self) -> TC<Term> {
        if !self.covered {
            Err(format!(
                "TC: arms for constructors {} are needed!",
                self.unseen_constructors
                    .iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ))
        } else {
            Ok(self.context.matching(self.scrutinee, self.arms))
        }
    }
}

impl ArmContext<'_, '_, '_> {
    /// finalize the arm by giving a body
    ///
    /// invoking this method will make the parent [MatchContext] available.
    pub fn typed_arm(self, body: Term) -> TC<()> {
        let sort = body.get_sort(self.parent.context);
        if let Some(s) = &self.parent.arm_sort {
            if *s != sort {
                return sort_mismatch(s, &sort, body, "");
            }
        } else {
            self.parent.arm_sort = Some(sort);
        }

        match &self.pattern {
            Pattern::Wildcard(_) => {
                // in the wildcard case, we are already covered
                self.parent.covered = true;
            }
            Pattern::Ctor(ctor) | Pattern::Applied { ctor, .. } => {
                self.parent.unseen_constructors.remove(ctor);
            }
        }

        if self.parent.unseen_constructors.is_empty() {
            self.parent.covered = true;
        }
        let arm = PatternArm {
            pattern: self.pattern,
            body,
        };
        self.parent.arms.push(arm);
        Ok(())
    }
}

impl HasArena for ArmContext<'_, '_, '_> {
    fn arena(&mut self) -> &mut Arena {
        self.parent.context.arena()
    }
}

impl TypedApi for ArmContext<'_, '_, '_> {
    fn get_tcenv(&mut self) -> TCEnv<'_, '_, Sort> {
        let theories = self.parent.context.get_theories();
        TCEnv {
            arena: &mut self.parent.context.arena,
            theories,
            sorts: &mut self.parent.context.sorts,
            symbol_table: &self.parent.context.symbol_table,
            local: LocEnv::Cons {
                car: &self.env,
                cdr: &self.parent.tail,
            },
        }
    }

    fn build_quantifier(&mut self) -> TC<QuantifierContext<'_, '_>> {
        QuantifierContext::new(
            self.parent.context,
            LocEnv::Cons {
                car: &self.env,
                cdr: &self.parent.tail,
            },
        )
    }

    fn build_let<T, S>(&mut self, bindings: T) -> TC<LetContext<'_, '_>>
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

    fn build_matching(&mut self, scrutinee: Term) -> TC<MatchContext<'_, '_>> {
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
