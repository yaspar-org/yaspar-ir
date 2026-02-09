// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::allocator::LocalVarAllocator;
use crate::ast::alg::VarBinding;
use crate::ast::ctx::{
    Arena, Context, LetContext, QuantifierContext, Result, Sort, Str, Term, TypedApi,
};
use crate::ast::{MatchContext, SymbolQuote};
use crate::locenv::LocEnv;
use crate::raw::instance::HasArena;
use crate::raw::tc::{TCEnv, TC};
use crate::traits::{AllocatableString, Contains};
use std::collections::HashSet;

/// A structure that captures local sort bindings.
///
/// It is not meant to be exposed publicly.
pub(crate) struct LocalContext<'a, 'b> {
    pub(crate) context: &'a mut Context,
    pub(crate) env: Vec<VarBinding<Str, Sort>>,
    pub(crate) tail: LocEnv<'b, Str, Sort>,
}

impl<'a, 'b> LocalContext<'a, 'b> {
    pub(crate) fn new(context: &'a mut Context, tail: LocEnv<'b, Str, Sort>) -> Self {
        Self {
            context,
            env: vec![],
            tail,
        }
    }

    fn sanity_check<S>(&mut self, name: S) -> Result<Str>
    where
        S: AllocatableString<Arena>,
    {
        let symbol = name.allocate(self.arena());
        for v in &self.env {
            if v.0.as_str() == symbol.inner() {
                return Err(format!(
                    "duplicate name in binding: {}{} is already used!",
                    symbol.sym_quote(),
                    name.display_meta_data()
                ));
            }
        }
        Ok(symbol)
    }

    pub(crate) fn extend_impl<S>(&mut self, name: S, sort: Sort) -> Result<usize>
    where
        S: AllocatableString<Arena>,
    {
        let name = self.sanity_check(name)?;
        let id = self.context.new_local();
        self.env.push(VarBinding(name, id, sort));
        Ok(id)
    }

    /// Extends a name-sort binding to the local environment
    pub(crate) fn extend<S>(&mut self, name: S, sort: Sort) -> Result<usize>
    where
        S: AllocatableString<Arena>,
    {
        self.extend_impl(name, sort)
    }

    /// Extends a number of name-osrt bindings
    pub(crate) fn extend_many<T, S>(&mut self, tups: T) -> Result<Vec<usize>>
    where
        T: IntoIterator<Item = (S, Sort)>,
        S: AllocatableString<Arena>,
    {
        let mut bindings = vec![];
        let mut names = HashSet::new();
        let mut ids = vec![];
        for (name, sort) in tups {
            let name = name.allocate(self.arena());
            self.sanity_check(name.as_str())?;
            if !names.insert(name.clone()) {
                return Err(format!(
                    "duplicate name in binding: {} is already used",
                    name.sym_quote()
                ));
            }
            let id = self.context.new_local();
            bindings.push(VarBinding(name, id, sort));
            ids.push(id);
        }
        self.env.extend(bindings);
        Ok(ids)
    }
}

impl HasArena for LocalContext<'_, '_> {
    #[inline]
    fn arena(&mut self) -> &mut Arena {
        self.context.arena()
    }
}

impl TypedApi for LocalContext<'_, '_> {
    fn get_tcenv(&mut self) -> TCEnv<'_, '_, Sort> {
        let theories = self.context.get_theories();
        TCEnv {
            arena: &mut self.context.arena,
            theories,
            sorts: &mut self.context.sorts,
            symbol_table: &self.context.symbol_table,
            local: LocEnv::Cons {
                car: &self.env,
                cdr: &self.tail,
            },
        }
    }

    fn build_quantifier(&mut self) -> TC<QuantifierContext<'_, '_>> {
        QuantifierContext::new(
            self.context,
            LocEnv::Cons {
                car: &self.env,
                cdr: &self.tail,
            },
        )
    }

    fn build_let<T, S>(&mut self, bindings: T) -> TC<LetContext<'_, '_>>
    where
        T: IntoIterator<Item = (S, Term)>,
        S: AllocatableString<Arena>,
    {
        LetContext::new_with_bindings(
            self.context,
            LocEnv::Cons {
                car: &self.env,
                cdr: &self.tail,
            },
            bindings,
        )
    }

    fn build_matching(&mut self, scrutinee: Term) -> TC<MatchContext<'_, '_>> {
        MatchContext::new(
            self.context,
            LocEnv::Cons {
                car: &self.env,
                cdr: &self.tail,
            },
            scrutinee,
        )
    }
}
