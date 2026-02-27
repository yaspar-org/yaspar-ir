// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::allocator::{CommandAllocator, LocalVarAllocator};
use crate::ast::alg::VarBinding;
use crate::ast::ctx::bindings::LetContext;
use crate::ast::ctx::matching::MatchContext;
use crate::ast::ctx::quantifier::QuantifierContext;
use crate::ast::ctx::{Arena, CheckedApi, Context, FetchSort, SymbolQuote, TCEnv};
use crate::ast::ctx::{Command, FunctionDef, Sort, Str, TC, Term};
use crate::locenv::{LocEnv, sanitize_bindings};
use crate::raw::instance::HasArena;
use crate::traits::AllocatableString;
use std::collections::HashSet;

/// It is a builder context for building non-recursive functions
///
/// c.f. [FunctionContext::typed_define_fun]
pub struct FunctionContext<'a> {
    context: &'a mut Context,
    name: Str,
    inputs: Vec<VarBinding<Str, Sort>>,
    output: Option<Sort>,
}

impl<'a> FunctionContext<'a> {
    pub(crate) fn new<T, S>(
        context: &'a mut Context,
        name: S,
        inputs: T,
        output: Option<Sort>,
    ) -> TC<Self>
    where
        T: IntoIterator<Item = (S, Sort)>,
        S: AllocatableString<Arena>,
    {
        context.check_logic()?;
        let symbol = name.allocate(context.arena());
        context.can_add_symbol(&symbol).map_err(|_| {
            format!(
                "symbol {}{} cannot be added to the symbol table!",
                symbol.sym_quote(),
                name.display_meta_data()
            )
        })?;
        let inputs = inputs
            .into_iter()
            .map(|(s, so)| {
                let s = s.allocate(context.arena());
                let id = context.new_local();
                VarBinding(s, id, so)
            })
            .collect::<Vec<_>>();
        sanitize_bindings(&inputs, |v| v.0.clone())?;
        Ok(Self {
            context,
            name: symbol,
            inputs,
            output,
        })
    }

    /// Create the function with the given body
    pub fn typed_define_fun(self, body: Term) -> TC<Command> {
        let sort = body.get_sort(self.context);
        if let Some(s) = self.output.as_ref()
            && sort != *s
        {
            return Err(format!(
                "TC: function {} is declared to have sort {s} but is checked to have sort {sort}!",
                self.name.sym_quote(),
            ));
        }
        let def = FunctionDef {
            name: self.name,
            vars: self.inputs,
            out_sort: sort,
            body,
        };
        self.context
            .insert_symbol_with_def(HashSet::new(), def.clone());
        Ok(self.context.define_fun(def))
    }
}

impl HasArena for FunctionContext<'_> {
    #[inline]
    fn arena(&mut self) -> &mut Arena {
        self.context.arena()
    }
}

impl CheckedApi for FunctionContext<'_> {
    fn get_tcenv(&mut self) -> TCEnv<'_, '_, Sort> {
        let theories = self.context.get_theories();
        TCEnv {
            arena: &mut self.context.arena,
            theories,
            sorts: &mut self.context.sorts,
            symbol_table: &self.context.symbol_table,
            local: LocEnv::Cons {
                car: &self.inputs,
                cdr: &LocEnv::Nil,
            },
        }
    }

    fn build_quantifier(&mut self) -> TC<QuantifierContext<'_, '_>> {
        QuantifierContext::new(
            self.context,
            LocEnv::Cons {
                car: &self.inputs,
                cdr: &LocEnv::Nil,
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
                car: &self.inputs,
                cdr: &LocEnv::Nil,
            },
            bindings,
        )
    }

    fn build_matching(&mut self, scrutinee: Term) -> TC<MatchContext<'_, '_>> {
        MatchContext::new(
            self.context,
            LocEnv::Cons {
                car: &self.inputs,
                cdr: &LocEnv::Nil,
            },
            scrutinee,
        )
    }
}
