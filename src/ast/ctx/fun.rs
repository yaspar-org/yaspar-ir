// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::allocator::{CommandAllocator, LocalVarAllocator};
use crate::ast::alg::VarBinding;
use crate::ast::ctx::bindings::LetContext;
use crate::ast::ctx::matching::MatchContext;
use crate::ast::ctx::quantifier::QuantifierContext;
use crate::ast::ctx::{
    Arena, CheckedApi, Context, FetchSort, SymbolQuote, TCEnv, TCEnvGen, TCLocal,
};
use crate::ast::ctx::{Command, FunctionDef, Sort, Str, TC, Term};
use crate::containers::{LocEnv, sanitize_bindings};
use crate::raw::instance::HasArena;
use crate::traits::AllocatableString;
use std::collections::HashSet;

/// A builder context for constructing non-recursive function definitions (`define-fun`).
///
/// Created via [`Context::build_fun`] or [`Context::build_fun_out_sort`]. The function's
/// parameter names and sorts are provided at creation time and are available as local variables
/// inside this context.
///
/// Build the function body using any [`CheckedApi`] method, then finalize with
/// [`typed_define_fun`](Self::typed_define_fun), which validates the body sort (against the
/// declared output sort, if one was provided), registers the function in the global context,
/// and returns the `define-fun` command.
///
/// # Example
///
/// ```rust
/// use yaspar_ir::ast::{CheckedApi, Context, ScopedSortApi};
///
/// let mut context = Context::new();
/// context.ensure_logic();
/// let int = context.wf_sort("Int").unwrap();
/// let mut f = context.build_fun_out_sort("double", [("x", int.clone())], int).unwrap();
/// let x = f.typed_symbol("x").unwrap();
/// let body = f.typed_simp_app("+", [x.clone(), x]).unwrap();
/// let cmd = f.typed_define_fun(body).unwrap();
/// assert_eq!(cmd.to_string(), "(define-fun double ((x Int)) Int (+ x x))");
/// ```
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
            sort_params: vec![],
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
        TCEnvGen {
            arena: &mut self.context.arena,
            meta: &self.context.meta,
            frame: &self.context.frame,
            local: TCLocal {
                loc: LocEnv::Cons {
                    car: &self.inputs,
                    cdr: &LocEnv::Nil,
                },
                ..Default::default()
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
