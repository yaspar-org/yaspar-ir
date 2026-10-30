// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::allocator::CommandAllocator;
use crate::ast::alg::VarBinding;
use crate::ast::ctx::{Arena, Context, TCEnv};
use crate::ast::ctx::{Command, Sort, Str, TC};
use crate::ast::ctx::{DEFAULT_DIALECT, Dialect};
use crate::ast::{ScopedSortApi, SymbolQuote};
use crate::containers::{LocEnv, sanitize_bindings};
use crate::raw::instance::HasArena;
use crate::traits::{AllocatableString, HasMutRef};

/// A builder context for defining a sort alias (`define-sort`).
///
/// Created via [`Context::build_sort_alias`]. Sort parameters are in scope and can be
/// referenced via [`ScopedSortApi::wf_sort`]. Finalize with
/// [`typed_define_sort`](Self::typed_define_sort), which registers the alias in the global
/// context and returns the `define-sort` command.
///
/// # Example
///
/// ```rust
/// use yaspar_ir::ast::{CheckedApi, Context, ObjectAllocatorExt, ScopedSortApi};
///
/// let mut context = Context::new();
/// context.ensure_logic();
/// let int = context.wf_sort("Int").unwrap();
/// let s_ctx = context.build_sort_alias("MyInt", Vec::<&str>::new()).unwrap();
/// let cmd = s_ctx.typed_define_sort(int).unwrap();
/// assert_eq!(cmd.to_string(), "(define-sort MyInt () Int)");
/// ```
pub struct DefSortContext<'a, const D: Dialect = DEFAULT_DIALECT> {
    context: &'a mut Context<D>,
    name: Str,
    params: Vec<VarBinding<Str, ()>>,
}

impl<'a, const D: Dialect> DefSortContext<'a, D> {
    pub(crate) fn new<S>(
        context: &'a mut Context<D>,
        name: S,
        params: impl IntoIterator<Item = S>,
    ) -> TC<Self>
    where
        S: AllocatableString<Arena>,
    {
        context.check_logic()?;
        let symbol = name.allocate(context.arena());
        context.can_add_sort(&symbol).map_err(|_| {
            format!(
                "sort {}{} cannot be added to the symbol table!",
                symbol.sym_quote(),
                name.display_meta_data()
            )
        })?;
        let params = params
            .into_iter()
            .map(|s| {
                let s = s.allocate(context.arena());
                VarBinding(s, 0, ())
            })
            .collect::<Vec<_>>();
        sanitize_bindings(&params, |v| v.0.clone())?;
        Ok(Self {
            context,
            name: symbol,
            params,
        })
    }

    /// Consume the given context, update the global context and return a command of `define-sort`
    pub fn typed_define_sort(self, sort: Sort) -> TC<Command> {
        let params = self.params.into_iter().map(|v| v.0).collect::<Vec<_>>();
        self.context
            .def_sort(self.name.clone(), params.clone(), sort.clone())?;
        Ok(self.context.define_sort(self.name, params, sort))
    }
}

impl<const D: Dialect> HasArena for DefSortContext<'_, D> {
    fn arena(&mut self) -> &mut Arena {
        self.context.arena()
    }
}

impl<const D: Dialect> HasMutRef<Context<D>> for DefSortContext<'_, D> {
    type RefMut<'a>
        = &'a mut Context<D>
    where
        Self: 'a;

    #[inline]
    fn ref_mut(&mut self) -> Self::RefMut<'_> {
        self.context
    }
}

impl<const D: Dialect> ScopedSortApi<D> for DefSortContext<'_, D> {
    fn get_sort_tcenv(&mut self) -> TCEnv<'_, '_, (), D> {
        self.context
            .get_sort_tcenv()
            .convert_to_new_local(LocEnv::Cons {
                car: &self.params,
                cdr: &LocEnv::Nil,
            })
    }
}
