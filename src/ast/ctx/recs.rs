// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Module for APIs for defining recursive functions

use crate::allocator::{CommandAllocator, LocalVarAllocator};
use crate::ast::alg::VarBinding;
use crate::ast::ctx::checked::TypedApi;
use crate::ast::ctx::{Arena, Command, Context, FunctionDef, HasArena, Sig, Sort, Str, TCEnv, TC};
use crate::ast::{FetchSort, LetContext, MatchContext, QuantifierContext, SymbolQuote, Term};
use crate::locenv::{sanitize_bindings, LocEnv};
use crate::traits::AllocatableString;
use std::collections::{HashMap, HashSet};

/// A signature of a recursive function
pub struct RecFunc<S, So> {
    /// The name of the function
    name: S,
    /// The input names and sorts of the function
    inputs: Vec<(S, So)>,
    /// The output sort of the function
    output: So,
}

impl<S, So> RecFunc<S, So> {
    /// A convenient builder for [Self]
    pub fn new<T>(name: S, inputs: T, output: So) -> RecFunc<S, So>
    where
        T: IntoIterator<Item = (S, So)>,
    {
        Self {
            name,
            inputs: inputs.into_iter().collect(),
            output,
        }
    }
}

struct RecFunsDefs {
    new_funs: Vec<Str>,
    fun_defs: HashMap<Str, FunctionDef>,
    sigs: HashMap<Str, (Vec<VarBinding<Str, Sort>>, Sort)>,
}

/// It is a builder context for building recursive functions
///
/// c.f. [RecFunsContext::typed_define_funs_rec]
pub struct RecFunsContext<'a> {
    context: &'a mut Context,
    defs: Option<RecFunsDefs>,
    undefined_funs: HashSet<Str>,
}

/// It is a builder context for building each recursive function
pub struct EachRecFunContext<'b> {
    context: &'b mut Context,
    current: Str,
    inputs: &'b Vec<VarBinding<Str, Sort>>,
    output: &'b Sort,
    fun_defs: &'b mut HashMap<Str, FunctionDef>,
    undefined_funs: &'b mut HashSet<Str>,
}

impl<'a> RecFunsContext<'a> {
    pub(crate) fn new<T, S>(context: &'a mut Context, funs: T) -> TC<Self>
    where
        T: IntoIterator<Item = RecFunc<S, Sort>>,
        S: AllocatableString<Arena>,
    {
        context.check_logic()?;
        let mut new_funs = vec![];
        let mut var_map: HashMap<Str, usize> = HashMap::new();
        let mut sigs = HashMap::new();
        for fun in funs {
            let symbol = fun.name.allocate(context.arena());
            // 1. make sure the symbol can be added to the symbol table
            context.can_add_symbol(&symbol).map_err(|_| {
                format!(
                    "symbol {}{} cannot be added to the symbol table!",
                    symbol.sym_quote(),
                    fun.name.display_meta_data()
                )
            })?;
            new_funs.push(symbol.clone());
            // 2. make sure the symbols do not conflict with each other
            let entry = var_map.entry(symbol.clone()).or_insert(0);
            *entry += 1;
            if *entry > 1 {
                return Err(format!(
                    "TC: function {}{} is duplicated in the recursive definitions!",
                    symbol.sym_quote(),
                    fun.name.display_meta_data()
                ));
            }
            // 3. make sure the inputs are mutually different
            let inputs = fun
                .inputs
                .into_iter()
                .map(|(s, so)| {
                    let s = s.allocate(context.arena());
                    let id = context.new_local();
                    VarBinding(s, id, so)
                })
                .collect::<Vec<_>>();
            sanitize_bindings(&inputs, |v| v.0.clone())?;
            sigs.insert(symbol, (inputs, fun.output));
        }
        if new_funs.is_empty() {
            return Err("TC: should define at least one recursive function!".into());
        }
        let undefined_funs = new_funs.iter().cloned().collect::<HashSet<_>>();
        let defs = RecFunsDefs {
            new_funs,
            fun_defs: HashMap::new(),
            sigs,
        };

        Self {
            context,
            defs: Some(defs),
            undefined_funs,
        }
        .initial_insert_sigs()
    }

    fn initial_insert_sigs(self) -> TC<Self> {
        for (name, (inputs, out)) in &self.defs.as_ref().unwrap().sigs {
            self.context.add_symbol(
                name.clone(),
                Sig::func(inputs.iter().map(|v| v.2.clone()).collect(), out.clone()),
            )?;
        }
        Ok(self)
    }

    fn remove_sigs(&mut self) {
        if let Some(defs) = &self.defs {
            for n in &defs.new_funs {
                // we can just remove the symbols without worrying about overloading because we
                // have tested using `can_add_symbol`
                self.context.remove_symbol(n);
            }
        }
    }

    /// Return a set of undefined functions
    pub fn undefined_functions(&self) -> &HashSet<Str> {
        &self.undefined_funs
    }

    /// Create the recursive functions
    pub fn typed_define_funs_rec(mut self) -> TC<Command> {
        if !self.undefined_funs.is_empty() {
            return Err(format!(
                "TC: remaining undefined functions: {}",
                self.undefined_funs
                    .iter()
                    .map(|s| s.sym_quote())
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
        self.remove_sigs();
        let mut def = self.defs.take().unwrap();
        let mut fun_defs = vec![];
        let rec_defs = def.new_funs.iter().cloned().collect::<HashSet<_>>();
        for n in &def.new_funs {
            let def = def.fun_defs.remove(n).unwrap();
            self.context
                .insert_symbol_with_def(rec_defs.clone(), def.clone());
            fun_defs.push(def);
        }
        if fun_defs.len() == 1 {
            Ok(self.context.define_fun_rec(fun_defs.remove(0)))
        } else {
            Ok(self.context.define_funs_rec(fun_defs))
        }
    }

    /// Return a builder context for the body of the function
    pub fn build_function<S>(&mut self, name: S) -> TC<EachRecFunContext<'_>>
    where
        S: AllocatableString<Arena>,
    {
        EachRecFunContext::new(self, name)
    }
}

impl Drop for RecFunsContext<'_> {
    fn drop(&mut self) {
        self.remove_sigs();
    }
}

impl<'b> EachRecFunContext<'b> {
    fn new<'a, S>(parent: &'b mut RecFunsContext<'a>, name: S) -> TC<Self>
    where
        S: AllocatableString<Arena>,
    {
        let sym = name.allocate(parent.context.arena());
        if !parent.undefined_funs.contains(&sym) {
            return Err(format!(
                "TC: {}{} is not a remaining recursive function to be defined!",
                sym.sym_quote(),
                name.display_meta_data(),
            ));
        }
        let (fun_defs, inputs, output) = {
            let r = parent.defs.as_mut().unwrap();
            let (i, o) = r.sigs.get(&sym).unwrap();
            (&mut r.fun_defs, i, o)
        };
        Ok(Self {
            context: parent.context,
            current: sym,
            inputs,
            output,
            fun_defs,
            undefined_funs: &mut parent.undefined_funs,
        })
    }

    /// Create the function with the given body
    pub fn typed_function(mut self, body: Term) -> TC<()> {
        let sort = body.get_sort(&mut self);
        if sort != *self.output {
            return Err(format!(
                "TC: function {} is declared to have sort {} but is checked to have sort {}!",
                self.current.sym_quote(),
                *self.output,
                sort
            ));
        }
        self.undefined_funs.remove(&self.current);
        self.fun_defs.insert(
            self.current.clone(),
            FunctionDef {
                name: self.current.clone(),
                vars: self.inputs.clone(),
                out_sort: sort,
                body,
            },
        );
        Ok(())
    }
}

impl HasArena for EachRecFunContext<'_> {
    #[inline]
    fn arena(&mut self) -> &mut Arena {
        self.context.arena()
    }
}

impl TypedApi for EachRecFunContext<'_> {
    fn get_tcenv(&mut self) -> TCEnv<'_, '_, Sort> {
        self.context.get_tcenv().convert_to_new_local(LocEnv::Cons {
            car: self.inputs,
            cdr: &LocEnv::Nil,
        })
    }

    fn build_quantifier(&mut self) -> TC<QuantifierContext<'_, '_>> {
        QuantifierContext::new(
            self.context,
            LocEnv::Cons {
                car: self.inputs,
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
                car: self.inputs,
                cdr: &LocEnv::Nil,
            },
            bindings,
        )
    }

    fn build_matching(&mut self, scrutinee: Term) -> TC<MatchContext<'_, '_>> {
        MatchContext::new(
            self.context,
            LocEnv::Cons {
                car: self.inputs,
                cdr: &LocEnv::Nil,
            },
            scrutinee,
        )
    }
}
