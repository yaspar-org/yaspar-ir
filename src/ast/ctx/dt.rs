use crate::allocator::{CommandAllocator, ObjectAllocatorExt, SortAllocator, StrAllocator};
use crate::ast::alg::{SigIndex, VarBinding};
use crate::ast::ctx::checked::ScopedSortApi;
use crate::ast::ctx::{
    Arena, Command, ConstructorDec, Context, DatatypeDec, DatatypeDef, Sig, Sort, Str, TCEnv, Theory,
    TC,
};
use crate::ast::{alg, DatatypeFunction, FunctionMeta, SymbolQuote, Typecheck};
use crate::locenv::{sanitize_bindings, LocEnv};
use crate::raw::instance::HasArena;
use crate::traits::{AllocatableString, Contains};
use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};

struct DatatypeDefs {
    /// The names of datatypes to be defined
    new_dts: Vec<Str>,
    dt_defs: HashMap<Str, DatatypeDef>,
}

/// It is a builder context for datatypes
///
/// c.f. [DatatypeContext::build_datatype] and [DatatypeContext::typed_declare_datatypes]
pub struct DatatypeContext<'a> {
    context: &'a mut Context,
    /// Invariant: almost always Some; it is only None when we confirm we have managed to build
    /// datatypes properly
    defs: Option<DatatypeDefs>,
    undefined_dts: HashSet<Str>,
    additional_symbols: HashSet<Str>,
}

/// It is a builder context for individual datatype declarations
///
/// c.f. [DtDeclContext::build_datatype_constructor] and [DtDeclContext::typed_datatype]
pub struct DtDeclContext<'a, 'b> {
    parent: &'b mut DatatypeContext<'a>,
    params: Vec<VarBinding<Str, ()>>,
    current: Str,
    ctors: Vec<ConstructorDec>,
    additional_symbols: HashSet<Str>,
}

impl DatatypeDefs {
    fn get_datatype_defs(mut self) -> Vec<DatatypeDef> {
        let mut dt_defs = vec![];
        for name in self.new_dts {
            dt_defs.push(self.dt_defs.remove(&name).unwrap());
        }
        dt_defs
    }

    fn find_empty_dt_name(&self) -> Option<Str> {
        check_dt_emptiness(&self.dt_defs)
    }
}

impl<'a> DatatypeContext<'a> {
    pub(crate) fn new<T, P, S>(context: &'a mut Context, dt_names_and_sorts: T) -> TC<Self>
    where
        T: IntoIterator<Item = (S, P)>,
        P: IntoIterator<Item = S>,
        S: AllocatableString<Arena>,
    {
        context.check_logic()?;
        context.check_support_theory(Theory::Datatypes)?;
        let mut new_dts = vec![];
        let mut dt_defs = HashMap::new();
        for (name, sort_names) in dt_names_and_sorts {
            let symbol = name.allocate(context.arena());
            context.can_add_sort(&symbol).map_err(|_| {
                format!(
                    "sort {}{} cannot be added to the sort table!",
                    symbol.sym_quote(),
                    name.display_meta_data()
                )
            })?;
            new_dts.push(symbol.clone());
            let params = sort_names
                .into_iter()
                .map(|x| x.allocate(context.arena()))
                .collect::<Vec<_>>();
            sanitize_bindings(&params, |v| v.clone())?;
            dt_defs.insert(
                symbol.clone(),
                DatatypeDef {
                    name: symbol,
                    dec: DatatypeDec {
                        params,
                        constructors: vec![],
                    },
                },
            );
        }
        if new_dts.is_empty() {
            return Err("TC: should define at least one datatype!".into());
        }

        let undefined_dts = new_dts.iter().cloned().collect::<HashSet<_>>();
        Self {
            context,
            defs: Some(DatatypeDefs { new_dts, dt_defs }),
            undefined_dts,
            additional_symbols: Default::default(),
        }
        .initial_insert_sorts()
    }

    fn initial_insert_sorts(self) -> TC<Self> {
        for (name, df) in self.defs.as_ref().map(|ds| ds.dt_defs.iter()).unwrap() {
            self.context.add_sort(name.clone(), df.dec.params.len())?;
        }
        Ok(self)
    }

    fn remove_sorts(&mut self) {
        if let Some(ds) = &self.defs {
            for name in &ds.new_dts {
                self.context.remove_sort(name)
            }
        }
    }

    fn insert_dt_sorts(&mut self) {
        for (name, df) in self.defs.as_ref().map(|ds| ds.dt_defs.iter()).unwrap() {
            // we know the insertion will be successful as it happens after initial_insert_sorts
            self.context
                .add_dt_sort(name.clone(), df.dec.clone())
                .unwrap();
        }
    }

    /// Return the undefined datatypes
    pub fn undefined_datatypes(&self) -> &HashSet<Str> {
        &self.undefined_dts
    }

    /// Create a context to build an individual datatype
    pub fn build_datatype<'b, S>(&'b mut self, name: S) -> TC<DtDeclContext<'a, 'b>>
    where
        S: AllocatableString<Arena>,
    {
        DtDeclContext::new(self, name)
    }

    /// Invoke this method if all datatypes are built.
    ///
    /// If all datatypes are well-formed, then return a command for building the datatypes.
    //noinspection RsUnwrap
    pub fn typed_declare_datatypes(mut self) -> TC<Command> {
        if !self.undefined_dts.is_empty() {
            return Err(format!(
                "TC: remaining undefined datatypes: {}",
                self.undefined_dts
                    .iter()
                    .map(|s| s.sym_quote())
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
        if let Some(s) = self.defs.as_ref().and_then(|ds| ds.find_empty_dt_name()) {
            return Err(format!(
                "TC: datatype {} could be an empty sort! a base case is required!",
                s.sym_quote()
            ));
        }
        // at this point, there is no empty datatype; everything is good
        // we first remove the corresponding temporary uninterpreted sorts to insert the right sorts
        // to the context.
        self.remove_sorts();
        // we insert the datatype sorts
        self.insert_dt_sorts();
        let defs = std::mem::take(&mut self.defs).unwrap();
        // self.defs has been replaced with None, so Drop is a noop.
        let mut dt_defs = defs.get_datatype_defs();

        extend_symbols_about_datatypes(&dt_defs, self.context);
        if dt_defs.len() == 1 {
            let df = dt_defs.pop().unwrap();
            Ok(self.context.declare_datatype(df.name, df.dec))
        } else {
            Ok(self.context.declare_datatypes(dt_defs))
        }
    }
}

// if the datatype creation is not successful, we should clean up the [Context]
impl Drop for DatatypeContext<'_> {
    fn drop(&mut self) {
        self.remove_sorts();
    }
}

impl HasArena for DatatypeContext<'_> {
    #[inline]
    fn arena(&mut self) -> &mut Arena {
        self.context.arena()
    }
}

impl<'a, 'b> DtDeclContext<'a, 'b> {
    fn new<S>(parent: &'b mut DatatypeContext<'a>, s: S) -> TC<Self>
    where
        S: AllocatableString<Arena>,
    {
        let sym = s.allocate(parent.arena());
        if !parent.undefined_dts.contains(&sym) {
            return Err(format!(
                "TC: {}{} is not a remaining datatype to be defined!",
                sym.sym_quote(),
                s.display_meta_data()
            ));
        }
        let dt = parent
            .defs
            .as_ref()
            .map(|ds| ds.dt_defs.get(&sym).unwrap())
            .unwrap();
        let params = dt
            .dec
            .params
            .iter()
            .map(|s| VarBinding(s.clone(), 0, ()))
            .collect::<Vec<_>>();
        Ok(Self {
            parent,
            params,
            current: sym,
            ctors: vec![],
            additional_symbols: Default::default(),
        })
    }

    fn check_name<S>(&mut self, name: S, additional: &mut HashSet<Str>) -> TC<Str>
    where
        S: AllocatableString<Arena>,
    {
        let symbol = name.allocate(self.arena());
        self.parent.context.can_add_symbol(&symbol)?;
        if self.additional_symbols.contains(&symbol)
            || self.parent.additional_symbols.contains(&symbol)
            || additional.contains(&symbol)
        {
            Err(format!(
                "symbol {}{} is already defined!",
                symbol.sym_quote(),
                name.display_meta_data()
            ))
        } else {
            additional.insert(symbol.clone());
            Ok(symbol)
        }
    }

    /// Create a constructor with a given list of arguments
    pub fn build_datatype_constructor<T, S>(&mut self, ctor: S, args: T) -> TC<()>
    where
        T: IntoIterator<Item = (S, Sort)>,
        S: AllocatableString<Arena>,
    {
        let mut added_names = HashSet::new();
        let ctor = self.check_name(ctor, &mut added_names)?;
        let mut is_sym = "is-".to_string();
        is_sym.push_str(ctor.inner());
        let is_sym = self.allocate_symbol(&is_sym);
        self.check_name(is_sym, &mut added_names)?;
        let mut new_args = vec![];
        for (name, sort) in args {
            let name = self.check_name(name, &mut added_names)?;
            let mut env = self
                .parent
                .context
                .get_sort_tcenv()
                .convert_to_new_local(LocEnv::Cons {
                    car: &self.params,
                    cdr: &LocEnv::Nil,
                });
            if !wf_sort(
                &self.parent.defs.as_ref().unwrap().new_dts,
                &sort,
                &mut env,
                true,
            ) {
                return Err(format!(
                    "TC: sort {sort} is not well-formed in datatype {}.",
                    self.current.sym_quote(),
                ));
            }
            new_args.push(VarBinding(name, 0, sort));
        }
        self.ctors.push(ConstructorDec {
            ctor,
            args: new_args,
        });
        self.additional_symbols.extend(added_names);
        Ok(())
    }

    /// c.f. [Self::build_datatype_constructor]
    pub fn build_datatype_constructor_nullary<S>(&mut self, ctor: S) -> TC<()>
    where
        S: AllocatableString<Arena>,
    {
        self.build_datatype_constructor::<[_; 0], S>(ctor, [])
    }

    /// Build a constructor given a declaration
    pub fn build_datatype_constructor_declaration<S, So>(
        &mut self,
        dec: &alg::ConstructorDec<S, So>,
    ) -> TC<()>
    where
        S: AllocatableString<Arena>,
        So: Typecheck<Self, Out = Sort>,
    {
        let args = dec
            .args
            .iter()
            .map(|a| {
                let so = a.2.type_check(self)?;
                Ok((&a.0, so))
            })
            .collect::<TC<Vec<_>>>()?;
        self.build_datatype_constructor(&dec.ctor, args)
    }

    /// Build all constructors when given a sequence of constructors
    pub fn build_datatype_constructor_declarations<S, So>(
        &mut self,
        decs: impl IntoIterator<Item: Borrow<alg::ConstructorDec<S, So>>>,
    ) -> TC<()>
    where
        S: AllocatableString<Arena>,
        So: Typecheck<Self, Out = Sort>,
    {
        for dec in decs {
            self.build_datatype_constructor_declaration(dec.borrow())?;
        }
        Ok(())
    }

    /// Define the current datatype
    pub fn typed_datatype(self) -> TC<()> {
        if self.ctors.is_empty() {
            return Err(format!(
                "TC: datatype {} has no constructor!",
                self.current.sym_quote()
            ));
        }
        self.parent
            .additional_symbols
            .extend(self.additional_symbols);
        self.parent.undefined_dts.remove(&self.current);
        self.parent
            .defs
            .as_mut()
            .and_then(|ds| ds.dt_defs.get_mut(&self.current))
            .unwrap()
            .dec
            .constructors = self.ctors;
        Ok(())
    }
}

impl HasArena for DtDeclContext<'_, '_> {
    #[inline]
    fn arena(&mut self) -> &mut Arena {
        self.parent.context.arena()
    }
}
impl ScopedSortApi for DtDeclContext<'_, '_> {
    #[inline]
    fn get_sort_tcenv(&mut self) -> TCEnv<'_, '_, ()> {
        self.parent
            .context
            .get_sort_tcenv()
            .convert_to_new_local(LocEnv::Cons {
                car: &self.params,
                cdr: &LocEnv::Nil,
            })
    }
}

/// Check whether a given sort is well-formed in a data type definition
///
/// Well-formedness condition requires that sorts in `names` can only appear as `top` symbols.
///
/// * names: the names of the datatypes being defined.
/// * top: whether the given sort is a top symbol
pub(crate) fn wf_sort(names: &[Str], sort: &Sort, env: &mut TCEnv<()>, top: bool) -> bool {
    if env.local.lookup(sort.sort_name()).is_some() {
        // if the sort is a locally bound sort variable, then it's well-formed.
        true
    } else {
        // otherwise, we know sort name is globally bound.
        if names.contains(sort.sort_name()) && !top {
            // now we are checking a sort that is being defined
            // a datatype can only appear as a top symbol
            false
        } else {
            // the current sort is a top symbol; it could be an existing symbol or a datatype
            // we must check the well-formedness of all sub-symbols
            for sub in &sort.1 {
                if !wf_sort(names, sub, env, false) {
                    return false;
                }
            }
            true
        }
    }
}

/// The actuator that computes the non-emptiness of the `current` datatype using DFS
///
/// * `nonemptiness` is the cached result of non-emptiness
/// * `defs` is a mapping from names to definitions.
/// * `stack` is a visiting stack for DFS
/// * `current` is the current datatype being looked at
///
/// Return true if the `current` datatype is non-empty.
fn check_emptiness_once<D: Borrow<DatatypeDef>>(
    nonemptiness: &mut HashMap<Str, Option<bool>>,
    defs: &HashMap<Str, D>,
    stack: &mut Vec<Str>,
    current: &Str,
) -> bool {
    if let Some(Some(r)) = nonemptiness.get(current) {
        // the non-emptiness of def has been determined, so there is nothing to work on.
        return *r;
    }

    let def = defs.get(current).unwrap().borrow(); // unwrap because we only handle datatypes
    // now we are working on def
    stack.push(def.name.clone());

    let params = &def.dec.params;
    let mut def_nonemptiness = false;
    for ctor in &def.dec.constructors {
        if def_nonemptiness {
            break;
        }
        let mut ctor_nonemptiness = true;
        for x in &ctor.args {
            if !ctor_nonemptiness {
                break;
            }
            if params.contains(x.2.sort_name()) {
                // a parameter is always non-empty.
                continue;
            }
            if let Some(r) = nonemptiness.get(x.2.sort_name()) {
                // now we are handling a recursively defined datatype
                if let Some(r) = r {
                    // the non-emptiness has been determined for x.2
                    ctor_nonemptiness = ctor_nonemptiness && *r;
                } else {
                    // the non-emptiness has not been determined for x.2
                    if stack.contains(x.2.sort_name()) {
                        // now we hit a loop, so we assume this sort is empty
                        ctor_nonemptiness = false
                    } else {
                        // now we have not seen this sort, so we must recursively compute its non-emptiness
                        let r = check_emptiness_once(nonemptiness, defs, stack, x.2.sort_name());
                        ctor_nonemptiness = ctor_nonemptiness && r;
                    }
                }
            }
        }
        def_nonemptiness = def_nonemptiness || ctor_nonemptiness;
    }
    nonemptiness.insert(current.clone(), Some(def_nonemptiness));
    stack.pop();

    def_nonemptiness
}

/// Check the (non-)emptiness of given datatype definitions.
///
/// The well-foundness condition for datatypes requires that datatypes must inductively have a
/// base case. This is checked by a DFS to detect a base case.
///
/// Return the name of the empty datatype, if exists.
pub(crate) fn check_dt_emptiness<D: Borrow<DatatypeDef>>(def_map: &HashMap<Str, D>) -> Option<Str> {
    let mut nonemptiness = HashMap::new();
    for k in def_map.keys() {
        nonemptiness.insert(k.clone(), None);
    }
    let mut stack = vec![];
    for name in def_map.keys() {
        let def = def_map.get(name).unwrap().borrow();
        if !check_emptiness_once(&mut nonemptiness, def_map, &mut stack, &def.name) {
            return Some(name.clone());
        }
    }
    None
}

/// Assuming correct datatypes, extend the symbol table
///
/// Sorts have been inserted, so we only insert symbols
pub(crate) fn extend_symbols_about_datatypes(defs: &[DatatypeDef], env: &mut Context) {
    let bool_sort = env.bool_sort();
    let is_symb = env.allocate_symbol("is");
    for def in defs {
        for ctor in &def.dec.constructors {
            // 1. insert constructor
            let current_sort = env.sort_n_params(def.name.clone(), def.dec.params.clone());
            let sig = Sig::ParFunc(
                vec![],
                def.dec.params.clone(),
                ctor.args.iter().map(|v| v.2.clone()).collect(),
                current_sort.clone(),
            );
            env.insert_symbol(
                ctor.ctor.clone(),
                sig,
                FunctionMeta::Datatype {
                    dt_name: def.name.clone(),
                    kind: DatatypeFunction::Constructor,
                },
            );

            // 2. insert selectors
            for sel in &ctor.args {
                let sig = Sig::ParFunc(
                    vec![],
                    def.dec.params.clone(),
                    vec![current_sort.clone()],
                    sel.2.clone(),
                );
                env.insert_symbol(
                    sel.0.clone(),
                    sig,
                    FunctionMeta::Datatype {
                        dt_name: def.name.clone(),
                        kind: DatatypeFunction::Selector,
                    },
                );
            }

            // 3. insert (_ is X) testers
            let sig = Sig::ParFunc(
                vec![SigIndex::Symbol(ctor.ctor.clone())],
                def.dec.params.clone(),
                vec![current_sort.clone()],
                bool_sort.clone(),
            );
            env.push_symbol(
                is_symb.clone(),
                sig,
                FunctionMeta::Datatype {
                    dt_name: def.name.clone(),
                    kind: DatatypeFunction::Tester,
                },
            );

            // 4. insert is-X testers
            let mut is_sym = "is-".to_string();
            is_sym.push_str(ctor.ctor.inner());
            let is_sym = env.allocate_symbol(&is_sym);
            let sig = Sig::ParFunc(
                vec![],
                def.dec.params.clone(),
                vec![current_sort.clone()],
                bool_sort.clone(),
            );
            env.insert_symbol(
                is_sym.clone(),
                sig,
                FunctionMeta::Datatype {
                    dt_name: def.name.clone(),
                    kind: DatatypeFunction::Tester,
                },
            );
        }
    }
}
