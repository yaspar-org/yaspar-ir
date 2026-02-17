// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

mod bindings;
mod checked;
mod ds;
mod dt;
mod fun;
mod init;
mod local;
mod matching;
mod quantifier;
mod recs;
pub mod utils;

#[cfg(feature = "implicant-generation")]
use crate::ast::implicant::{ImplicantEnumerator, ImplicantIterator};
use crate::locenv::LocEnv;
pub use crate::raw::alg::{
    Command as ACommand, Constant as AConstant, Index as AIndex, SortDef as ASortDef, StrQuote,
    SymbolQuote, Term as ATerm,
};
pub use crate::raw::instance::*;
use crate::raw::tc::{TC, TCEnv};
pub use checked::{ScopedSortApi, TypedApi};
use lazy_static::lazy_static;
use std::collections::hash_map::Keys;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Formatter};

#[cfg(feature = "cnf")]
use crate::ast::cnf::{CNFCache, CNFEnv};
#[cfg(feature = "cnf")]
pub use crate::ast::cnf::{CNFConversion, partition_nnfs};
use crate::statics::{BITVEC, BV_RE};
use crate::traits::AllocatableString;
pub use crate::traits::Contains;
pub use crate::traits::Repr;
pub use bindings::*;
pub use ds::*;
pub use dt::*;
pub use fun::*;
pub use matching::*;
pub use quantifier::*;
pub use recs::*;
#[cfg(feature = "cnf")]
use sat_interface::Formula;
#[cfg(feature = "implicant-generation")]
use sat_interface::SatSolver;

// See: https://smt-lib.org/logics.shtml and https://zenodo.org/records/15493090
lazy_static! {
    static ref LOGICS: HashMap<&'static str, HashSet<Theory>> = HashMap::from([
        ("IDL", HashSet::from([Theory::Quantifiers, Theory::Ints])),
        ("LIA", HashSet::from([Theory::Quantifiers, Theory::Ints])),
        ("LRA", HashSet::from([Theory::Quantifiers, Theory::Reals])),
        ("LIRA", HashSet::from([Theory::Quantifiers, Theory::RealInts])),
        ("NIA", HashSet::from([Theory::Quantifiers, Theory::Ints])),
        ("NRA", HashSet::from([Theory::Quantifiers, Theory::Reals])),
        ("NIRA", HashSet::from([Theory::Quantifiers, Theory::RealInts])),
        (
            "AUFLIA",
            HashSet::from([Theory::Quantifiers, Theory::Ints, Theory::ArrayEx])
        ),
        (
            "AUFLIRA",
            HashSet::from([Theory::Quantifiers, Theory::RealInts, Theory::ArrayEx])
        ),
        (
            "AUFNIRA",
            HashSet::from([Theory::Quantifiers, Theory::RealInts, Theory::ArrayEx])
        ),
        // Note: there are no SMT Comp benchmarks as of 2025 for AUFLRA, AUFNRA
        ("QF_BV", HashSet::from([Theory::Bitvectors])),
        ("QF_IDL", HashSet::from([Theory::Ints])),
        ("QF_LIA", HashSet::from([Theory::Ints])),
        ("QF_LRA", HashSet::from([Theory::Reals])),
        ("QF_LIRA", HashSet::from([Theory::RealInts])),
        ("QF_NIA", HashSet::from([Theory::Ints])),
        ("QF_NRA", HashSet::from([Theory::Reals])),
        ("QF_NIRA", HashSet::from([Theory::RealInts])),
        ("QF_RDL", HashSet::from([Theory::Reals])),
        ("QF_UF", HashSet::from([])),
        ("QF_UFIDL", HashSet::from([Theory::Ints])),
        ("QF_UFLIA", HashSet::from([Theory::Ints])),
        ("QF_UFLRA", HashSet::from([Theory::Reals])),
        ("QF_UFNRA", HashSet::from([Theory::Reals])),
        ("QF_S", HashSet::from([Theory::Strings])),
        ("QF_SLIA", HashSet::from([Theory::Ints, Theory::Strings])),
        ("QF_SNIA", HashSet::from([Theory::Ints, Theory::Strings])),
        ("QF_AUFLIA", HashSet::from([Theory::Ints, Theory::ArrayEx])),
        ("QF_AX", HashSet::from([Theory::ArrayEx])),
        ("UFLRA", HashSet::from([Theory::Quantifiers, Theory::Reals])),
        ("UFNIA", HashSet::from([Theory::Quantifiers, Theory::Ints])),
        (
            "ALL",
            HashSet::from([
                Theory::Quantifiers,
                Theory::RealInts,
                Theory::Strings,
                Theory::ArrayEx,
                Theory::FloatingPoints,
                Theory::Bitvectors,
                Theory::Datatypes
            ])
        ),
    ]);
    pub(crate) static ref ALL_LOGICS: Vec<&'static str> = LOGICS.keys().cloned().collect();
    static ref EMP_SET: HashSet<Theory> = HashSet::from([]);
    static ref SPECIAL_SYMBOLS: HashSet<&'static str> = {
      let mut set = yaspar::tokens::SPECIAL_SYMBOLS.keys().cloned().collect::<HashSet<_>>();
        set.extend(["and", "or", "not", "ite", "=>", "distinct", "="].iter());
        set
    };
}

#[cfg(feature = "cache")]
pub struct Caches {
    #[cfg(feature = "cnf")]
    pub cnf_cache: CNFCache,
}

/// The kinds of a function related to a datatype
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DatatypeFunction {
    Constructor,
    Selector,
    Tester,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionMetaDefined {
    /// The dependent names if the function is defined recursively
    pub rec_deps: HashSet<Str>,
    /// The definition of the function
    pub def: FunctionDef,
}

/// meta-data for functions
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FunctionMeta {
    /// An opaque function; it could either be an uninterpreted function or a builtin one
    Opaque,
    /// A defined function via define-fun, define-const, define-fun-rec or define-funs-rec
    Defined(FunctionMetaDefined),
    /// A generated function related to a datatype
    Datatype {
        /// The name of the datatype
        dt_name: Str,
        /// The kind of this function
        kind: DatatypeFunction,
    },
}

/// Global context for the current session
pub struct Context {
    /// The memory arena
    pub(crate) arena: Arena,
    /// Logic
    pub(crate) logic: Option<String>,
    /// Custom sorts; mapping sort names to arities
    pub(crate) sorts: HashMap<Str, SortDef>,
    /// Mapping custom functions to their signatures and potentially their definitions
    pub(crate) symbol_table: HashMap<Str, Vec<(Sig, FunctionMeta)>>,
    /// Caches for various algorithms
    #[cfg(feature = "cache")]
    pub caches: Caches,
}

pub(crate) type Result<T> = std::result::Result<T, String>;

impl Context {
    /// Return the name of the logic; need to make sure the logic is set
    pub fn get_logic(&self) -> &str {
        self.logic.as_ref().unwrap()
    }

    /// Return the theories
    pub fn get_theories(&self) -> &'static HashSet<Theory> {
        match &self.logic {
            None => &EMP_SET,
            Some(l) => LOGICS.get(l.as_str()).unwrap(),
        }
    }

    fn check_bv(&self, sort: &Str) -> Result<()> {
        if sort.inner() == BITVEC && self.check_support_theory(Theory::Bitvectors).is_ok() {
            Err("BitVec cannot be redeclared!".to_string())
        } else {
            Ok(())
        }
    }

    /// Check whether a given sort name can be added to the sort table
    pub fn can_add_sort(&self, symbol: &Str) -> Result<()> {
        self.check_special_symbols(symbol)?;
        self.check_bv(symbol)?;
        if self.sorts.contains_key(symbol) {
            Err(format!("sort {} is already defined!", symbol.sym_quote()))
        } else {
            Ok(())
        }
    }

    /// Extend the given context with a custom sort with its arity
    pub fn add_sort<S>(&mut self, sort: S, arity: usize) -> Result<()>
    where
        S: AllocatableString<Arena>,
    {
        let sort = sort.allocate(self.arena());
        self.can_add_sort(&sort)?;
        self.sorts.insert(sort, SortDef::Opaque(arity));
        Ok(())
    }

    /// Remove a sort from the sort table
    pub fn remove_sort<S>(&mut self, sort: &S)
    where
        S: AllocatableString<Arena>,
    {
        let sort = sort.allocate(self.arena());
        self.sorts.remove(&sort);
    }

    /// Extend the given context with a custom sort with its definition
    pub fn def_sort<S>(
        &mut self,
        sort: S,
        params: impl IntoIterator<Item = S>,
        s: Sort,
    ) -> Result<()>
    where
        S: AllocatableString<Arena>,
    {
        let sort = sort.allocate(self.arena());
        self.can_add_sort(&sort)?;
        let params = params
            .into_iter()
            .map(|p| p.allocate(self.arena()))
            .collect();
        self.sorts
            .insert(sort, SortDef::Transparent { params, sort: s });
        Ok(())
    }

    pub(crate) fn add_dt_sort<S>(&mut self, sort: S, dt: DatatypeDec) -> Result<()>
    where
        S: AllocatableString<Arena>,
    {
        let sort = sort.allocate(self.arena());
        self.can_add_sort(&sort)?;
        self.sorts.insert(sort, SortDef::Datatype(dt));
        Ok(())
    }

    fn check_special_symbols(&self, sym: &Str) -> Result<()> {
        if SPECIAL_SYMBOLS.contains(sym.as_str()) {
            Err("Special symbols cannot be declared!".to_string())
        } else {
            Ok(())
        }
    }

    fn check_bv_sym(&self, sym: &Str) -> Result<()> {
        if self.check_support_theory(Theory::Bitvectors).is_ok() && BV_RE.is_match(sym) {
            Err("symbols of the form bvX cannot be declared!".to_string())
        } else {
            Ok(())
        }
    }

    fn check_is_sym(&self, sym: &Str) -> Result<()> {
        if self.check_support_theory(Theory::Datatypes).is_ok() && sym.inner() == "is" {
            Err("`is` cannot be declared!".into())
        } else {
            Ok(())
        }
    }

    fn check_sym_validity(&self, sym: &Str) -> Result<()> {
        self.check_special_symbols(sym)?;
        self.check_bv_sym(sym)?;
        self.check_is_sym(sym)
    }

    /// Check whether a symbol is contained in the symbol table
    pub fn contain_symbol(&self, sym: &Str) -> bool {
        self.symbol_table.contains_key(sym)
    }

    /// Check whether a given symbol can be added to the symbol table
    pub fn can_add_symbol(&self, symbol: &Str) -> Result<()> {
        self.check_sym_validity(symbol)?;
        if self.symbol_table.contains_key(symbol) {
            Err(format!("symbol {} is already defined!", symbol.sym_quote()))
        } else {
            Ok(())
        }
    }

    /// Insert the symbol to the table without any checks. Use it only when invariance is known
    /// to have been maintained.
    pub(crate) fn insert_symbol(&mut self, symbol: Str, sig: Sig, meta: FunctionMeta) {
        self.symbol_table.insert(symbol, vec![(sig, meta)]);
    }

    /// Insert the symbol to the table with its definition without any checks. Use it only when
    /// invariance is known to have been maintained.
    pub(crate) fn insert_symbol_with_def(&mut self, rec_deps: HashSet<Str>, def: FunctionDef) {
        self.symbol_table.insert(
            def.name.clone(),
            vec![(
                Sig::func(
                    def.vars.iter().map(|v| v.2.clone()).collect(),
                    def.out_sort.clone(),
                ),
                FunctionMeta::Defined(FunctionMetaDefined { rec_deps, def }),
            )],
        );
    }

    /// Add a declared symbol to the symbol table and reject duplicated definitions.
    pub fn add_symbol<S>(&mut self, symbol: S, sig: Sig) -> Result<()>
    where
        S: AllocatableString<Arena>,
    {
        let symbol = symbol.allocate(self.arena());
        self.can_add_symbol(&symbol)?;
        self.insert_symbol(symbol, sig, FunctionMeta::Opaque);
        Ok(())
    }

    /// Add a symbol with its definition to the symbol table and reject duplicated definitions.
    pub fn def_symbol(&mut self, def: FunctionDef) -> Result<()> {
        self.can_add_symbol(&def.name)?;
        self.insert_symbol_with_def(HashSet::new(), def);
        Ok(())
    }

    /// Push the symbol to the table without any checks. Use it only when invariance is known
    /// to have been maintained.
    pub(crate) fn push_symbol(&mut self, symbol: Str, sig: Sig, meta: FunctionMeta) {
        self.symbol_table
            .entry(symbol)
            .or_default()
            .push((sig, meta));
    }

    /// Extend a symbol to the symbol table
    ///
    /// It overloads the given symbol if it has been defined, c.f. [Self::add_symbol]
    pub fn extend_symbol<S>(&mut self, symbol: S, sig: Sig) -> Result<()>
    where
        S: AllocatableString<Arena>,
    {
        let symbol = symbol.allocate(self.arena());
        self.check_special_symbols(&symbol)?;
        self.check_bv_sym(&symbol)?;
        self.push_symbol(symbol, sig, FunctionMeta::Opaque);
        Ok(())
    }

    /// Remove a symbol from the symbol table
    pub fn remove_symbol<S>(&mut self, symbol: &S)
    where
        S: AllocatableString<Arena>,
    {
        let symbol = symbol.allocate(self.arena());
        self.symbol_table.remove(&symbol);
    }

    /// Return the number of symbols; overloaded symbols are considered multiple times
    pub fn symbol_count(&self) -> usize {
        self.symbol_table
            .values()
            .fold(0, |acc, sigs| acc + sigs.len())
    }

    /// Return the number of symbols in the symbol table without considering overloading
    pub fn symbol_count_no_dup(&self) -> usize {
        self.symbol_table.len()
    }

    /// Return the number of defined sorts
    pub fn sort_count(&self) -> usize {
        self.sorts.len()
    }

    /// Given a SAT solver, produce an iterator that iterates through the implicants of given assertions.
    ///
    /// When the iterator produces an [Err], it means the SAT solver returns unknown and the iteration
    /// terminates, even if theoretically there could be more implicants.
    #[cfg(feature = "implicant-generation")]
    pub fn iter_implicants<'a, 'b, Solver: SatSolver>(
        &'a mut self,
        solver: &'b mut Solver,
        asserts: &Vec<Term>,
    ) -> impl ImplicantIterator<Vec<Term>> + use<'a, 'b, Solver> {
        let formula = asserts.cnf(&mut *self);
        solver.insert(&formula);
        let nnfs = asserts.nnf(&mut *self);
        ImplicantEnumerator {
            arena: &mut self.arena,
            solver,
            cache: &mut self.caches.cnf_cache,
            nnf: nnfs,
            finished: false,
        }
    }

    /// Convert an arena `id` into a sat variables.
    #[cfg(feature = "cnf")]
    pub fn sat_var(&self, id: u64) -> Option<i32> {
        self.caches.cnf_cache.var_map.get(&id).copied()
    }

    /// Convert a slice of arena `ids` into a vector of sat variables.
    #[cfg(feature = "cnf")]
    pub fn sat_vars(&self, ids: &[u64], negate: bool) -> Vec<i32> {
        let factor = if negate { -1 } else { 1 };
        ids.iter()
            .map(
                |id| match self.caches.cnf_cache.var_map.get(id).map(|n| *n * factor) {
                    Some(n) => n,
                    None => panic!("var {} not found!", id),
                },
            )
            .collect()
    }

    pub fn expose_symbol_table(&self) -> &HashMap<Str, Vec<(Sig, FunctionMeta)>> {
        &self.symbol_table
    }

    pub fn expose_sorts(&self) -> &HashMap<Str, SortDef> {
        &self.sorts
    }

    /// Return an iterable for all symbols
    pub fn all_symbols(&self) -> Keys<'_, Str, Vec<(Sig, FunctionMeta)>> {
        self.symbol_table.keys()
    }

    /// Return an iterable for all sorts
    pub fn all_sorts(&self) -> Keys<'_, Str, SortDef> {
        self.sorts.keys()
    }

    /// Get the binding associated with the given symbol in the symbol table
    pub fn get_symbol_binding(&self, symbol: &Str) -> Option<&[(Sig, FunctionMeta)]> {
        self.symbol_table.get(symbol).map(|sigs| sigs.as_slice())
    }

    /// Get the definition associated with the given name
    pub fn get_definition(&self, symbol: &Str) -> Option<&FunctionMetaDefined> {
        self.get_symbol_binding(symbol).and_then(|sigs| {
            sigs.iter().find_map(|(_, m)| {
                if let FunctionMeta::Defined(d) = m {
                    Some(d)
                } else {
                    None
                }
            })
        })
    }

    /// Return the definition of the sort bound to a given name
    pub fn get_sort_def(&self, name: &Str) -> Option<&SortDef> {
        self.sorts.get(name)
    }

    /// Get all the symbols with a definition body
    pub fn all_defined_symbols(&self) -> HashSet<Str> {
        self.symbol_table
            .iter()
            .filter_map(|(name, sigs)| {
                // scan all signatures for one that has a defined body
                sigs.iter()
                    .filter_map(|(_, def)| {
                        if matches!(def, FunctionMeta::Defined { .. }) {
                            Some(name.clone())
                        } else {
                            None
                        }
                    })
                    .next()
            })
            .collect()
    }

    /// Test only
    ///
    /// Used to access signatures
    #[cfg(test)]
    pub fn get_symbol_str(
        &mut self,
        symbol: &str,
    ) -> Option<(QualifiedIdentifier, &Vec<(Sig, FunctionMeta)>)> {
        let symbol = self.allocate_symbol(symbol);
        self.symbol_table
            .get(&symbol)
            .map(|sigs| (QualifiedIdentifier::simple(symbol.clone()), sigs))
    }
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

impl Debug for Context {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Context")
    }
}

impl HasArena for Context {
    #[inline]
    fn arena(&mut self) -> &mut Arena {
        &mut self.arena
    }
}

impl TypedApi for Context {
    fn get_tcenv(&mut self) -> TCEnv<'_, '_, Sort> {
        let theories = self.get_theories();
        TCEnv {
            arena: &mut self.arena,
            theories,
            sorts: &mut self.sorts,
            symbol_table: &self.symbol_table,
            local: LocEnv::Nil,
        }
    }

    fn build_quantifier(&mut self) -> TC<QuantifierContext<'_, '_>> {
        QuantifierContext::new(self, LocEnv::Nil)
    }

    fn build_let<T, S>(&mut self, bindings: T) -> TC<LetContext<'_, '_>>
    where
        T: IntoIterator<Item = (S, Term)>,
        S: AllocatableString<Arena>,
    {
        LetContext::new_with_bindings(self, LocEnv::Nil, bindings)
    }

    fn build_matching(&mut self, scrutinee: Term) -> TC<MatchContext<'_, '_>> {
        MatchContext::new(self, LocEnv::Nil, scrutinee)
    }
}

#[cfg(feature = "cnf")]
impl<T> CNFConversion<&mut Context> for T
where
    T: for<'a, 'b> CNFConversion<&'b mut CNFEnv<'a>>,
{
    fn cnf(&self, env: &mut Context) -> Formula {
        let mut env = CNFEnv {
            arena: &mut env.arena,
            cache: &mut env.caches.cnf_cache,
        };
        self.cnf(&mut env)
    }

    fn cnf_tseitin(&self, env: &mut Context) -> Formula {
        let mut env = CNFEnv {
            arena: &mut env.arena,
            cache: &mut env.caches.cnf_cache,
        };
        self.cnf_tseitin(&mut env)
    }

    fn nnf(&self, env: &mut Context) -> Self {
        let mut env = CNFEnv {
            arena: &mut env.arena,
            cache: &mut env.caches.cnf_cache,
        };
        self.nnf(&mut env)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{LetElim, Typecheck, u};
    use crate::untyped::UntypedAst;
    use dashu::integer::IBig;

    fn do_tc_let_elim(context: &mut Context, cmds: Vec<u::Command>) -> Option<Term> {
        for cmd in &cmds {
            let cmd = cmd.type_check(context).unwrap();
            if let ACommand::Assert(t) = cmd.repr() {
                return Some(t.let_elim(context));
            }
        }
        None
    }

    #[test]
    fn test_script1() {
        let script: String = r"(declare-sort S1 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 () Int)
(declare-fun f4 (Int Int) Int)
(assert (not (= f1 f2)))
"
        .into();
        let cmds = UntypedAst.parse_script_str(&script).unwrap();
        let mut context = Context::new();
        context.ensure_logic();
        let t = do_tc_let_elim(&mut context, cmds).unwrap();
        assert_eq!(t.to_string(), "(not (= f1 f2))");
        let s1_str = context.allocate_symbol("S1");
        let s1 = context.sort0(s1_str);
        let f1 = context.simple_sorted_symbol("f1", s1.clone());
        let f2 = context.simple_sorted_symbol("f2", s1.clone());
        let eq = context.eq(f1, f2);
        assert_eq!(t, context.not(eq));

        // check context
        match context.get_symbol_str("f1") {
            None => panic!("symbol not found!"),
            Some((qid, sigs)) => {
                assert_eq!(qid.id_str().as_str(), "f1");
                assert_eq!(sigs.len(), 1);
                assert_eq!(sigs[0].0, Sig::sort(s1.clone()));
            }
        }

        match context.get_symbol_str("f2") {
            None => panic!("symbol not found!"),
            Some((qid, sigs)) => {
                assert_eq!(qid.id_str().as_str(), "f2");
                assert_eq!(sigs.len(), 1);
                assert_eq!(sigs[0].0, Sig::sort(s1));
            }
        }

        let int_sort = context.int_sort();
        match context.get_symbol_str("f3") {
            None => panic!("symbol not found!"),
            Some((qid, sigs)) => {
                assert_eq!(qid.id_str().as_str(), "f3");
                assert_eq!(sigs.len(), 1);
                assert_eq!(sigs[0].0, Sig::sort(int_sort.clone()).clone());
            }
        }

        match context.get_symbol_str("f4") {
            None => panic!("symbol not found!"),
            Some((qid, sigs)) => {
                assert_eq!(qid.id_str().as_str(), "f4");
                assert_eq!(sigs.len(), 1);
                assert_eq!(
                    sigs[0].0,
                    Sig::func(vec![int_sort.clone(), int_sort.clone()], int_sort.clone())
                );
            }
        }
    }

    #[test]
    fn test_script2() {
        let script: String = r"(declare-sort S1 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 () Int)
(declare-fun f4 (Int Int) Int)
(assert (not (< (+ (* 4 f3) 1) 2)))
"
        .into();
        let cmds = UntypedAst.parse_script_str(&script).unwrap();
        let mut context = Context::new();
        context.ensure_logic();
        let tct = do_tc_let_elim(&mut context, cmds).unwrap();

        let int_sort = context.int_sort();
        let bool_sort = context.bool_sort();
        let f3 = context.simple_sorted_symbol("f3", int_sort.clone());

        let times = context.get_symbol_str("*").unwrap().0;
        let four = context.integer(IBig::from(4)).unwrap();
        let t1 = context.app(times, vec![four, f3], Some(int_sort.clone()));
        let plus = context.get_symbol_str("+").unwrap().0;
        let one = context.integer(IBig::from(1)).unwrap();
        let t2 = context.app(plus, vec![t1, one], Some(int_sort.clone()));
        let lt = context.get_symbol_str("<").unwrap().0;
        let two = context.integer(IBig::from(2)).unwrap();
        let t3 = context.app(lt, vec![t2, two], Some(bool_sort.clone()));
        let nt3 = context.not(t3);
        assert_eq!(tct, nt3);
    }

    #[test]
    fn test_script3() {
        let script: String = r"(declare-sort S1 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 () Int)
(declare-fun f4 (Int Int) Int)
(assert (let ((?v_0 (+ (* 4 f3) 1))) (let ((?v_1 (f4 ?v_0 (- ?v_0 1)))) (< ?v_1 (+ (- ?v_1 ?v_0) 2)))))
".into();
        let cmds = UntypedAst.parse_script_str(&script).unwrap();
        let mut context = Context::new();
        context.ensure_logic();
        let tct = do_tc_let_elim(&mut context, cmds).unwrap();
        let int_sort = context.int_sort();
        let bool_sort = context.bool_sort();
        let f3 = context.simple_sorted_symbol("f3", int_sort.clone());
        let f4 = context.get_symbol_str("f4").unwrap().0;

        let times = context.get_symbol_str("*").unwrap().0;
        let four = context.integer(IBig::from(4)).unwrap();
        let t1 = context.app(times, vec![four, f3], Some(int_sort.clone()));
        let plus = context.get_symbol_str("+").unwrap().0;
        let one = context.integer(IBig::from(1)).unwrap();
        let v0 = context.app(plus.clone(), vec![t1, one.clone()], Some(int_sort.clone()));

        let minus = context.get_symbol_str("-").unwrap().0;
        let t2 = context.app(minus.clone(), vec![v0.clone(), one], Some(int_sort.clone()));
        let v1 = context.app(f4, vec![v0.clone(), t2], Some(int_sort.clone()));

        let t3 = context.app(minus, vec![v1.clone(), v0], Some(int_sort.clone()));
        let two = context.integer(IBig::from(2)).unwrap();
        let t4 = context.app(plus, vec![t3, two], Some(int_sort.clone()));
        let lt = context.get_symbol_str("<").unwrap().0;
        let t5 = context.app(lt, vec![v1, t4], Some(bool_sort.clone()));

        assert_eq!(tct, t5);
    }

    #[test]
    fn test_script4() {
        let mut context = Context::new();
        let cmd = UntypedAst
            .parse_command_str("(set-info :smt-lib-version 2.6)")
            .unwrap();
        // 2.6 in set-info shouldn't matter
        cmd.type_check(&mut context).unwrap();
    }
}
