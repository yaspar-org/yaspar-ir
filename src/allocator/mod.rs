// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Allocator traits for an arena
//!
//! These traits expose unchecked APIs. They are responsible for object allocations **only**.
//! Invariants need to be explicitly maintained.

use crate::raw::alg::*;
use crate::statics::{ARRAY, BITVEC, BOOL, INT, REAL, REGLAN, STRING};
use dashu::integer::UBig;
use paste::paste;
use yaspar::ast::Keyword;

macro_rules! gen_ctor {
    ($alloc: tt, $t:ident :: $ctor:ident() -> $rt:ty) => {
        paste! {
            #[doc = "Allocate a new `" $ctor "` object. This API requires manual maintenance of invariance. Consider [crate::ast::CheckedApi] and [crate::ast::ScopedSortApi] instead"]
            fn [<$ctor:snake>](&mut self) -> $rt {
               self.$alloc($t::$ctor)
            }
        }
    };
    ($alloc: tt, $fname:ident, $t:ident :: $ctor:ident() -> $rt:ty) => {
        paste! {
            #[doc = "Allocate a new `" $ctor "` object. This API requires manual maintenance of invariance. Consider [crate::ast::CheckedApi] and [crate::ast::ScopedSortApi] instead"]
            fn $fname(&mut self) -> $rt {
               self.$alloc($t::$ctor)
            }
        }
    };
    ($alloc: tt, $t:ident :: $ctor:ident($($x:ident : $xt:ty),+) -> $rt:ty) => {
        paste! {
            #[doc = "Allocate a new `" $ctor "` object. This API requires manual maintenance of invariance. Consider [crate::ast::CheckedApi] and [crate::ast::ScopedSortApi] instead"]
            fn [<$ctor:snake>](&mut self $(, $x: $xt)*) -> $rt {
               self.$alloc($t::$ctor($($x,)*))
            }
        }
    };
    ($alloc: tt, $fname:ident, $t:ident :: $ctor:ident($($x:ident : $xt:ty),+) -> $rt:ty) => {
        paste! {
            #[doc = "Allocate a new `" $ctor "` object. This API requires manual maintenance of invariance. Consider [crate::ast::CheckedApi] and [crate::ast::ScopedSortApi] instead"]
            fn $fname(&mut self $(, $x: $xt)*) -> $rt {
               self.$alloc($t::$ctor($($x,)*))
            }
        }
    };
}

macro_rules! gen_ctors {
    ($alloc: tt -> $rt:ty $(| $t:ident :: $ctor:ident($($x:ident : $xt:ty),*))*) => {
        $( gen_ctor!($alloc, $t::$ctor($($x:$xt),*) -> $rt); )*
    }
}

fn from_parse_string(s: &str) -> String {
    let s = &s[1..s.len() - 1]; // strip off quotes
    s.replace("\"\"", "\"")
}

/// The ability to allocate strings
pub trait StrAllocator {
    type Str;

    /// The underlying machinery to hash cons a string
    fn allocate_str(&mut self, s: &str) -> Self::Str;
    /// The underlying machinery to hash cons a string
    fn allocate_string(&mut self, s: String) -> Self::Str;

    /// Allocate an SMTLib string of the form `"XXX"`
    fn allocate_parsed_str(&mut self, s: &str) -> Self::Str {
        self.allocate_string(from_parse_string(s))
    }

    /// Allocate an SMTLib symbol
    fn allocate_symbol(&mut self, s: &str) -> Self::Str;
}

/// The ability to allocate sorts
pub trait SortAllocator<Str, So> {
    fn allocate_sort(&mut self, s: Sort<Str, So>) -> So;

    fn sort(&mut self, id: Identifier<Str>, ss: Vec<So>) -> So {
        self.allocate_sort(Sort(id, ss))
    }

    fn sort0(&mut self, s: Str) -> So {
        self.sort_n(s, vec![])
    }

    fn sort_n(&mut self, s: Str, ss: Vec<So>) -> So {
        self.allocate_sort(Sort(Identifier::simple(s), ss))
    }

    fn sort_n_params(&mut self, s: Str, ss: Vec<Str>) -> So {
        let params = ss.into_iter().map(|s| self.sort0(s)).collect();
        self.sort_n(s, params)
    }
}

/// The ability to allocate terms
pub trait TermAllocator<Str, So, T> {
    fn allocate_term(&mut self, t: Term<Str, So, T>) -> T;

    gen_ctor!(allocate_term, let_term, Term::Let(vs: Vec<VarBinding<Str, T>>, t: T) -> T);

    gen_ctors!(allocate_term -> T
    | Term::Constant(c : Constant<Str>, s: Option<So>)
    | Term::Global(id: QualifiedIdentifier<Str, So>, sort: Option<So>)
    | Term::Local(id: Local<Str, So>)
    | Term::App(id: QualifiedIdentifier<Str, So>, ts: Vec<T>, s: Option<So>)
    | Term::Exists(vs: Vec<VarBinding<Str, So>>, t: T)
    | Term::Forall(vs: Vec<VarBinding<Str, So>>, t: T)
    | Term::Matching(scrutinee: T, cases: Vec<PatternArm<Str, T>>)
    | Term::Annotated(t: T, anns: Vec<Attribute<Str, T>>)
    | Term::Eq(a: T, b: T)
    | Term::Distinct(ts: Vec<T>)
    | Term::And(ts: Vec<T>)
    | Term::Or(ts: Vec<T>)
    | Term::Xor(ts: Vec<T>)
    | Term::Not(t: T)
    | Term::Implies(ts: Vec<T>, t: T)
    | Term::Ite(b: T, t: T, e: T));
}

/// The ability to allocate commands
pub trait CommandAllocator<Str, So, T, C> {
    fn allocate_command(&mut self, t: Command<Str, So, T>) -> C;

    gen_ctors!(allocate_command -> C
    | Command::Assert(t: T)
    | Command::CheckSat()
    | Command::CheckSatAssuming(terms: Vec<T>)
    | Command::DeclareConst(n: Str, s: So)
    | Command::DeclareDatatype(name: Str, dec: DatatypeDec<Str, So>)
    | Command::DeclareDatatypes(defs: Vec<DatatypeDef<Str, So>>)
    | Command::DeclareFun(f: Str, ss: Vec<So>, o: So)
    | Command::DeclareSort(n: Str, arity: usize)
    | Command::DefineConst(n: Str, s: So, t: T)
    | Command::DefineFun(fd: FunctionDef<Str, So, T>)
    | Command::DefineFunRec(fd: FunctionDef<Str, So, T>)
    | Command::DefineFunsRec(fd: Vec<FunctionDef<Str, So, T>>)
    | Command::DefineSort(n: Str, params: Vec<Str>, sort: So)
    | Command::Echo(s: Str)
    | Command::Exit()
    | Command::GetAssertions()
    | Command::GetAssignment()
    | Command::GetInfo(kw: Keyword)
    | Command::GetModel()
    | Command::GetOption(kw: Keyword)
    | Command::GetProof()
    | Command::GetUnsatAssumptions()
    | Command::GetUnsatCore()
    | Command::GetValue(ts: Vec<T>)
    | Command::Pop(n: UBig)
    | Command::Push(n: UBig)
    | Command::Reset()
    | Command::ResetAssertions()
    | Command::SetInfo(ats: Attribute<Str, T>)
    | Command::SetLogic(logic: Str)
    | Command::SetOption(ats: Attribute<Str, T>)
    );
}

pub trait LocalVarAllocator {
    fn new_local(&mut self) -> usize;
}

/// Extension trait for more functions
pub trait ObjectAllocatorExt<So, T>:
    StrAllocator + SortAllocator<Self::Str, So> + TermAllocator<Self::Str, So, T>
{
    fn simple_sort(&mut self, s: &str) -> So {
        let s = self.allocate_symbol(s);
        self.sort0(s)
    }

    fn bool_sort(&mut self) -> So {
        self.simple_sort(BOOL)
    }

    fn int_sort(&mut self) -> So {
        self.simple_sort(INT)
    }

    fn real_sort(&mut self) -> So {
        self.simple_sort(REAL)
    }

    fn string_sort(&mut self) -> So {
        self.simple_sort(STRING)
    }

    fn reglan_sort(&mut self) -> So {
        self.simple_sort(REGLAN)
    }

    fn array_sort(&mut self, from: So, to: So) -> So {
        let arr = self.allocate_symbol(ARRAY);
        self.allocate_sort(Sort(Identifier::simple(arr), vec![from, to]))
    }

    fn bv_sort(&mut self, len: UBig) -> So {
        let symbol = self.allocate_symbol(BITVEC);
        let id = Identifier {
            symbol,
            indices: vec![Index::Numeral(len)],
        };
        self.sort(id, vec![])
    }

    /// Return a symbol of sort Bool
    fn simple_symbol(&mut self, s: &str) -> T
    where
        So: Clone,
    {
        let b = self.bool_sort();
        self.simple_sorted_symbol(s, b)
    }

    /// Return a symbol of a given sort
    fn simple_sorted_symbol(&mut self, s: &str, sort: So) -> T
    where
        So: Clone,
    {
        let s = self.allocate_symbol(s);
        self.global(QualifiedIdentifier::simple(s), Some(sort))
    }

    fn bool(&mut self, b: bool) -> T {
        let bs = self.bool_sort();
        self.allocate_term(Term::Constant(Constant::Bool(b), Some(bs)))
    }

    fn get_true(&mut self) -> T {
        self.bool(true)
    }

    fn get_false(&mut self) -> T {
        self.bool(false)
    }
}

impl<So, T, X> ObjectAllocatorExt<So, T> for X where
    X: StrAllocator + SortAllocator<Self::Str, So> + TermAllocator<Self::Str, So, T>
{
}
