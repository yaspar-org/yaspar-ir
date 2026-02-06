#[macro_export]
macro_rules! instantiate_ast {
    ($Wrapper: ident) => {
        use $crate::wrapper_type;

        pub type Str = $Wrapper<String>;

        pub type Constant = $crate::raw::alg::Constant<Str>;

        pub type Index = $crate::raw::alg::Index<Str>;

        pub type Identifier = $crate::raw::alg::Identifier<Str>;

        pub type Attribute = $crate::raw::alg::Attribute<Str, Term>;

        pub type Sort = $Wrapper<RSort>;

        pub type Local = $crate::raw::alg::Local<Str, Sort>;

        pub type SigIndex = $crate::raw::alg::SigIndex<Str>;

        pub type BvInSort = $crate::raw::alg::BvInSort<Sort>;

        pub type BvOutSort = $crate::raw::alg::BvOutSort<Sort>;

        pub type Sig = $crate::raw::alg::Sig<Str, Sort>;

        wrapper_type!(RSort, $crate::raw::alg::Sort<Str, Sort>);

        pub type QualifiedIdentifier = $crate::raw::alg::QualifiedIdentifier<Str, Sort>;

        pub type Pattern = $crate::raw::alg::Pattern<Str>;

        pub type PatternArm = $crate::raw::alg::PatternArm<Str, Term>;

        pub type SortDef = $crate::raw::alg::SortDef<Str, Sort>;

        pub type ConstructorDec = $crate::raw::alg::ConstructorDec<Str, Sort>;

        pub type DatatypeDec = $crate::raw::alg::DatatypeDec<Str, Sort>;

        pub type DatatypeDef = $crate::raw::alg::DatatypeDef<Str, Sort>;

        pub type FunctionDef = $crate::raw::alg::FunctionDef<Str, Sort, Term>;

        pub type Term = $Wrapper<RTerm>;

        wrapper_type!(RTerm, $crate::raw::alg::Term<Str, Sort, Term>);

        wrapper_type!(RCommand, $crate::raw::alg::Command<Str, Sort, Term>);

        pub type Command = $Wrapper<RCommand>;
    };
}
