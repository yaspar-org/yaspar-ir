// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! This module instantiates untyped AST

use crate::allocator::StrAllocator;
use crate::ast::{alg, ACommand, AConstant, AIndex, ATerm, HasArenaAlt};
use crate::instantiate_ast;
use crate::meta::WithMeta;
use crate::raw::alg::CheckIdentifier;
use crate::traits::{Allocatable, Contains, MetaData};
use dashu::float::DBig;
use dashu::integer::UBig;
use lalrpop_util::ParseError;
use num_traits::ToPrimitive;
use std::fmt::{Debug, Display};
use std::ops::Deref;
use std::rc::Rc;
use yaspar::action::{
    ActionOnAttribute, ActionOnConstant, ActionOnIdentifier, ActionOnIndex, ActionOnSort,
    ActionOnString, ActionOnTerm, ParsingAction, ParsingResult, Pattern as ActionOnPattern,
};
use yaspar::ast::{GrammarError, Keyword};
use yaspar::position::Range;
use yaspar::smtlib2::{CommandParser, ScriptParser, SortParser, TermParser};
use yaspar::Tokenizer;

/// An untyped object is an object with associated location information
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Untyped<T>(Rc<WithMeta<T, Range>>);

impl<T> Display for Untyped<T>
where
    T: Display,
{
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.data.fmt(f)
    }
}

impl<T> Debug for Untyped<T>
where
    T: Debug,
{
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.data.fmt(f)
    }
}

impl<T> Deref for Untyped<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0.data
    }
}

impl<T> Contains for Untyped<T> {
    type T = T;

    #[inline]
    fn inner(&self) -> &Self::T {
        &self.0.data
    }
}

impl<T> MetaData for Untyped<T> {
    type T = Range;

    #[inline]
    fn meta_data(&self) -> &Self::T {
        &self.0.meta
    }

    fn display_meta_data(&self) -> String {
        let range = self.meta_data();
        format!(
            " {}:{}-{}:{}",
            range.start.lin_num, range.start.col_num, range.end.lin_num, range.end.col_num
        )
    }
}

type P<T> = Untyped<T>;

instantiate_ast!(P);

impl<Env: HasArenaAlt> Allocatable<Env> for Str {
    type Out = crate::ast::Str;

    fn allocate(&self, env: &mut Env) -> Self::Out {
        env.arena_alt().allocate_symbol(self.as_str())
    }
}

fn wrap<T>(t: T, range: Range) -> P<T> {
    Untyped(Rc::new(WithMeta::new(t, range)))
}

pub struct UntypedAst;

impl ActionOnString for UntypedAst {
    type Str = Str;

    fn on_string(&mut self, range: Range, s: String) -> ParsingResult<Self::Str> {
        Ok(wrap(s, range))
    }
}

impl ActionOnConstant for UntypedAst {
    type Constant = Constant;

    fn on_constant_binary(
        &mut self,
        _range: Range,
        bytes: Vec<u8>,
        len: usize,
    ) -> ParsingResult<Self::Constant> {
        Ok(AConstant::Binary(bytes, len))
    }

    fn on_constant_hexadecimal(
        &mut self,
        _range: Range,
        bytes: Vec<u8>,
        len: usize,
    ) -> ParsingResult<Self::Constant> {
        Ok(AConstant::Hexadecimal(bytes, len))
    }

    fn on_constant_decimal(
        &mut self,
        _range: Range,
        decimal: DBig,
    ) -> ParsingResult<Self::Constant> {
        Ok(AConstant::Decimal(decimal))
    }

    fn on_constant_numeral(
        &mut self,
        _range: Range,
        numeral: UBig,
    ) -> ParsingResult<Self::Constant> {
        Ok(AConstant::Numeral(numeral))
    }

    fn on_constant_string(
        &mut self,
        _range: Range,
        string: Self::Str,
    ) -> ParsingResult<Self::Constant> {
        Ok(AConstant::String(string))
    }

    fn on_constant_bool(&mut self, _range: Range, boolean: bool) -> ParsingResult<Self::Constant> {
        Ok(AConstant::Bool(boolean))
    }
}

impl ActionOnIndex for UntypedAst {
    type Index = Index;

    fn on_index_numeral(&mut self, _range: Range, index: UBig) -> ParsingResult<Self::Index> {
        Ok(AIndex::Numeral(index))
    }

    fn on_index_symbol(&mut self, _range: Range, index: Str) -> ParsingResult<Self::Index> {
        Ok(AIndex::Symbol(index))
    }

    fn on_index_hexadecimal(
        &mut self,
        _range: Range,
        bytes: Vec<u8>,
        len: usize,
    ) -> ParsingResult<Self::Index> {
        Ok(AIndex::Hexadecimal(bytes, len))
    }
}

impl ActionOnIdentifier for UntypedAst {
    type Identifier = Identifier;

    fn on_identifier(
        &mut self,
        _range: Range,
        symbol: Self::Str,
        indices: Vec<Self::Index>,
    ) -> ParsingResult<Self::Identifier> {
        Ok(alg::Identifier { symbol, indices })
    }
}

impl ActionOnAttribute for UntypedAst {
    type Term = Term;
    type Attribute = Attribute;

    fn on_attribute_keyword(
        &mut self,
        _range: Range,
        keyword: Keyword,
    ) -> ParsingResult<Self::Attribute> {
        Ok(Attribute::Keyword(keyword))
    }

    fn on_attribute_constant(
        &mut self,
        _range: Range,
        keyword: Keyword,
        constant: Self::Constant,
    ) -> ParsingResult<Self::Attribute> {
        Ok(Attribute::Constant(keyword, constant))
    }

    fn on_attribute_symbol(
        &mut self,
        _range: Range,
        keyword: Keyword,
        symbol: Self::Str,
    ) -> ParsingResult<Self::Attribute> {
        Ok(Attribute::Symbol(keyword, symbol))
    }

    fn on_attribute_named(
        &mut self,
        _range: Range,
        name: Self::Str,
    ) -> ParsingResult<Self::Attribute> {
        Ok(Attribute::Named(name))
    }

    fn on_attribute_pattern(
        &mut self,
        _range: Range,
        patterns: Vec<Self::Term>,
    ) -> ParsingResult<Self::Attribute> {
        Ok(Attribute::Pattern(patterns))
    }
}

impl ActionOnSort for UntypedAst {
    type Sort = Sort;

    fn on_sort(
        &mut self,
        range: Range,
        identifier: Self::Identifier,
        args: Vec<Self::Sort>,
    ) -> ParsingResult<Self::Sort> {
        Ok(wrap(alg::Sort(identifier, args).into(), range))
    }
}

fn conv_pattern<T>(pattern: ActionOnPattern<T>) -> alg::Pattern<T> {
    match pattern {
        ActionOnPattern::Single(name) => alg::Pattern::Wildcard(name.map(|w| (w, 0))),
        ActionOnPattern::Applied { head, tail } => alg::Pattern::Applied {
            ctor: head,
            arguments: tail.into_iter().map(|s| s.map(|t| (t, 0))).collect(),
        },
    }
}

impl ActionOnTerm for UntypedAst {
    fn on_term_constant(
        &mut self,
        range: Range,
        constant: Self::Constant,
    ) -> ParsingResult<Self::Term> {
        Ok(wrap(ATerm::Constant(constant, None).into(), range))
    }

    fn on_term_identifier(
        &mut self,
        range: Range,
        identifier: Self::Identifier,
        sort: Option<Self::Sort>,
    ) -> ParsingResult<Self::Term> {
        Ok(wrap(
            ATerm::Global(alg::QualifiedIdentifier(identifier, sort), None).into(),
            range,
        ))
    }

    fn on_term_app(
        &mut self,
        range: Range,
        identifier: Self::Identifier,
        sort: Option<Self::Sort>,
        mut args: Vec<Self::Term>,
    ) -> ParsingResult<Self::Term> {
        match identifier.get_kind() {
            None => Ok(wrap(
                ATerm::App(alg::QualifiedIdentifier(identifier, sort), args, None).into(),
                range,
            )),
            Some(kind) => match kind {
                IdentifierKind::And => {
                    if !args.is_empty() {
                        Ok(wrap(ATerm::And(args).into(), range))
                    } else {
                        Err(ParseError::User {
                            error: GrammarError::Other {
                                range,
                                message: "Parsing: 'and' should be given at least one argument!"
                                    .into(),
                            },
                        })
                    }
                }
                IdentifierKind::Or => {
                    if !args.is_empty() {
                        Ok(wrap(ATerm::Or(args).into(), range))
                    } else {
                        Err(ParseError::User {
                            error: GrammarError::Other {
                                range,
                                message: "Parsing: 'or' should be given at least one argument!"
                                    .into(),
                            },
                        })
                    }
                }
                IdentifierKind::Not => {
                    if args.len() != 1 {
                        Err(ParseError::User {
                            error: GrammarError::Other {
                                range,
                                message: "Parsing: 'not' takes exactly one argument!".into(),
                            },
                        })
                    } else {
                        Ok(wrap(ATerm::Not(args.remove(0)).into(), range))
                    }
                }
                IdentifierKind::Implies => {
                    match args.pop() {
                        None => {}
                        Some(rt) => {
                            if !args.is_empty() {
                                return Ok(wrap(ATerm::Implies(args, rt).into(), range));
                            }
                        }
                    }
                    Err(ParseError::User {
                        error: GrammarError::Other {
                            range,
                            message:
                                "Parsing: implications => should be given at least two argument!"
                                    .into(),
                        },
                    })
                }
                IdentifierKind::Eq => {
                    if args.len() != 2 {
                        Err(ParseError::User {
                            error: GrammarError::Other {
                                range,
                                message: "Parsing: '=' takes exactly two argument!".into(),
                            },
                        })
                    } else {
                        Ok(wrap(
                            ATerm::Eq(args.remove(0), args.remove(0)).into(),
                            range,
                        ))
                    }
                }
                IdentifierKind::Distinct => {
                    if args.len() < 2 {
                        Err(ParseError::User {
                            error: GrammarError::Other {
                                range,
                                message:
                                    "Parsing: 'distinct' should be given at least two arguments!"
                                        .into(),
                            },
                        })
                    } else {
                        Ok(wrap(ATerm::Distinct(args).into(), range))
                    }
                }
                IdentifierKind::Ite => {
                    if args.len() != 3 {
                        Err(ParseError::User {
                            error: GrammarError::Other {
                                range,
                                message: "Parsing: 'ite' takes exactly three argument!".into(),
                            },
                        })
                    } else {
                        Ok(wrap(
                            ATerm::Ite(args.remove(0), args.remove(0), args.remove(0)).into(),
                            range,
                        ))
                    }
                }
                _ => Ok(wrap(
                    ATerm::App(alg::QualifiedIdentifier(identifier, sort), args, None).into(),
                    range,
                )),
            },
        }
    }

    fn on_term_let(
        &mut self,
        range: Range,
        bindings: Vec<(Self::Str, Self::Term)>,
        body: Self::Term,
    ) -> ParsingResult<Self::Term> {
        Ok(wrap(
            ATerm::Let(
                bindings
                    .into_iter()
                    .map(|(n, t)| alg::VarBinding(n, 0, t))
                    .collect(),
                body,
            )
            .into(),
            range,
        ))
    }

    fn on_term_lambda(
        &mut self,
        range: Range,
        _names: Vec<(Self::Str, Self::Sort)>,
        _body: Self::Term,
    ) -> ParsingResult<Self::Term> {
        Err(ParseError::User {
            error: GrammarError::Other {
                range,
                message: "Parsing: 'lambda' is not supported yet!".into(),
            },
        })
    }

    fn on_term_exists(
        &mut self,
        range: Range,
        names: Vec<(Self::Str, Self::Sort)>,
        body: Self::Term,
    ) -> ParsingResult<Self::Term> {
        Ok(wrap(
            ATerm::Exists(
                names
                    .into_iter()
                    .map(|(n, s)| alg::VarBinding(n, 0, s))
                    .collect(),
                body,
            )
            .into(),
            range,
        ))
    }

    fn on_term_forall(
        &mut self,
        range: Range,
        names: Vec<(Self::Str, Self::Sort)>,
        body: Self::Term,
    ) -> ParsingResult<Self::Term> {
        Ok(wrap(
            ATerm::Forall(
                names
                    .into_iter()
                    .map(|(n, s)| alg::VarBinding(n, 0, s))
                    .collect(),
                body,
            )
            .into(),
            range,
        ))
    }

    fn on_term_match(
        &mut self,
        range: Range,
        scrutinee: Self::Term,
        cases: Vec<(ActionOnPattern<Self::Str>, Self::Term)>,
    ) -> ParsingResult<Self::Term> {
        Ok(wrap(
            ATerm::Matching(
                scrutinee,
                cases
                    .into_iter()
                    .map(|(pat, body)| PatternArm {
                        pattern: conv_pattern(pat),
                        body,
                    })
                    .collect(),
            )
            .into(),
            range,
        ))
    }

    fn on_term_annotated(
        &mut self,
        range: Range,
        t: Self::Term,
        attributes: Vec<Self::Attribute>,
    ) -> ParsingResult<Self::Term> {
        Ok(wrap(ATerm::Annotated(t, attributes).into(), range))
    }
}

fn datatype_dec_conv<Str, S>(
    datatype: yaspar::ast::DatatypeDec<Str, S>,
) -> alg::DatatypeDec<Str, S> {
    alg::DatatypeDec {
        params: datatype.params,
        constructors: datatype
            .constructors
            .into_iter()
            .map(|c| alg::ConstructorDec {
                ctor: c.0,
                args: c
                    .1
                    .into_iter()
                    .map(|a| alg::VarBinding(a.0, 0, a.1))
                    .collect(),
            })
            .collect(),
    }
}

fn function_def_conv<Str, S, T>(
    definition: yaspar::ast::FunctionDef<Str, S, T>,
) -> alg::FunctionDef<Str, S, T> {
    alg::FunctionDef {
        name: definition.name,
        vars: definition
            .vars
            .into_iter()
            .map(|(n, s)| alg::VarBinding(n, 0, s))
            .collect(),
        out_sort: definition.out_sort,
        body: definition.body,
    }
}

impl ParsingAction for UntypedAst {
    type Command = Command;

    fn on_command_assert(&mut self, range: Range, t: Self::Term) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::Assert(t).into(), range))
    }

    fn on_command_check_sat(&mut self, range: Range) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::CheckSat.into(), range))
    }

    fn on_command_check_sat_assuming(
        &mut self,
        range: Range,
        terms: Vec<Self::Term>,
    ) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::CheckSatAssuming(terms).into(), range))
    }

    fn on_command_declare_const(
        &mut self,
        range: Range,
        name: Self::Str,
        sort: Self::Sort,
    ) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::DeclareConst(name, sort).into(), range))
    }

    fn on_command_declare_datatype(
        &mut self,
        range: Range,
        name: Self::Str,
        datatype: yaspar::ast::DatatypeDec<Self::Str, Self::Sort>,
    ) -> ParsingResult<Self::Command> {
        Ok(wrap(
            ACommand::DeclareDatatype(name, datatype_dec_conv(datatype)).into(),
            range,
        ))
    }

    fn on_command_declare_datatypes(
        &mut self,
        range: Range,
        defs: Vec<yaspar::ast::DatatypeDef<Self::Str, Self::Sort>>,
    ) -> ParsingResult<Self::Command> {
        Ok(wrap(
            ACommand::DeclareDatatypes(
                defs.into_iter()
                    .map(|def| alg::DatatypeDef {
                        name: def.name,
                        dec: datatype_dec_conv(def.dec),
                    })
                    .collect(),
            )
            .into(),
            range,
        ))
    }

    fn on_command_declare_fun(
        &mut self,
        range: Range,
        name: Self::Str,
        input_sorts: Vec<Self::Sort>,
        out_sort: Self::Sort,
    ) -> ParsingResult<Self::Command> {
        Ok(wrap(
            ACommand::DeclareFun(name, input_sorts, out_sort).into(),
            range,
        ))
    }

    fn on_command_declare_sort(
        &mut self,
        range: Range,
        name: Self::Str,
        arity: UBig,
    ) -> ParsingResult<Self::Command> {
        match arity.to_usize() {
            None => Err(ParseError::User {
                error: GrammarError::Other {
                    range,
                    message: format!("arity {} is too large!", arity),
                },
            }),
            Some(arity) => Ok(wrap(ACommand::DeclareSort(name, arity).into(), range)),
        }
    }

    fn on_command_declare_sort_parameter(
        &mut self,
        range: Range,
        _name: Self::Str,
    ) -> ParsingResult<Self::Command> {
        Err(ParseError::User {
            error: GrammarError::Other {
                range,
                message: "Parsing: 'declare-sort-parameter' is not supported yet!".into(),
            },
        })
    }

    fn on_command_define_const(
        &mut self,
        range: Range,
        name: Self::Str,
        sort: Self::Sort,
        term: Self::Term,
    ) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::DefineConst(name, sort, term).into(), range))
    }

    fn on_command_define_fun(
        &mut self,
        range: Range,
        definition: yaspar::ast::FunctionDef<Self::Str, Self::Sort, Self::Term>,
    ) -> ParsingResult<Self::Command> {
        Ok(wrap(
            ACommand::DefineFun(function_def_conv(definition)).into(),
            range,
        ))
    }

    fn on_command_define_fun_rec(
        &mut self,
        range: Range,
        definition: yaspar::ast::FunctionDef<Self::Str, Self::Sort, Self::Term>,
    ) -> ParsingResult<Self::Command> {
        Ok(wrap(
            ACommand::DefineFunRec(function_def_conv(definition)).into(),
            range,
        ))
    }

    fn on_command_define_funs_rec(
        &mut self,
        range: Range,
        definitions: Vec<yaspar::ast::FunctionDef<Self::Str, Self::Sort, Self::Term>>,
    ) -> ParsingResult<Self::Command> {
        Ok(wrap(
            ACommand::DefineFunsRec(definitions.into_iter().map(function_def_conv).collect())
                .into(),
            range,
        ))
    }

    fn on_command_define_sort(
        &mut self,
        range: Range,
        name: Self::Str,
        params: Vec<Self::Str>,
        sort: Self::Sort,
    ) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::DefineSort(name, params, sort).into(), range))
    }

    fn on_command_echo(&mut self, range: Range, s: Self::Str) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::Echo(s).into(), range))
    }

    fn on_command_exit(&mut self, range: Range) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::Exit.into(), range))
    }

    fn on_command_get_assertions(&mut self, range: Range) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::GetAssertions.into(), range))
    }

    fn on_command_get_assignment(&mut self, range: Range) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::GetAssignment.into(), range))
    }

    fn on_command_get_info(&mut self, range: Range, kw: Keyword) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::GetInfo(kw).into(), range))
    }

    fn on_command_get_model(&mut self, range: Range) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::GetModel.into(), range))
    }

    fn on_command_get_option(&mut self, range: Range, kw: Keyword) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::GetOption(kw).into(), range))
    }

    fn on_command_get_proof(&mut self, range: Range) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::GetProof.into(), range))
    }

    fn on_command_get_unsat_assumptions(&mut self, range: Range) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::GetUnsatAssumptions.into(), range))
    }

    fn on_command_get_unsat_core(&mut self, range: Range) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::GetUnsatCore.into(), range))
    }

    fn on_command_get_value(
        &mut self,
        range: Range,
        ts: Vec<Self::Term>,
    ) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::GetValue(ts).into(), range))
    }

    fn on_command_pop(&mut self, range: Range, lvl: UBig) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::Pop(lvl).into(), range))
    }

    fn on_command_push(&mut self, range: Range, lvl: UBig) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::Push(lvl).into(), range))
    }

    fn on_command_reset(&mut self, range: Range) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::Reset.into(), range))
    }

    fn on_command_reset_assertions(&mut self, range: Range) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::ResetAssertions.into(), range))
    }

    fn on_command_set_info(
        &mut self,
        range: Range,
        attributes: Self::Attribute,
    ) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::SetInfo(attributes).into(), range))
    }

    fn on_command_set_logic(
        &mut self,
        range: Range,
        logic: Self::Str,
    ) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::SetLogic(logic).into(), range))
    }

    fn on_command_set_option(
        &mut self,
        range: Range,
        attribute: Self::Attribute,
    ) -> ParsingResult<Self::Command> {
        Ok(wrap(ACommand::SetOption(attribute).into(), range))
    }
}

impl UntypedAst {
    pub fn parse_script<T>(&mut self, iter: T) -> ParsingResult<Vec<Command>>
    where
        T: Iterator<Item = char>,
    {
        ScriptParser::new().parse(self, Tokenizer::new(iter, false))
    }

    pub fn parse_command<T>(&mut self, iter: T) -> ParsingResult<Command>
    where
        T: Iterator<Item = char>,
    {
        CommandParser::new().parse(self, Tokenizer::new(iter, false))
    }

    pub fn parse_term<T>(&mut self, iter: T) -> ParsingResult<Term>
    where
        T: Iterator<Item = char>,
    {
        TermParser::new().parse(self, Tokenizer::new(iter, false))
    }

    pub fn parse_sort<T>(&mut self, iter: T) -> ParsingResult<Sort>
    where
        T: Iterator<Item = char>,
    {
        SortParser::new().parse(self, Tokenizer::new(iter, false))
    }

    pub fn parse_script_str(&mut self, s: &str) -> ParsingResult<Vec<Command>> {
        self.parse_script(s.chars())
    }

    pub fn parse_command_str(&mut self, s: &str) -> ParsingResult<Command> {
        self.parse_command(s.chars())
    }

    pub fn parse_term_str(&mut self, s: &str) -> ParsingResult<Term> {
        self.parse_term(s.chars())
    }
    pub fn parse_sort_str(&mut self, s: &str) -> ParsingResult<Sort> {
        self.parse_sort(s.chars())
    }
}
