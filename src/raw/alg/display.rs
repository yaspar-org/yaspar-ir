// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Printing of terms and sorts, with a length budget.
//!
//! A term is a DAG of unbounded depth, so printing it by recursing natively overflows the stack on
//! machine-generated input, and printing it in full is not what a diagnostic wants: the interesting
//! part of a 90 MB assertion is its first line. This module answers both, for every instantiation of
//! the grammar in [`crate::raw::alg`] — the bounds ask only that a child can be unwrapped to its own
//! node, which is what the typed and the untyped AST each provide.
//!
//! # The document
//!
//! A document is a [`Tree`]: a leaf holds a token, and a node holds a forest which prints
//! parenthesised, its members separated by a space. So `(and x y)` is a node over three leaves, and
//! the shape of the document is the shape of the term.
//!
//! [`WorkSpace`] builds one. It keeps the *tail* of the document — the forests still open, i.e. its
//! right spine — in a `Vec`, together with the size of what has been emitted. Printing does two
//! things to it: push a leaf onto the innermost forest, or, once a parenthesised group is finished,
//! pop that forest, wrap it in a [`Tree::Node`], and push it onto the forest beneath. When the scan
//! finishes, one forest is left holding one tree, and that tree is the document.
//!
//! # The budget
//!
//! [`PrintConfig::max_length`] caps [`WorkSpace::size`], which counts parentheses and separators as
//! well as tokens, so it tracks what the document will render to. It is checked after each token, so
//! the cap holds to within one token: once it is spent the descent returns [`Elided`], which unwinds
//! to [`WorkSpace::finish`], where the marker `...` is pushed and every open forest is closed — so a
//! cut-short document is still a tree, still balances, and says so where it was cut. Nothing past the cut is ever visited, so
//! printing the first 200 bytes of a huge term costs about 200 bytes of work.
//!
//! # Depth
//!
//! The two descents and the rendering of the tree they build all carry `#[stack_safe]`, so their
//! recursion lives on the heap. Each descent is a single function rather than a group of them, which
//! is what keeps one driver for the whole walk: a term descends into a sort but never the other way
//! round, so a term that mentions a sort costs one nested driver, not one per level.

use crate::raw::alg::{self, StrQuote, SymbolQuote};
use crate::statics::{ADD, AND, BITVEC, DISTINCT, EQ, IMPLIES, ITE, MUL, NOT, OR, SUB, XOR};
use crate::traits::{Contains, Repr};
use dashu::base::Sign;
use num_traits::Signed;
use std::fmt::Write;
use yaspar::ast::Keyword;
use yaspar::tokens::{Command as CommandName, Token};
use yaspar::{binary_to_string, hex_to_string};
use yaspar_macros::stack_safe;

/// The marker pushed where a document was cut short.
const ELLIPSIS: &str = "...";

/// What a signature calls the list of indices a symbol admits.
const INDICES: &str = "indices:";

/// How a signature spells a position that admits any literal of a reserved kind, e.g. `<NUMERAL>`.
fn reserved(t: Token) -> String {
    format!("<{t}>")
}

/// How a signature spells the lower bound on a variadic function's arity.
fn at_least(n: usize) -> String {
    format!("...[>= {n} times]")
}

/// How much of a term to print.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrintConfig {
    /// Stop once the document has reached this many bytes, or print all of it when [`None`].
    ///
    /// The cap holds to within one token, since it is checked between tokens.
    pub max_length: Option<usize>,
}

impl PrintConfig {
    /// Print the whole term, however large.
    pub const UNLIMITED: Self = Self { max_length: None };

    /// Print at most `max_length` bytes.
    pub const fn limited(max_length: usize) -> Self {
        Self {
            max_length: Some(max_length),
        }
    }
}

impl Default for PrintConfig {
    fn default() -> Self {
        Self::UNLIMITED
    }
}

/// A printed document: a leaf is a token, and a node is a parenthesised forest.
///
/// It is the printer's own scaffolding: [`Print`] hands back the text it renders to.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Tree {
    /// One token of output: a symbol, a literal, a keyword.
    Leaf(String),
    /// A group, which renders as its members in parentheses, separated by spaces.
    Node(Vec<Tree>),
}

/// Tear a document down iteratively, since it is as deep as the term it came from.
impl Drop for Tree {
    fn drop(&mut self) {
        let Tree::Node(forest) = self else { return };
        let mut pending = std::mem::take(forest);
        while let Some(mut t) = pending.pop() {
            if let Tree::Node(forest) = &mut t {
                // draining the group leaves nothing for `t`'s own drop to recurse into
                pending.append(forest);
            }
        }
    }
}

/// Render a document, without recursing natively: it is as deep as its term.
#[stack_safe]
fn write_tree<W: Write>(t: &Tree, out: &mut W) -> std::fmt::Result {
    match t {
        Tree::Leaf(s) => out.write_str(s),
        Tree::Node(forest) => {
            out.write_char('(')?;
            let mut i = 0usize;
            while i < forest.len() {
                if i > 0 {
                    out.write_char(' ')?;
                }
                write_tree(&forest[i], out)?;
                i += 1;
            }
            out.write_char(')')
        }
    }
}

/// Render a forest: its members, separated by a space.
///
/// Only a [`Tree::Node`] brings parentheses, so a document that is a forest — a function definition,
/// an annotation — prints as a sequence, which is what the grammar asks for.
fn render(forest: &[Tree]) -> String {
    let mut out = String::new();
    let mut i = 0usize;
    while i < forest.len() {
        if i > 0 {
            out.push(' ');
        }
        // writing into a String cannot fail
        let _ = write_tree(&forest[i], &mut out);
        i += 1;
    }
    out
}

/// Print `self`, by writing it into a document.
///
/// Writing is what an implementor supplies, which is what lets the grammar be printed generically: a
/// `VarBinding<Str, T>` or a `Sig<Str, So>` knows nothing about its payload beyond this, and both the
/// typed and the untyped AST supply it — a wrapper writes whatever it wraps. Rendering the document is
/// the same for all of them, so [`Print::print`] is a default.
pub trait Print {
    /// Push the tokens of `self` onto `w`, failing once its budget is spent.
    fn write_doc(&self, w: &mut WorkSpace) -> Res;

    /// Render to text, stopping once the budget in `config` is spent.
    ///
    /// Text that was cut short carries `...` where the budget ran out.
    fn print(&self, config: &PrintConfig) -> String {
        let mut w = WorkSpace::new(config);
        let cut = self.write_doc(&mut w).is_err();
        render(&w.finish(cut))
    }
}

impl<St, So, T> Print for alg::Term<St, So, T>
where
    St: StrQuote<String> + SymbolQuote<String>,
    So: Print + Contains<T: Repr<T = alg::Sort<St, So>>>,
    T: Contains<T: Repr<T = alg::Term<St, So, T>>>,
{
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        write_term(self, w)
    }
}

impl<St, So> Print for alg::Sort<St, So>
where
    St: SymbolQuote<String>,
    So: Contains<T: Repr<T = alg::Sort<St, So>>>,
{
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        write_sort(self, w)
    }
}

/// A wrapper writes what it wraps, which is how a handle of either AST is printed.
impl<X> Print for X
where
    X: Contains<T: Repr<T: Print>>,
{
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        self.inner().repr().write_doc(w)
    }
}

/// The budget ran out; unwinds the descent to [`WorkSpace::finish`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Elided;

/// What a step of a descent returns: `Err` means the budget is spent.
type Res = Result<(), Elided>;

/// A document under construction: what it will render to so far, and the forests still open.
pub struct WorkSpace {
    /// Length the document would render to, so far.
    sz: usize,
    /// The innermost forest, i.e. the one a tree is pushed onto.
    ///
    /// It is a field of its own rather than the end of `forests`, so that reaching it is neither a
    /// lookup nor a case to rule out.
    last: Vec<Tree>,
    /// The rest of the tail: the forest of each enclosing open group, outermost first.
    forests: Vec<Vec<Tree>>,
    /// Size at which to stop; [`usize::MAX`] when unlimited.
    limit: usize,
}

impl WorkSpace {
    /// A workspace that will honour `config`.
    pub fn new(config: &PrintConfig) -> Self {
        Self {
            sz: 0,
            // the outermost forest, which ends up holding the one tree that is the document
            last: Vec::new(),
            forests: Vec::new(),
            limit: config.max_length.unwrap_or(usize::MAX),
        }
    }

    /// Length the document would render to, so far.
    pub fn size(&self) -> usize {
        self.sz
    }

    /// How many groups are open.
    pub fn depth(&self) -> usize {
        self.forests.len()
    }

    /// Push a tree onto the innermost forest, charging for the separator in front of it.
    fn push(&mut self, t: Tree, len: usize) {
        let separator = usize::from(!self.last.is_empty());
        self.last.push(t);
        self.sz += len + separator;
    }

    /// Fail once the budget is spent, which unwinds the descent.
    fn check(&mut self) -> Res {
        if self.sz >= self.limit {
            Err(Elided)
        } else {
            Ok(())
        }
    }

    /// Push a leaf, i.e. one token of output.
    ///
    /// It takes either of the two forms a token arrives in: one of the grammar's fixed words, or text
    /// that had to be built, e.g. a quoted symbol.
    fn leaf(&mut self, s: impl Into<String>) -> Res {
        let s = s.into();
        let len = s.len();
        self.push(Tree::Leaf(s), len);
        self.check()
    }

    /// Print a parenthesised group: open it, let `f` fill it, then close it.
    ///
    /// A spent budget leaves the group open, which is what [`WorkSpace::finish`] expects.
    fn group(&mut self, f: impl FnOnce(&mut Self) -> Res) -> Res {
        self.open()?;
        f(self)?;
        self.close();
        Ok(())
    }

    /// Open a group: put the forest in progress aside and start one for the group.
    fn open(&mut self) -> Res {
        // its parentheses, and the separator in front of it if it has a predecessor
        self.sz += 2 + usize::from(!self.last.is_empty());
        self.forests.push(std::mem::take(&mut self.last));
        self.check()
    }

    /// Close the innermost group: wrap its forest and push it onto the one it was opened in.
    ///
    /// The parentheses were charged for by [`WorkSpace::open`], so closing costs nothing and cannot
    /// take the document over budget.
    fn close(&mut self) {
        // nothing to close unless a group was opened
        if let Some(enclosing) = self.forests.pop() {
            let forest = std::mem::replace(&mut self.last, enclosing);
            self.last.push(Tree::Node(forest));
        }
    }

    /// Finish, closing whatever the descent left open.
    ///
    /// `cut` says whether the descent stopped early, in which case the marker goes into the innermost
    /// group before the rest are closed, so that the document reads as a prefix of the whole.
    fn finish(mut self, cut: bool) -> Vec<Tree> {
        if cut {
            // already over budget, so there is nothing left to check
            let _ = self.leaf(ELLIPSIS);
        }
        while !self.forests.is_empty() {
            self.close();
        }
        self.last
    }
}

/// Print a constant literal.
fn write_constant<St>(c: &alg::Constant<St>, w: &mut WorkSpace) -> Res
where
    St: StrQuote<String>,
{
    match c {
        alg::Constant::Numeral(n) => w.leaf(n.to_string()),
        // a negative decimal is a term, i.e. `(- 1.5)`
        alg::Constant::Decimal(r) => {
            let abs = r.abs();
            let body = if r.floor() == *r {
                format!("{abs}.0")
            } else {
                format!("{abs}")
            };
            if r.sign() == Sign::Negative {
                w.group(|w| {
                    w.leaf(SUB)?;
                    w.leaf(body)
                })
            } else {
                w.leaf(body)
            }
        }
        alg::Constant::String(s) => w.leaf(s.quote()),
        alg::Constant::Binary(bs, n) => w.leaf(format!("#b{}", binary_to_string(bs, *n))),
        alg::Constant::Hexadecimal(bs, n) => w.leaf(format!("#x{}", hex_to_string(bs, *n))),
        alg::Constant::Bool(true) => w.leaf(Token::True.to_string()),
        alg::Constant::Bool(false) => w.leaf(Token::False.to_string()),
    }
}

/// Print one index of an indexed identifier.
fn write_index<St>(i: &alg::Index<St>, w: &mut WorkSpace) -> Res
where
    St: SymbolQuote<String>,
{
    match i {
        alg::Index::Numeral(n) => w.leaf(n.to_string()),
        alg::Index::Symbol(s) => w.leaf(s.sym_quote()),
        alg::Index::Hexadecimal(bs, n) => w.leaf(format!("#x{}", hex_to_string(bs, *n))),
    }
}

/// Print an identifier: `f`, or `(_ f i …)` when it is indexed.
fn write_identifier<St>(id: &alg::Identifier<St>, w: &mut WorkSpace) -> Res
where
    St: SymbolQuote<String>,
{
    if id.indices.is_empty() {
        w.leaf(id.symbol.sym_quote())
    } else {
        w.group(|w| {
            w.leaf(Token::Underscore.to_string())?;
            w.leaf(id.symbol.sym_quote())?;
            let mut i = 0usize;
            while i < id.indices.len() {
                write_index(&id.indices[i], w)?;
                i += 1;
            }
            Ok(())
        })
    }
}

/// Print the pattern of a match arm.
fn write_pattern<St>(p: &alg::Pattern<St>, w: &mut WorkSpace) -> Res
where
    St: SymbolQuote<String>,
{
    match p {
        alg::Pattern::Wildcard(None) => w.leaf(Token::Underscore.to_string()),
        alg::Pattern::Wildcard(Some((sym, _))) => w.leaf(sym.sym_quote()),
        alg::Pattern::Ctor(s) => w.leaf(s.sym_quote()),
        alg::Pattern::Applied { ctor, arguments } => w.group(|w| {
            w.leaf(ctor.sym_quote())?;
            let mut i = 0usize;
            while i < arguments.len() {
                match &arguments[i] {
                    None => w.leaf(Token::Underscore.to_string())?,
                    Some((sym, _)) => w.leaf(sym.sym_quote())?,
                }
                i += 1;
            }
            Ok(())
        }),
    }
}

/// Print a signature index, i.e. what an indexed identifier admits in one position.
fn write_sig_index<St>(i: &alg::SigIndex<St>, w: &mut WorkSpace) -> Res
where
    St: SymbolQuote<String>,
{
    match i {
        alg::SigIndex::Numeral => w.leaf(reserved(Token::RWNumeral)),
        alg::SigIndex::Hexadecimal => w.leaf(reserved(Token::RWHexadecimal)),
        // a single admissible symbol is printed bare; a genuine choice is braced, and braces are not
        // the document's parentheses, so the choice is one token
        alg::SigIndex::Symbol(ss) => {
            let names = || ss.iter().map(|s| s.sym_quote());
            match ss.len() {
                1 => w.leaf(names().collect::<String>()),
                _ => w.leaf(format!("{{{}}}", names().collect::<Vec<_>>().join(" "))),
            }
        }
    }
}

/// Print a bit-vector length expression, e.g. the `(+ x0 x1)` of a concatenation.
#[stack_safe]
fn write_bv_len(e: &alg::BvLenExpr, w: &mut WorkSpace) -> Res {
    match e {
        alg::BvLenExpr::Fixed(n) => w.leaf(n.to_string()),
        alg::BvLenExpr::Var(n) => w.leaf(format!("x{n}")),
        alg::BvLenExpr::Add { left, right } => {
            w.open()?;
            w.leaf(ADD)?;
            write_bv_len(left.as_ref(), w)?;
            write_bv_len(right.as_ref(), w)?;
            w.close();
            Ok(())
        }
        alg::BvLenExpr::Sub { left, right } => {
            w.open()?;
            w.leaf(SUB)?;
            write_bv_len(left.as_ref(), w)?;
            write_bv_len(right.as_ref(), w)?;
            w.close();
            Ok(())
        }
        alg::BvLenExpr::Mul { left, right } => {
            w.open()?;
            w.leaf(MUL)?;
            write_bv_len(left.as_ref(), w)?;
            write_bv_len(right.as_ref(), w)?;
            w.close();
            Ok(())
        }
    }
}

/// Print a command, i.e. `(assert t)` and its kin.
fn write_command<St, So, T>(c: &alg::Command<St, So, T>, w: &mut WorkSpace) -> Res
where
    St: Clone + StrQuote<String> + SymbolQuote<String>,
    So: Contains<T: Repr<T = alg::Sort<St, So>>>,
    T: Contains<T: Repr<T = alg::Term<St, So, T>>>,
{
    w.group(|w| {
        match c {
            alg::Command::Assert(t) => {
                w.leaf(CommandName::Assert.to_string())?;
                write_term(t.inner().repr(), w)?;
            }
            alg::Command::CheckSat => w.leaf(CommandName::CheckSat.to_string())?,
            alg::Command::CheckSatAssuming(ts) => {
                w.leaf(CommandName::CheckSatAssuming.to_string())?;
                w.group(|w| {
                    for t in ts {
                        write_term(t.inner().repr(), w)?;
                    }
                    Ok(())
                })?;
            }
            alg::Command::DeclareConst(id, s) => {
                w.leaf(CommandName::DeclareConst.to_string())?;
                w.leaf(id.sym_quote())?;
                write_sort(s.inner().repr(), w)?;
            }
            alg::Command::DeclareDatatype(id, dec) => {
                w.leaf(CommandName::DeclareDatatype.to_string())?;
                w.leaf(id.sym_quote())?;
                dec.write_doc(w)?;
            }
            alg::Command::DeclareDatatypes(defs) => {
                w.leaf(CommandName::DeclareDatatypes.to_string())?;
                // each datatype is named with its arity, then declared
                w.group(|w| {
                    for d in defs {
                        w.group(|w| {
                            w.leaf(d.name.sym_quote())?;
                            w.leaf(d.dec.params.len().to_string())
                        })?;
                    }
                    Ok(())
                })?;
                w.group(|w| {
                    for d in defs {
                        d.dec.write_doc(w)?;
                    }
                    Ok(())
                })?;
            }
            alg::Command::DeclareFun(id, ss, s) => {
                w.leaf(CommandName::DeclareFun.to_string())?;
                w.leaf(id.sym_quote())?;
                w.group(|w| {
                    for x in ss {
                        write_sort(x.inner().repr(), w)?;
                    }
                    Ok(())
                })?;
                write_sort(s.inner().repr(), w)?;
            }
            alg::Command::DeclareSort(id, arity) => {
                w.leaf(CommandName::DeclareSort.to_string())?;
                w.leaf(id.sym_quote())?;
                w.leaf(arity.to_string())?;
            }
            alg::Command::DefineConst(sym, sort, term) => {
                w.leaf(CommandName::DefineConst.to_string())?;
                w.leaf(sym.sym_quote())?;
                write_sort(sort.inner().repr(), w)?;
                write_term(term.inner().repr(), w)?;
            }
            alg::Command::DefineFun(fd) => {
                w.leaf(CommandName::DefineFun.to_string())?;
                fd.write_doc(w)?;
            }
            alg::Command::DefineFunRec(fd) => {
                w.leaf(CommandName::DefineFunRec.to_string())?;
                fd.write_doc(w)?;
            }
            alg::Command::DefineFunsRec(fds) => {
                // the signatures first, then the bodies
                w.leaf(CommandName::DefineFunsRec.to_string())?;
                w.group(|w| {
                    for fd in fds {
                        w.group(|w| {
                            w.leaf(fd.name.sym_quote())?;
                            w.group(|w| {
                                for v in &fd.vars {
                                    v.write_doc(w)?;
                                }
                                Ok(())
                            })?;
                            write_sort(fd.out_sort.inner().repr(), w)
                        })?;
                    }
                    Ok(())
                })?;
                w.group(|w| {
                    for fd in fds {
                        write_term(fd.body.inner().repr(), w)?;
                    }
                    Ok(())
                })?;
            }
            alg::Command::DefineSort(name, params, sort) => {
                w.leaf(CommandName::DefineSort.to_string())?;
                w.leaf(name.sym_quote())?;
                w.group(|w| {
                    for p in params {
                        w.leaf(p.sym_quote())?;
                    }
                    Ok(())
                })?;
                write_sort(sort.inner().repr(), w)?;
            }
            alg::Command::Echo(s) => {
                w.leaf(CommandName::Echo.to_string())?;
                w.leaf(s.quote())?;
            }
            alg::Command::Exit => w.leaf(CommandName::Exit.to_string())?,
            alg::Command::GetAssertions => w.leaf(CommandName::GetAssertions.to_string())?,
            alg::Command::GetAssignment => w.leaf(CommandName::GetAssignment.to_string())?,
            alg::Command::GetInfo(kw) => {
                w.leaf(CommandName::GetInfo.to_string())?;
                w.leaf(kw.to_string())?;
            }
            alg::Command::GetModel => w.leaf(CommandName::GetModel.to_string())?,
            alg::Command::GetOption(kw) => {
                w.leaf(CommandName::GetOption.to_string())?;
                w.leaf(kw.to_string())?;
            }
            alg::Command::GetProof => w.leaf(CommandName::GetProof.to_string())?,
            alg::Command::GetUnsatAssumptions => {
                w.leaf(CommandName::GetUnsatAssumptions.to_string())?
            }
            alg::Command::GetUnsatCore => w.leaf(CommandName::GetUnsatCore.to_string())?,
            alg::Command::GetValue(ts) => {
                w.leaf(CommandName::GetValue.to_string())?;
                w.group(|w| {
                    for t in ts {
                        write_term(t.inner().repr(), w)?;
                    }
                    Ok(())
                })?;
            }
            alg::Command::Pop(i) => {
                w.leaf(CommandName::Pop.to_string())?;
                w.leaf(i.to_string())?;
            }
            alg::Command::Push(i) => {
                w.leaf(CommandName::Push.to_string())?;
                w.leaf(i.to_string())?;
            }
            alg::Command::Reset => w.leaf(CommandName::Reset.to_string())?,
            alg::Command::ResetAssertions => w.leaf(CommandName::ResetAssertions.to_string())?,
            alg::Command::SetInfo(at) => {
                w.leaf(CommandName::SetInfo.to_string())?;
                write_attribute(at, w)?;
            }
            alg::Command::SetLogic(l) => {
                w.leaf(CommandName::SetLogic.to_string())?;
                w.leaf(l.sym_quote())?;
            }
            alg::Command::SetOption(op) => {
                w.leaf(CommandName::SetOption.to_string())?;
                write_attribute(op, w)?;
            }
        }
        Ok(())
    })
}

/// Print a sort: `Int`, or `(Array Int Int)` when it has arguments.
///
/// One self-recursive function, so the whole descent shares one driver.
#[stack_safe]
fn write_sort<St, So>(node: &alg::Sort<St, So>, w: &mut WorkSpace) -> Res
where
    St: SymbolQuote<String>,
    So: Contains<T: Repr<T = alg::Sort<St, So>>>,
{
    if node.1.is_empty() {
        write_identifier(&node.0, w)
    } else {
        w.open()?;
        write_identifier(&node.0, w)?;
        let mut i = 0usize;
        while i < node.1.len() {
            write_sort(node.1[i].inner().repr(), w)?;
            i += 1;
        }
        w.close();
        Ok(())
    }
}

/// The descent over a term, i.e. the cycle a term and its annotations form.
///
/// They are members of one group so that a call between them is a step of the same driver: an
/// annotation holds terms, and a term holds annotations, to any depth.
#[stack_safe]
mod term {
    use super::*;

    /// Print a term.
    pub(super) fn write_term<St, So, T>(node: &alg::Term<St, So, T>, w: &mut WorkSpace) -> Res
    where
        St: StrQuote<String> + SymbolQuote<String>,
        So: Print + Contains<T: Repr<T = alg::Sort<St, So>>>,
        T: Contains<T: Repr<T = alg::Term<St, So, T>>>,
    {
        match node {
            alg::Term::Constant(c, _) => write_constant(c, w),
            alg::Term::Local(id) => w.leaf(id.symbol.sym_quote()),
            alg::Term::Global(id, _) => id.write_doc(w),
            // `(f a1 … an)`
            alg::Term::App(id, args, _) => {
                w.open()?;
                id.write_doc(w)?;
                let mut i = 0usize;
                while i < args.len() {
                    write_term(args[i].inner().repr(), w)?;
                    i += 1;
                }
                w.close();
                Ok(())
            }
            alg::Term::Eq(a, b) => {
                w.open()?;
                w.leaf(EQ)?;
                write_term(a.inner().repr(), w)?;
                write_term(b.inner().repr(), w)?;
                w.close();
                Ok(())
            }
            alg::Term::Not(t) => {
                w.open()?;
                w.leaf(NOT)?;
                write_term(t.inner().repr(), w)?;
                w.close();
                Ok(())
            }
            alg::Term::Ite(b, t, e) => {
                w.open()?;
                w.leaf(ITE)?;
                write_term(b.inner().repr(), w)?;
                write_term(t.inner().repr(), w)?;
                write_term(e.inner().repr(), w)?;
                w.close();
                Ok(())
            }
            alg::Term::Distinct(ts) => {
                w.open()?;
                w.leaf(DISTINCT)?;
                let mut i = 0usize;
                while i < ts.len() {
                    write_term(ts[i].inner().repr(), w)?;
                    i += 1;
                }
                w.close();
                Ok(())
            }
            alg::Term::And(ts) => {
                w.open()?;
                w.leaf(AND)?;
                let mut i = 0usize;
                while i < ts.len() {
                    write_term(ts[i].inner().repr(), w)?;
                    i += 1;
                }
                w.close();
                Ok(())
            }
            alg::Term::Or(ts) => {
                w.open()?;
                w.leaf(OR)?;
                let mut i = 0usize;
                while i < ts.len() {
                    write_term(ts[i].inner().repr(), w)?;
                    i += 1;
                }
                w.close();
                Ok(())
            }
            alg::Term::Xor(ts) => {
                w.open()?;
                w.leaf(XOR)?;
                let mut i = 0usize;
                while i < ts.len() {
                    write_term(ts[i].inner().repr(), w)?;
                    i += 1;
                }
                w.close();
                Ok(())
            }
            // `(=> p1 … pn q)`, i.e. the premises then the conclusion
            alg::Term::Implies(ts, r) => {
                w.open()?;
                w.leaf(IMPLIES)?;
                let mut i = 0usize;
                while i < ts.len() {
                    write_term(ts[i].inner().repr(), w)?;
                    i += 1;
                }
                write_term(r.inner().repr(), w)?;
                w.close();
                Ok(())
            }
            // `(let ((x e) …) body)`
            alg::Term::Let(vs, body) => {
                w.open()?;
                w.leaf(Token::Let.to_string())?;
                w.open()?;
                let mut i = 0usize;
                while i < vs.len() {
                    w.open()?;
                    w.leaf(vs[i].0.sym_quote())?;
                    write_term(vs[i].2.inner().repr(), w)?;
                    w.close();
                    i += 1;
                }
                w.close();
                write_term(body.inner().repr(), w)?;
                w.close();
                Ok(())
            }
            // `(exists ((x S) …) body)`
            alg::Term::Exists(vs, body) => {
                w.open()?;
                w.leaf(Token::Exists.to_string())?;
                w.open()?;
                let mut i = 0usize;
                while i < vs.len() {
                    w.open()?;
                    w.leaf(vs[i].0.sym_quote())?;
                    write_sort(vs[i].2.inner().repr(), w)?;
                    w.close();
                    i += 1;
                }
                w.close();
                write_term(body.inner().repr(), w)?;
                w.close();
                Ok(())
            }
            // `(forall ((x S) …) body)`
            alg::Term::Forall(vs, body) => {
                w.open()?;
                w.leaf(Token::Forall.to_string())?;
                w.open()?;
                let mut i = 0usize;
                while i < vs.len() {
                    w.open()?;
                    w.leaf(vs[i].0.sym_quote())?;
                    write_sort(vs[i].2.inner().repr(), w)?;
                    w.close();
                    i += 1;
                }
                w.close();
                write_term(body.inner().repr(), w)?;
                w.close();
                Ok(())
            }
            // `(! t :key val …)`
            alg::Term::Annotated(t, anns) => {
                w.open()?;
                w.leaf(Token::Exclamation.to_string())?;
                let count: usize = anns.len();
                write_term(t.inner().repr(), w)?;
                let mut i = 0usize;
                // this slice has to survive the descent above, and the macro cannot infer the type of
                // what travels in a payload: hence the length read before the call, and the name given
                // to the slice inside the loop
                while i < count {
                    let anns: &[alg::Attribute<St, T>] = anns;
                    write_attribute(&anns[i], w)?;
                    i += 1;
                }
                w.close();
                Ok(())
            }
            // `(match t ((p body) …))`
            alg::Term::Matching(scrutinee, arms) => {
                w.open()?;
                w.leaf(Token::Match.to_string())?;
                let count: usize = arms.len();
                write_term(scrutinee.inner().repr(), w)?;
                w.open()?;
                let mut i = 0usize;
                // spelled out for the same reason as the annotations above
                while i < count {
                    let arms: &[alg::PatternArm<St, T>] = arms;
                    let arm: &alg::PatternArm<St, T> = &arms[i];
                    w.open()?;
                    write_pattern(&arm.pattern, w)?;
                    write_term(arm.body.inner().repr(), w)?;
                    w.close();
                    i += 1;
                }
                w.close();
                w.close();
                Ok(())
            }
        }
    }

    /// Print an annotation.
    ///
    /// `:pattern` and `:no-pattern` hold terms, which is why this is a member of the same cycle as
    /// [`write_term`] rather than a function it calls: a call between members is a step of the one driver,
    /// so annotations nested to any depth cost no native frames.
    pub(super) fn write_attribute<St, So, T>(a: &alg::Attribute<St, T>, w: &mut WorkSpace) -> Res
    where
        St: StrQuote<String> + SymbolQuote<String>,
        So: Contains<T: Repr<T = alg::Sort<St, So>>>,
        T: Print + Contains<T: Repr<T = alg::Term<St, So, T>>>,
    {
        match a {
            alg::Attribute::Keyword(kw) => w.leaf(kw.to_string()),
            alg::Attribute::Constant(kw, c) => {
                w.leaf(kw.to_string())?;
                write_constant(c, w)
            }
            alg::Attribute::Symbol(kw, s) => {
                w.leaf(kw.to_string())?;
                w.leaf(s.sym_quote())
            }
            alg::Attribute::Named(s) => {
                w.leaf(Keyword::Named.to_string())?;
                w.leaf(s.sym_quote())
            }
            alg::Attribute::Pattern(ts) => {
                w.leaf(Keyword::Pattern.to_string())?;
                w.open()?;
                let mut i = 0usize;
                while i < ts.len() {
                    write_term(ts[i].inner().repr(), w)?;
                    i += 1;
                }
                w.close();
                Ok(())
            }
            #[cfg(feature = "no-pattern")]
            alg::Attribute::NoPattern(t) => {
                w.leaf(Keyword::NoPattern.to_string())?;
                write_term(t.inner().repr(), w)
            }
        }
    }
}

impl<St> Print for alg::Constant<St>
where
    St: StrQuote<String>,
{
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        write_constant(self, w)
    }
}

impl<St> Print for alg::Index<St>
where
    St: SymbolQuote<String>,
{
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        write_index(self, w)
    }
}

impl<St> Print for alg::Identifier<St>
where
    St: SymbolQuote<String>,
{
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        write_identifier(self, w)
    }
}

impl<St> Print for alg::Pattern<St>
where
    St: SymbolQuote<String>,
{
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        write_pattern(self, w)
    }
}

impl<St> Print for alg::SigIndex<St>
where
    St: SymbolQuote<String>,
{
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        write_sig_index(self, w)
    }
}

impl Print for alg::BvLenExpr {
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        write_bv_len(self, w)
    }
}

impl<St, So> Print for alg::QualifiedIdentifier<St, So>
where
    St: SymbolQuote<String>,
    So: Print,
{
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        match &self.1 {
            None => write_identifier(&self.0, w),
            Some(s) => w.group(|w| {
                w.leaf(Token::As.to_string())?;
                write_identifier(&self.0, w)?;
                s.write_doc(w)
            }),
        }
    }
}

impl<St, T> Print for alg::VarBinding<St, T>
where
    St: SymbolQuote<String>,
    T: Print,
{
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        w.group(|w| {
            w.leaf(self.0.sym_quote())?;
            self.2.write_doc(w)
        })
    }
}

impl<St, T> Print for alg::PatternArm<St, T>
where
    St: SymbolQuote<String>,
    T: Print,
{
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        w.group(|w| {
            write_pattern(&self.pattern, w)?;
            self.body.write_doc(w)
        })
    }
}

impl<St, So, T> Print for alg::Attribute<St, T>
where
    St: StrQuote<String> + SymbolQuote<String>,
    So: Contains<T: Repr<T = alg::Sort<St, So>>>,
    T: Print + Contains<T: Repr<T = alg::Term<St, So, T>>>,
{
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        write_attribute::<St, So, T>(self, w)
    }
}

impl<So> Print for alg::BvInSort<So>
where
    So: Print,
{
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        match self {
            alg::BvInSort::BitVec(n) => w.group(|w| {
                w.leaf(Token::Underscore.to_string())?;
                w.leaf(BITVEC)?;
                w.leaf(format!("x{n}"))
            }),
            alg::BvInSort::Sort(s) => s.write_doc(w),
        }
    }
}

impl<So> Print for alg::BvOutSort<So>
where
    So: Print,
{
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        match self {
            alg::BvOutSort::BitVec(e) => w.group(|w| {
                w.leaf(Token::Underscore.to_string())?;
                w.leaf(BITVEC)?;
                write_bv_len(e, w)
            }),
            alg::BvOutSort::Sort(s) => s.write_doc(w),
        }
    }
}

impl<St, So> Print for alg::Sig<St, So>
where
    St: SymbolQuote<String>,
    So: Print,
{
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        match self {
            alg::Sig::ParFunc(idx, pars, inps, o) => {
                // the arrow, or just the output sort when the function takes nothing
                let arrow = |w: &mut WorkSpace| {
                    if inps.is_empty() {
                        o.write_doc(w)
                    } else {
                        w.group(|w| {
                            w.leaf(IMPLIES)?;
                            for i in inps {
                                i.write_doc(w)?;
                            }
                            o.write_doc(w)
                        })
                    }
                };
                // the sort parameters wrap it, and the indices wrap that
                let parametrised = |w: &mut WorkSpace| {
                    if pars.is_empty() {
                        arrow(w)
                    } else {
                        w.group(|w| {
                            w.leaf(Token::Par.to_string())?;
                            w.group(|w| {
                                for p in pars {
                                    w.leaf(p.sym_quote())?;
                                }
                                Ok(())
                            })?;
                            arrow(w)
                        })
                    }
                };
                if idx.is_empty() {
                    parametrised(w)
                } else {
                    w.group(|w| {
                        w.leaf(INDICES)?;
                        for i in idx {
                            write_sig_index(i, w)?;
                        }
                        parametrised(w)
                    })
                }
            }
            alg::Sig::VarLenFunc(inp, n, out) => w.group(|w| {
                w.leaf(IMPLIES)?;
                inp.write_doc(w)?;
                w.leaf(at_least(*n))?;
                inp.write_doc(w)?;
                out.write_doc(w)
            }),
            alg::Sig::BvFunc(n, _, _, inps, o) => {
                let arrow = |w: &mut WorkSpace| {
                    if inps.is_empty() {
                        o.write_doc(w)
                    } else {
                        w.group(|w| {
                            w.leaf(IMPLIES)?;
                            for i in inps {
                                i.write_doc(w)?;
                            }
                            o.write_doc(w)
                        })
                    }
                };
                if *n == 0 {
                    arrow(w)
                } else {
                    w.group(|w| {
                        w.leaf(INDICES)?;
                        for _ in 0..*n {
                            w.leaf(reserved(Token::RWNumeral))?;
                        }
                        arrow(w)
                    })
                }
            }
            alg::Sig::BvVarLenFunc(_, inp, n, o) => w.group(|w| {
                w.leaf(IMPLIES)?;
                inp.write_doc(w)?;
                w.leaf(at_least(*n))?;
                inp.write_doc(w)?;
                o.write_doc(w)
            }),
            alg::Sig::BvConcat => {
                w.leaf("(=> (_ BitVec l1) ... (_ BitVec ln) (_ BitVec (+ l1 ... ln)))")
            }
            alg::Sig::Rejected => w.leaf("REJECTED"),
        }
    }
}

impl<St, So> Print for alg::ConstructorDec<St, So>
where
    St: SymbolQuote<String>,
    So: Print,
{
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        w.group(|w| {
            w.leaf(self.ctor.sym_quote())?;
            for a in &self.args {
                a.write_doc(w)?;
            }
            Ok(())
        })
    }
}

impl<St, So> Print for alg::DatatypeDec<St, So>
where
    St: SymbolQuote<String>,
    So: Print,
{
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        let constructors = |w: &mut WorkSpace| {
            w.group(|w| {
                for c in &self.constructors {
                    c.write_doc(w)?;
                }
                Ok(())
            })
        };
        if self.params.is_empty() {
            constructors(w)
        } else {
            // the parameters wrap the constructors, i.e. `(par (a) ((c a)))`
            w.group(|w| {
                w.leaf(Token::Par.to_string())?;
                w.group(|w| {
                    for p in &self.params {
                        w.leaf(p.sym_quote())?;
                    }
                    Ok(())
                })?;
                constructors(w)
            })
        }
    }
}

impl<St, So, T> Print for alg::FunctionDef<St, So, T>
where
    St: SymbolQuote<String>,
    So: Print,
    T: Print,
{
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        w.leaf(self.name.sym_quote())?;
        w.group(|w| {
            for v in &self.vars {
                v.write_doc(w)?;
            }
            Ok(())
        })?;
        self.out_sort.write_doc(w)?;
        self.body.write_doc(w)
    }
}

impl<St, So, T> Print for alg::Command<St, So, T>
where
    St: Clone + StrQuote<String> + SymbolQuote<String>,
    So: Print + Contains<T: Repr<T = alg::Sort<St, So>>>,
    T: Print + Contains<T: Repr<T = alg::Term<St, So, T>>>,
{
    fn write_doc(&self, w: &mut WorkSpace) -> Res {
        write_command(self, w)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::allocator::ObjectAllocatorExt;
    use crate::ast::Arena;
    use crate::traits::Repr;
    use crate::untyped::UntypedAst;

    /// Parse a term, i.e. take the untyped instantiation of the grammar.
    fn parse(s: &str) -> crate::untyped::Term {
        UntypedAst.parse_term_str(s).expect("parse")
    }

    /// Every syntactic form, printed back as it came in.
    #[test]
    fn round_trips_every_form() {
        for s in [
            "x",
            "(and x (or y z))",
            "(not (= a b))",
            "(distinct a b c)",
            "(=> p q r)",
            "(ite c t e)",
            "(xor p q)",
            "(f a b)",
            "((_ extract 3 0) x)",
            "(let ((a 1) (b 2)) (+ a b))",
            "(forall ((x Int) (y Int)) (> x y))",
            "(exists ((x (Array Int Int))) (= x x))",
            "(! (> x 0) :named p)",
            "(! (forall ((x Int)) (p x)) :pattern ((p x)))",
            "(match l ((nil 0) ((cons h t) h)))",
            "(as const (Array Int Int))",
        ] {
            assert_eq!(parse(s).to_string(), s, "printing {s}");
        }
    }

    /// The document is a tree whose shape is the term's, which the text alone would not show.
    #[test]
    fn document_is_a_tree() {
        let t = parse("(and x (or y z))");
        let mut w = WorkSpace::new(&PrintConfig::UNLIMITED);
        let cut = write_term(t.repr(), &mut w).is_err();
        assert_eq!(
            Tree::Node(w.finish(cut)),
            Tree::Node(vec![Tree::Node(vec![
                Tree::Leaf("and".to_string()),
                Tree::Leaf("x".to_string()),
                Tree::Node(vec![
                    Tree::Leaf("or".to_string()),
                    Tree::Leaf("y".to_string()),
                    Tree::Leaf("z".to_string()),
                ]),
            ])])
        );
    }

    #[test]
    fn a_spent_budget_cuts_the_document_short() {
        let t = parse("(and (or a b) (or c d) (or e f))");
        // the budget ran out inside the first group, so that is where the marker sits
        assert_eq!(
            t.repr().print(&PrintConfig::limited(12)),
            "(and (or a ...))"
        );
        // the same term, printed whole
        assert_eq!(t.to_string(), "(and (or a b) (or c d) (or e f))");
    }

    #[test]
    fn an_unspent_budget_prints_everything() {
        assert_eq!(
            parse("(and x y)").repr().print(&PrintConfig::limited(1024)),
            "(and x y)"
        );
    }

    /// A budget of zero still yields a tree, and says that it is not the whole term.
    #[test]
    fn a_budget_of_zero_yields_a_marker() {
        assert_eq!(
            parse("(and x y)").repr().print(&PrintConfig::limited(0)),
            "(...)"
        );
    }

    /// Sorts go through the same infrastructure, on the typed instantiation.
    #[test]
    fn sorts_print_through_the_same_infra() {
        let mut arena = Arena::default();
        let int = arena.int_sort();
        let arr = arena.array_sort(int.clone(), int);
        assert_eq!(arr.to_string(), "(Array Int Int)");
        assert_eq!(arr.repr().print(&PrintConfig::limited(4)), "(Array ...)");
    }
}

#[cfg(test)]
mod stack_safety {
    use super::*;
    use crate::allocator::{ObjectAllocatorExt, TermAllocator};
    use crate::ast::{Arena, Sort, Term};
    use crate::traits::Repr;

    const DEEP: usize = 100_000;
    const SMALL_STACK: usize = 256 * 1024;

    /// `(not (not (… x)))`, nested `depth` deep.
    fn deep_not(arena: &mut Arena, depth: usize) -> Term {
        let bs = arena.bool_sort();
        let mut t = arena.simple_sorted_symbol("x", bs);
        for _ in 0..depth {
            t = arena.not(t);
        }
        t
    }

    /// `(Array Int (Array Int (… Int)))`, nested `depth` deep.
    fn deep_array(arena: &mut Arena, depth: usize) -> Sort {
        let mut s = arena.int_sort();
        for _ in 0..depth {
            let idx = arena.int_sort();
            s = arena.array_sort(idx, s);
        }
        s
    }

    /// Run `f` where a per-level native frame cannot fit, and hand back what it produced.
    fn on_small_stack<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
        std::thread::Builder::new()
            .stack_size(SMALL_STACK)
            .spawn(f)
            .expect("spawn")
            .join()
            .expect("printing overflowed the stack")
    }

    /// The term is leaked in each of these, since dropping one this deep still recurses.
    #[test]
    fn printing_a_deep_term_is_flat() {
        let printed = on_small_stack(|| {
            let mut arena = Arena::default();
            let t = deep_not(&mut arena, DEEP);
            let printed = t.to_string();
            std::mem::forget((t, arena));
            printed
        });
        assert_eq!(
            printed,
            format!("{}x{}", "(not ".repeat(DEEP), ")".repeat(DEEP))
        );
    }

    /// The same, for a sort.
    #[test]
    fn printing_a_deep_sort_is_flat() {
        let printed = on_small_stack(|| {
            let mut arena = Arena::default();
            let s = deep_array(&mut arena, DEEP);
            let printed = s.to_string();
            std::mem::forget((s, arena));
            printed
        });
        assert_eq!(
            printed,
            format!("{}Int{}", "(Array Int ".repeat(DEEP), ")".repeat(DEEP))
        );
    }

    /// `(! x :pattern ((! x :pattern (…))))`, i.e. nesting that goes through an annotation.
    ///
    /// This is the path that only stays flat if a term and its annotations share one driver, since
    /// each level is a call from one member of the cycle into the other.
    #[test]
    fn printing_deep_annotations_is_flat() {
        let printed = on_small_stack(|| {
            let mut arena = Arena::default();
            let bs = arena.bool_sort();
            let x = arena.simple_sorted_symbol("x", bs);
            let mut t = x.clone();
            for _ in 0..DEEP {
                t = arena.annotated(x.clone(), vec![alg::Attribute::Pattern(vec![t])]);
            }
            let printed = t.to_string();
            std::mem::forget((t, x, arena));
            printed
        });
        assert_eq!(
            printed,
            format!("{}x{}", "(! x :pattern (".repeat(DEEP), "))".repeat(DEEP))
        );
    }

    /// A budget bounds the work, so a deep term under a small cap costs a small document.
    #[test]
    fn a_budget_bounds_the_work() {
        let printed = on_small_stack(|| {
            let mut arena = Arena::default();
            let t = deep_not(&mut arena, DEEP);
            let printed = t.repr().print(&PrintConfig::limited(40));
            std::mem::forget((t, arena));
            printed
        });
        // seven levels fit in the budget; the other 99 993 are never visited
        assert_eq!(
            printed,
            format!("{}{ELLIPSIS}{}", "(not ".repeat(7), ")".repeat(7))
        );
    }

    /// Dropping a deep document is iterative, i.e. the `Drop` impl earns its keep.
    ///
    /// There is nothing to compare: a native teardown aborts the process rather than returning.
    #[test]
    fn dropping_a_deep_document_is_flat() {
        on_small_stack(|| {
            let mut arena = Arena::default();
            let t = deep_not(&mut arena, DEEP);
            let mut w = WorkSpace::new(&PrintConfig::UNLIMITED);
            let cut = write_term(t.repr(), &mut w).is_err();
            drop(w.finish(cut));
            std::mem::forget((t, arena));
        });
    }
}
