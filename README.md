# Yaspar-IR

This crate provides a few representations of SMT scripts and other functionalities.

## Introduction

### A typical use of the crate

We could use this crate to parse and analyze SMTLib scripts. This can be achieved in the following workflow:

```rust
fn main() {
    let script_string: String = read_script();
    // now we parse the string and hopefully we obtain a vector of untyped commands.
    // untyped ASTs in general maintain location information for error reporting, but they could be semantically mal-formed.
    let commands: Vec<u::Command> = UntypedAst.parse_script_str(&script_string).unwrap();
    // then we create a context to operate on. for most use cases, it doesn't make sense to hold more than one top-level context.
    let mut context = Context::new();
    // we invoke type-checking, after which we know the commands are well-formed and obtain a vector of typed commands.
    // typed ASTs returned by this crate maintain type invariant, so we can assume well-formedness of the terms, etc., and
    // operations on them shouldn't need to perform any type invariant checking.
    // it is possible for crate users to build their own typed ASTs directly. it is users' responsibility to maintain the
    // invariants. for testing purposes, users can invoke `.type_check()` again on these terms to check the invariant compliance.
    let commands: Vec<Command> = commands.type_check(&mut context).unwrap();
    // after type-checking, declarations and definitions are inserted to the context. check functions for contexts for details.

    // ...

    // next, we could, for example, obtain the assertions and analyze them.
    let mut asserted_terms: Vec<Term> = vec![];
    for command in &commands {
        // `command` is a hashconsed representation of a command.
        // we should call `.repr()` to obtain its internal representation, which is an enum.
        if let ACommand::Assert(t) = command.repr() {
            // we store the clone of the asserted term.
            // since `Term`s are also hashconsed, it's cheap to call `.clone()`!
            asserted_terms.push(t.clone());

            asserted_term.pop();
            // alternatively, we can insert a let-eliminated version of `t`, so that we do not have to consider let bindings!
            asserted_term.push(t.let_elim(&mut context));
        }
    }

    // now we have all the asserted terms, we can do whatever we want!
    let state = check_satisfiability(&mut context, asserted_terms);
    if state.is_sat() {
        println!("sat");
    } else if state.is_unsat() {
        println!("unsat");
    } else {
        println!("unknown");
    }
}
```

### Checked v.s. Unchecked Building APIs

In general, we maintain a global top-level context to keep track of SMTLib objects and their validity:

```
let mut context = Context::new();
```

Via `context`, we can build typed SMTLib objects like `Command`s, `Term`s, and `Sort`s programmatically. Expectedly,
these
objects have well-formednes invariants. Users have two choices: either maintain the invariants manually via untyped
APIs,
or use the checked building APIs, which operations in a type-checking `TC<T>` monad.

To illustrate, the following snippet uses only the unchecked APIs to build `(+ x y)`:

```rust
fn test_add_1() {
    let mut context = Context::new();
    // invoke `.ensure_logic()` to make sure a logic is set for the context, which affect type-checking.
    // we could also invoke `.set_ctx_logic("ALL")` (with any standard logic) to set a different logic.
    // type-checking commands could also set the logic if there is a `set-logic` command.
    context.ensure_logic();

    // ... something happened.

    let int_sort = context.int_sort();
    // create terms for global constants x and y
    let x = context.simple_sorted_symbol("x", int_sort.clone());
    let y = context.simple_sorted_symbol("y", int_sort.clone());
    // allocate a symbol for `+`
    let plus = context.allocate_symbol("+");
    // then we create `(+ x y)`
    let add_x_y = context.app(
        QualifiedIdentifier::simple(plus),
        vec![x, y],
        Some(int_sort), // note here that we must specify the return type of the application, and it cannot be `None`!
    );
    assert_eq!(add_x_y.to_string(), "(+ x y)");
}
```

The code above is error-prone for the following reasons:

1. it allocates the `Int` sort, which might not exist in the current logic, e.g. `QF_NRA` includes no `Int`.
2. Either `x` or `y` might not be present in the current context, depending on the setup, as they require declarations.

As a result, the addition itself might not be well-formed. Therefore, this code, even though the assertion will still
succeed, might not maintain the invariants.

However, since these APIs are low-level and thus efficient, advanced users could use them for efficient term building,
provided that they are responsible for maintaining the invariants.

Instead, we could write the following snippet, which relies on checked APIs to maintain the invariants; hence users are
released from the responsibility.

```rust
fn test_add_2() -> TC<()> {
    let mut context = Context::new();
    context.ensure_logic();

    // ... something happened.

    // `.typed_symbol()` ensures that `x` and `y` are in scope. 
    // if not, an `Err` is returned.
    let x = context.typed_symbol("x")?;
    let y = context.typed_symbol("y")?;
    // same works for `.typed_simp_app`, which makes sure `+` is in scope, and it can takes
    // both `x` and `y` as arguments.
    let add_x_y = context.typed_simp_app("+", [x, y])?;
    assert_eq!(add_x_y.to_string(), "(+ x y)");
    Ok(())
}
```

All checked APIs are in the form of `typed_*` for building terms, and `wf_*` for building sorts. See
the module `ast::ctx::checked`, and traits `TypedApi` and `ScopedSortApi` for the full list of APIs.

### Analyzing hashconsed objects

Typed ASTs in this crate are hashconsed to optimize memory and run time efficiency. It is still possible to pattern
match on terms by calling `.repr()`. For example, the following function computes the depth of a given term:

```rust
fn depth(t: &Term) -> usize {
    // invoke `.repr()` to obtain the internal representation
    match t.repr() {
        ATerm::Constant(_, _) | ATerm::Global(_, _) | ATerm::Local(_) => 1,
        ATerm::App(_, ts, _) => ts.iter().map(depth).max().unwrap() + 1,
        ATerm::Let(ts, t) => ts.iter().map(|b| &b.2).chain([t]).map(depth).max().unwrap() + 1,
        ATerm::Exists(_, t) | ATerm::Forall(_, t) | ATerm::Annotated(t, _) | ATerm::Not(t) => {
            1 + depth(t)
        }
        ATerm::Matching(t, arms) => {
            arms.iter()
                .map(|a| &a.body)
                .chain([t])
                .map(depth)
                .max()
                .unwrap()
                + 1
        }
        ATerm::Eq(a, b) => {
            let a = depth(a);
            let b = depth(b);
            1 + a.max(b)
        }
        ATerm::Distinct(ts) | ATerm::And(ts) | ATerm::Or(ts) => {
            1 + ts.iter().map(depth).max().unwrap()
        }
        ATerm::Implies(ts, cl) => ts.iter().chain([cl]).map(depth).max().unwrap(),
        ATerm::Ite(c, t, e) => {
            let c = depth(c);
            let t = depth(t);
            let e = depth(e);
            1 + c.max(t.max(e))
        }
    }
}
```

### More examples

More use of APIs can be found in the `tests/` folder.

## A parametric, algebraic representation of ASTs

For a package that provides functionalities for SMT scripts, sits at the core a parametric, algebraic representation of
ASTs.
This representation is defined by various enums and structs in `raw::alg`. Please consult the doc of the module for more
details.

This representation is flexible and allows two benefits:

1. We can instantiate this representation into different instances. In this package, there are two different instances
   of ASTs:

    1. an untyped representation with location information (`ast::u`), and
    2. a hashcons-ed, typed representation (`ast`).

   The former is a faithful parsing result of a grammatically correct SMT script, which could be potentially
   semantically
   mal-formed. Through type-checking (by calling `.type_check()`, we convert an untyped AST to a typed AST, which is
   more
   compactly stored in memory via a hashconsing arena. If type-checking fails, the location information of the untyped
   representation is used for error reporting.

2. We can achieve very good code reuse. In particular, functions implemented for the algebraic representation
   automatically works for all instantiations. For instance, the printing implementation works automatically for both
   typed and untyped representations. The type-checking algorithm also applies for both untyped (to obtain a typed AST)
   and typed (to re-check an AST constructed by untyped APIs) ASTs.

Use the macro `instantiate_ast!` to instantiate more variants!

## Functionalities provided by the package

Currently, the crate provides the following functionalities:

1. Parsing to an untyped representation: see functions exposed by `ast::u::UntypedAst`. This functionality uses
   `yaspar` under the hood.
2. Typechecking: see `ast::Typecheck`. After invoking `.type_check()`, we are handling the typed representation and can
   assume type invariants of the representation. All typed ASTs are managed by `ast::Context`, which keeps track of the
   current logic, symbols, sorts, and cache. Type-checking commands has the side effect of potentially extending the
   context.
3. A set of unchecked APIs for building typed ASTs. This functionality is achieved using allocator functions exposed by
   `ast::Context`.
4. A set of checked APIs for building typed ASTs. This functionality is exposed by the functions in `ast::ctx::checked`.
5. Let-elimination: see `ast::LetElim`.
6. Computing free variables of a given term: see `ast::FreeLocalVars`.
7. A fresh variable allocator, which returns a fresh symbol that has not been used prior to the point of allocation: see
   `FreshVar`.
8. A compact infrastructure for let-introduction based on topological sorting: see `ast::TopoLetIntro`. This
   functionality
   introduces let-bindings to terms, so that they can be compactly printed with let-bindings inserted for sub-terms
   appearing multiple times.
9. Global and local substitutions; see `ast::Substitute`, `ast::GlobalSubstInplace`, and `ast::GlobalSubstPreproc`.
10. NNF and CNF conversion: see `ast::CNFConversion` . This functionality requires the feature `cnf`.
11. Implicant computation: see `ast::FindImplicant`. This functionality requires the feature `implicant-generation`.

## SMTLib compliance

This package is completely SMTLib-2.7-compliant. Namely, it follows the SMTLib spec and fully supports specified
features (with exceptions below),
including quantifiers and datatypes. Extension theories supported by z3 or cvc5 are usually not considered.

The following features are intensionally avoided, but we welcome contributors to extend them:

1. floating points,
2. higher order logic, and
3. prenex polymorphism in user-defined sorts and functions.

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.