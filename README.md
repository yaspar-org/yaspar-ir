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
relieved from the responsibility.

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
the module `ast::ctx::checked`, and traits `CheckedApi` and `ScopedSortApi` for the full list of APIs.

### Checked APIs in detail

The checked APIs are organized around two traits and a set of builder context types. Together, they
form a scoped, type-safe interface for constructing well-formed SMTLib objects.

#### The `TC<T>` monad

All checked APIs return `TC<T>`, which is an alias for `Result<T, String>`. When a well-formedness
invariant is violated (e.g. a symbol is not in scope, a sort mismatch occurs, or an argument count
is wrong), the API returns an `Err` with a descriptive message. This means callers can use `?` to
propagate errors ergonomically.

#### The `CheckedApi` trait — building terms

`CheckedApi` is implemented by `Context` and by all builder context types (see below). It provides
the following categories of functions:

**Symbols and identifiers:**

| Method                               | Description                                                                                              |
|--------------------------------------|----------------------------------------------------------------------------------------------------------|
| `typed_symbol(name)`                 | Look up a declared/defined symbol by name. Returns `Err` if not in scope or ambiguous (e.g. overloaded). |
| `typed_symbol_with_sort(name, sort)` | Look up a symbol and disambiguate by sort. Useful for polymorphic constructors like `nil`.               |
| `typed_identifier(qid)`              | Look up a fully qualified identifier.                                                                    |

**Function application:**

| Method                            | Description                                                                 |
|-----------------------------------|-----------------------------------------------------------------------------|
| `typed_app(qid, args)`            | Apply a qualified identifier to arguments. Checks arity and argument sorts. |
| `typed_simp_app(name, args)`      | Convenience wrapper: apply a function by name string.                       |
| `typed_app_with_kind(kind, args)` | Apply a builtin `IdentifierKind` (e.g. indexed operators).                  |

**Literals:**

| Method              | Description                                                         |
|---------------------|---------------------------------------------------------------------|
| `numeral(n)`        | Build a numeral literal from a `UBig`.                              |
| `integer(i)`        | Build an integer literal from an `IBig` (wraps negation if needed). |
| `typed_constant(c)` | Build a typed constant from a `Constant` value.                     |

**Logical connectives (all arguments must be `Bool`):**

| Method                           | Description                                                                |
|----------------------------------|----------------------------------------------------------------------------|
| `typed_eq(a, b)`                 | Equality `(= a b)`. Both arguments must have the same sort.                |
| `typed_distinct(ts)`             | `(distinct ...)`. At least two arguments required.                         |
| `typed_and(ts)`                  | `(and ...)`. At least one argument.                                        |
| `typed_or(ts)`                   | `(or ...)`. At least one argument.                                         |
| `typed_xor(ts)`                  | `(xor ...)`. At least two arguments.                                       |
| `typed_not(t)`                   | `(not t)`.                                                                 |
| `typed_implies(premises, concl)` | `(=> p1 p2 ... concl)`.                                                    |
| `typed_ite(cond, then, else)`    | `(ite c t e)`. Condition must be `Bool`; branches must have the same sort. |

**Builder contexts (scoped sub-environments):**

| Method                                   | Returns                 | Purpose                                                          |
|------------------------------------------|-------------------------|------------------------------------------------------------------|
| `build_quantifier()`                     | `TC<QuantifierContext>` | Enter a scope for building `forall`/`exists`.                    |
| `build_quantifier_with_domain(bindings)` | `TC<QuantifierContext>` | Shorthand: enter a quantifier scope with pre-declared variables. |
| `build_let(bindings)`                    | `TC<LetContext>`        | Enter a scope for building `let` bindings.                       |
| `build_matching(scrutinee)`              | `TC<MatchContext>`      | Enter a scope for building `match` expressions.                  |

#### The `ScopedSortApi` trait — building sorts

`ScopedSortApi` is automatically implemented for any type that implements `CheckedApi`. It provides
well-formedness-checked sort construction:

| Method                    | Description                                                              |
|---------------------------|--------------------------------------------------------------------------|
| `wf_sort(name)`           | Look up a sort by name (e.g. `"Int"`, `"Bool"`, a user-defined sort).    |
| `wf_sort_n(name, params)` | Parameterized sort (e.g. `wf_sort_n("List", [int])` for `(List Int)`).   |
| `wf_sort_id(id, params)`  | Sort from an `Identifier` and parameters.                                |
| `wf_bv_sort(len)`         | Bitvector sort `(_ BitVec len)`. Validates length > 0 and within bounds. |

These return `Err` when the sort doesn't exist in the current logic, has the wrong number of
parameters, or is otherwise invalid.

#### Builder context types

Builder contexts are scoped environments that extend the current context with local bindings. They
implement `CheckedApi` themselves, so all term-building functions are available inside them. The key
pattern is: create a builder, build terms within it, then finalize.

**`QuantifierContext`** — for `forall` and `exists`:

```rust
let mut context = Context::new();
context.ensure_logic();

let int = context.int_sort();
// Option 1: extend incrementally
let mut q_ctx = context.build_quantifier() ?;
q_ctx.extend("x", int.clone()) ?.extend("y", int) ?;

// Option 2: provide domain upfront (equivalent)
let mut q_ctx = context.build_quantifier_with_domain([("x", int.clone()), ("y", int)]) ?;

// Build terms using the local variables
let body = q_ctx.typed_simp_app(">", [
q_ctx.typed_symbol("x") ?,
q_ctx.typed_symbol("y") ?,
]) ?;

// Finalize — consumes the context
let forall_term = q_ctx.typed_forall(body) ?;  // or .typed_exists(body)?
```

The body must be a `Bool`-sorted term. Duplicate variable names are rejected.

**`LetContext`** — for `let` bindings:

```rust
// Bindings are provided at creation time (they are well-formed in the parent scope)
let bound_term = context.typed_simp_app("+", [a.clone(), b.clone()]) ?;
let mut l_ctx = context.build_let([("sum", bound_term)]) ?;

// "sum" is now available as a local variable
let body = l_ctx.typed_simp_app("*", [
l_ctx.typed_symbol("sum") ?,
l_ctx.typed_symbol("sum") ?,
]) ?;

// Finalize
let let_term = l_ctx.typed_let(body);
```

Note that `typed_let` does not return `TC` — it always succeeds because the bindings were already
validated at context creation.

**`MatchContext` and `ArmContext`** — for `match` expressions:

```rust
// Assume List datatype is declared and l1 : (List Int)
let mut m_ctx = context.build_matching(l1) ?;

// Build the nil arm (nullary constructor)
let nil_arm = m_ctx.build_arm_nullary("nil") ?;
nil_arm.typed_arm(some_body) ?;

// Build the cons arm with named variables
let mut cons_arm = m_ctx.build_arm("cons", [Some("h"), Some("t")]) ?;
// "h" and "t" are now in scope within cons_arm
let h = cons_arm.typed_symbol("h") ?;
let t = cons_arm.typed_symbol("t") ?;
let body = /* ... build body using h and t ... */;
cons_arm.typed_arm(body) ?;

// Finalize — all constructors must be covered (or a wildcard must be present)
let match_term = m_ctx.typed_matching() ?;
```

The match context tracks constructor coverage. `typed_matching()` returns `Err` if not all
constructors are covered. Use `build_arm_wildcard(var)` or `build_arm_catchall()` for wildcard
arms. All arm bodies must have the same sort.

**`FunctionContext`** — for `define-fun`:

```rust
let int = context.int_sort();
let mut f_ctx = context.build_fun_out_sort(
"double", [("x", int.clone())], int
) ?;
let x = f_ctx.typed_symbol("x") ?;
let body = f_ctx.typed_simp_app("+", [x.clone(), x]) ?;
let cmd = f_ctx.typed_define_fun(body) ?;
// "double" is now in the global context
```

Use `build_fun` (without output sort) to let the sort be inferred from the body.

**`RecFunsContext` and `EachRecFunContext`** — for `define-fun-rec` / `define-funs-rec`:

```rust
let int = context.int_sort();
let list_int = context.wf_sort_n("List", [int.clone()]) ?;
let mut ctx = context.build_rec_funs([
RecFunc::new("length", [("l", list_int.clone())], int.clone()),
]) ?;
let mut f_ctx = ctx.build_function("length") ?;
// The function "length" is already in scope (for recursive calls)
let body = /* ... */;
f_ctx.typed_function(body) ?;
let cmd = ctx.typed_define_funs_rec() ?;
```

All declared functions must be given a body before calling `typed_define_funs_rec()`.

**`DatatypeContext` and `DtDeclContext`** — for `declare-datatype(s)`:

```rust
// Simple enum
let cmd = context.typed_enum("Color", ["red", "green", "blue"]) ?;

// Polymorphic datatype
let mut d_ctx = context.build_datatypes([("List", ["X"])]) ?;
let mut c_ctx = d_ctx.build_datatype("List") ?;
c_ctx.build_datatype_constructor_nullary("nil") ?;
let xvar = c_ctx.wf_sort("X") ?;  // sort parameter is in scope
let list_x = c_ctx.wf_sort_n("List", [xvar.clone()]) ?;
c_ctx.build_datatype_constructor("cons", [("car", xvar), ("cdr", list_x)]) ?;
c_ctx.typed_datatype() ?;
let cmd = d_ctx.typed_declare_datatypes() ?;
```

Datatype contexts validate non-emptiness, constructor uniqueness, and selector name uniqueness.
If the context is dropped without calling `typed_declare_datatypes()`, no changes are made to the
global context (the operation is transactional).

**`DefSortContext`** — for `define-sort`:

```rust
let int = context.int_sort();
let s_ctx = context.build_sort_alias("MyInt", []) ?;
let cmd = s_ctx.typed_define_sort(int) ?;
// "MyInt" is now an alias for Int
```

For parameterized sort aliases, the sort parameters are available via `wf_sort` inside the context.

**Top-level command helpers on `Context`:**

| Method                                        | Description                                                                     |
|-----------------------------------------------|---------------------------------------------------------------------------------|
| `typed_assert(t)`                             | Build `(assert t)`. Validates `t` is `Bool` and processes `:named` annotations. |
| `typed_define_const(name, body)`              | Build `(define-const name sort body)` with inferred sort.                       |
| `typed_define_const_sorted(name, sort, body)` | Same, but validates the body matches the declared sort.                         |
| `typed_set_option(opt)`                       | Build `(set-option ...)` with keyword-specific validation.                      |
| `typed_check_sat_assuming(assumptions)`       | Build `(check-sat-assuming ...)`. All assumptions must be `Bool`.               |

#### Context nesting

Builder contexts can be nested. For example, a `QuantifierContext` can create a `LetContext`, which
can create another `QuantifierContext`, and so on. Each nested context sees all bindings from its
ancestors:

```rust
let mut q_ctx = context.build_quantifier_with_domain([("x", int)]) ?;
let inc_x = q_ctx.typed_simp_app("+", [q_ctx.typed_symbol("x") ?, one]) ?;
let mut l_ctx = q_ctx.build_let([("y", inc_x)]) ?;
// "y" and "x" are both in scope here
let body = l_ctx.typed_simp_app("*", [
l_ctx.typed_symbol("x") ?,
l_ctx.typed_symbol("y") ?,
]) ?;
let let_term = l_ctx.typed_let(body);
let forall = q_ctx.typed_forall(let_term) ?;
```

### Analyzing hashconsed objects

Typed ASTs in this crate are hashconsed to optimize memory and run time efficiency. It is still possible to pattern
match on terms by calling `.repr()`. For example, the following function computes the depth of a given term:

```rust
fn depth(t: &Term) -> usize {
    // invoke `.repr()` to obtain the internal representation
    match t.repr() {
        ATerm::Constant(_, _) | ATerm::Global(_, _) | ATerm::Local(_) => 1,
        ATerm::Exists(_, t) | ATerm::Forall(_, t) | ATerm::Annotated(t, _) | ATerm::Not(t) => {
            1 + depth(t)
        }
        ATerm::Matching(t, arms) => {
            1 + arms.iter()
                .map(|a| &a.body)
                .chain([t])
                .map(depth)
                .max()
                .unwrap()
        }
        ATerm::Eq(a, b) => {
            let a = depth(a);
            let b = depth(b);
            1 + a.max(b)
        }
        ATerm::App(_, ts, _) | ATerm::Distinct(ts) | ATerm::And(ts) | ATerm::Or(ts) => {
            1 + ts.iter().map(depth).max().unwrap()
        }
        ATerm::Let(ts, t) | ATerm::Implies(ts, t) => 1 + ts.iter().chain([t]).map(depth).max().unwrap(),
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
4. A set of checked APIs for building typed ASTs. This functionality is exposed by the `CheckedApi` and `ScopedSortApi`
   traits, and the builder context types in `ast::ctx`. See the [Checked APIs in detail](#checked-apis-in-detail)
   section for a comprehensive guide.
5. Let-elimination: see `ast::LetElim`.
6. Computing free variables of a given term: see `ast::FreeLocalVars`.
7. A fresh variable allocator, which returns a fresh symbol that has not been used prior to the point of allocation: see
   `FreshVar`.
8. A compact infrastructure for let-introduction based on topological sorting: see `ast::TopoLetIntro`. This
   functionality
   introduces let-bindings to terms, so that they can be compactly printed with let-bindings inserted for sub-terms
   appearing multiple times.
9. Global and local substitutions; see `ast::Substitute` and `ast::GlobalSubst`.
10. NNF and CNF conversion: see `ast::CNFConversion` . This functionality requires the feature `cnf`.
11. Implicant computation: see `ast::FindImplicant`. This functionality requires the feature `implicant-generation`.
12. Translation to cvc5: see the `cvc5` module and the `ConvertToCvc5` trait. This functionality requires the feature
    `cvc5`. It translates typed `Sort`s, `Term`s, and `Command`s to their cvc5-rs counterparts, with caching and
    support for quantifier `:pattern` annotations.

### Translation to cvc5

The `cvc5` module exposes the `ConvertToCvc5<Env, A>` trait, which provides a uniform `.to_cvc5(env, ctx)` method for
translating sorts, terms, and commands. Two environment types are used:

- `Cvc5Env` — wraps a `TermManager` and caches. Used for translating `Sort`s and `Term`s.
- `Cvc5EnvSolver` — wraps a `Cvc5Env` and a `Solver`. Used for translating `Command`s.

```rust
use cvc5_rs::{Solver, TermManager};
use yaspar_ir::ast::{Context, Typecheck};
use yaspar_ir::cvc5::{ConvertToCvc5, Cvc5Env, Cvc5EnvSolver};
use yaspar_ir::untyped::UntypedAst;

fn main() {
    let mut ctx = Context::new();
    let cmds = UntypedAst
        .parse_script_str(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (> x 0))
             (check-sat)",
        )
        .unwrap()
        .type_check(&mut ctx)
        .unwrap();

    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    let mut env = Cvc5Env::new(&tm);

    // translate commands (which internally translate sorts and terms)
    let mut es = Cvc5EnvSolver::new(&mut env, &mut solver);
    for cmd in &cmds {
        cmd.to_cvc5(&mut es, &mut ctx).unwrap();
    }

    // sorts and terms can also be translated individually
    let int = ctx.int_sort();
    let cvc5_int = int.to_cvc5(&mut env, &mut ctx).unwrap();

    let term = UntypedAst.parse_term_str("(+ x 1)").unwrap().type_check(&mut ctx).unwrap();
    let cvc5_term = term.to_cvc5(&mut env, &mut ctx).unwrap();
}
```

## SMTLib compliance

This crate is completely SMTLib-2.7-compliant. Namely, it follows the SMTLib spec and fully supports specified
features (with exceptions below), including quantifiers and datatypes. Extension theories supported by z3 or cvc5 are
usually not considered.

The following features are intensionally avoided, but we welcome contributors to extend them:

1. floating points,
2. higher order logic, and
3. prenex polymorphism in user-defined sorts and functions.

### Datatypes

This crate fully supports features of datatypes as described by the SMTLib standard. More specifically, it supports:

1. Polymorphic, mutually recursive datatype declarations,
2. Well-formedness and non-emptiness checking, as described by the SMTLib standard,
3. Constructors, selectors and testers generation; In particular, this crate supports both `(_ is X)` tester (standard),
   and `is-X` tester (common extension and de facto standard). `is-X` is defined in terms of `(_ is X)` as a definition.
4. Match expressions.

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
