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
let mut q_ctx = context.build_quantifier()?;
q_ctx.extend("x", int.clone())?.extend("y", int)?;

// Option 2: provide domain upfront (equivalent)
let mut q_ctx = context.build_quantifier_with_domain([("x", int.clone()), ("y", int)])?;

// Build terms using the local variables
let body = q_ctx.typed_simp_app(">", [
q_ctx.typed_symbol("x")?,
q_ctx.typed_symbol("y")?,
])?;

// Finalize — consumes the context
let forall_term = q_ctx.typed_forall(body)?;  // or .typed_exists(body)?
```

The body must be a `Bool`-sorted term. Duplicate variable names are rejected.

**`LetContext`** — for `let` bindings:

```rust
// Bindings are provided at creation time (they are well-formed in the parent scope)
let bound_term = context.typed_simp_app("+", [a.clone(), b.clone()])?;
let mut l_ctx = context.build_let([("sum", bound_term)])?;

// "sum" is now available as a local variable
let body = l_ctx.typed_simp_app("*", [
l_ctx.typed_symbol("sum")?,
l_ctx.typed_symbol("sum")?,
])?;

// Finalize
let let_term = l_ctx.typed_let(body);
```

Note that `typed_let` does not return `TC` — it always succeeds because the bindings were already
validated at context creation.

**`MatchContext` and `ArmContext`** — for `match` expressions:

```rust
// Assume List datatype is declared and l1 : (List Int)
let mut m_ctx = context.build_matching(l1)?;

// Build the nil arm (nullary constructor)
let nil_arm = m_ctx.build_arm_nullary("nil")?;
nil_arm.typed_arm(some_body)?;

// Build the cons arm with named variables
let mut cons_arm = m_ctx.build_arm("cons", [Some("h"), Some("t")])?;
// "h" and "t" are now in scope within cons_arm
let h = cons_arm.typed_symbol("h")?;
let t = cons_arm.typed_symbol("t")?;
let body = /* ... build body using h and t ... */;
cons_arm.typed_arm(body)?;

// Finalize — all constructors must be covered (or a wildcard must be present)
let match_term = m_ctx.typed_matching()?;
```

The match context tracks constructor coverage. `typed_matching()` returns `Err` if not all
constructors are covered. Use `build_arm_wildcard(var)` or `build_arm_catchall()` for wildcard
arms. All arm bodies must have the same sort.

**`FunctionContext`** — for `define-fun`:

```rust
let int = context.int_sort();
let mut f_ctx = context.build_fun_out_sort(
"double", [("x", int.clone())], int
)?;
let x = f_ctx.typed_symbol("x")?;
let body = f_ctx.typed_simp_app("+", [x.clone(), x])?;
let cmd = f_ctx.typed_define_fun(body)?;
// "double" is now in the global context
```

Use `build_fun` (without output sort) to let the sort be inferred from the body.

**`RecFunsContext` and `EachRecFunContext`** — for `define-fun-rec` / `define-funs-rec`:

```rust
let int = context.int_sort();
let list_int = context.wf_sort_n("List", [int.clone()])?;
let mut ctx = context.build_rec_funs([
RecFunc::new("length", [("l", list_int.clone())], int.clone()),
])?;
let mut f_ctx = ctx.build_function("length")?;
// The function "length" is already in scope (for recursive calls)
let body = /* ... */;
f_ctx.typed_function(body)?;
let cmd = ctx.typed_define_funs_rec()?;
```

All declared functions must be given a body before calling `typed_define_funs_rec()`.

**`DatatypeContext` and `DtDeclContext`** — for `declare-datatype(s)`:

```rust
// Simple enum
let cmd = context.typed_enum("Color", ["red", "green", "blue"])?;

// Polymorphic datatype
let mut d_ctx = context.build_datatypes([("List", ["X"])])?;
let mut c_ctx = d_ctx.build_datatype("List")?;
c_ctx.build_datatype_constructor_nullary("nil")?;
let xvar = c_ctx.wf_sort("X")?;  // sort parameter is in scope
let list_x = c_ctx.wf_sort_n("List", [xvar.clone()])?;
c_ctx.build_datatype_constructor("cons", [("car", xvar), ("cdr", list_x)])?;
c_ctx.typed_datatype()?;
let cmd = d_ctx.typed_declare_datatypes()?;
```

Datatype contexts validate non-emptiness, constructor uniqueness, and selector name uniqueness.
If the context is dropped without calling `typed_declare_datatypes()`, no changes are made to the
global context (the operation is transactional).

**`DefSortContext`** — for `define-sort`:

```rust
let int = context.int_sort();
let s_ctx = context.build_sort_alias("MyInt", [])?;
let cmd = s_ctx.typed_define_sort(int)?;
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
let mut q_ctx = context.build_quantifier_with_domain([("x", int)])?;
let inc_x = q_ctx.typed_simp_app("+", [q_ctx.typed_symbol("x")?, one])?;
let mut l_ctx = q_ctx.build_let([("y", inc_x)])?;
// "y" and "x" are both in scope here
let body = l_ctx.typed_simp_app("*", [
l_ctx.typed_symbol("x")?,
l_ctx.typed_symbol("y")?,
])?;
let let_term = l_ctx.typed_let(body);
let forall = q_ctx.typed_forall(let_term)?;
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
        ATerm::App(_, ts, _) | ATerm::Distinct(ts) | ATerm::And(ts) | ATerm::Or(ts) | ATerm::Xor(ts) => {
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

### Stack-safe term recursion with `TermRecursor`

The manual pattern-matching approach above works well for simple analyses, but it uses the call
stack for recursion, which can overflow on deeply nested terms. It also requires the implementor
to handle every `ATerm` variant explicitly.

The `TermRecursor` trait provides a stack-safe, callback-driven alternative. The traversal is
driven by an internal `Vec`-based stack, so it never overflows regardless of term depth.
Implementors define one callback per term variant and receive the already-computed results for
child terms.

Every callback receives a `current: &T` parameter — a reference to the original term node being
recursed on. This gives access to the hashconsed identity, sort information, or other metadata
without reconstructing the term from its parts.

Here is the `depth` example rewritten using `TermRecursor`:

```rust
use yaspar_ir::ast::alg::{
    Attribute, Constant, Local, PatternArm, QualifiedIdentifier, VarBinding,
};
use yaspar_ir::ast::{Bottom, Sort, Str, Term, TermRecursor, TypedTermRecursor};

struct TermDepth;

impl TermRecursor<Str, Sort, Term> for TermDepth {
    type Out = usize;
    type Attr = ();
    type Binding = usize;
    type Pattern = ();
    type Arm = usize;
    type Err = Bottom;

    // Leaves have depth 1
    fn on_constant(&mut self, _: &Term, _: &Constant<Str>, _: &Option<Sort>) -> Result<usize, Bottom> { Ok(1) }
    fn on_global(&mut self, _: &Term, _: &QualifiedIdentifier<Str, Sort>, _: &Option<Sort>) -> Result<usize, Bottom> { Ok(1) }
    fn on_local(&mut self, _: &Term, _: &Local<Str, Sort>) -> Result<usize, Bottom> { Ok(1) }

    // Compound nodes: 1 + max of children
    fn on_app(&mut self, _: &Term, _: &QualifiedIdentifier<Str, Sort>, _: &[Term], _: &Option<Sort>, recs: Vec<usize>) -> Result<usize, Bottom> {
        Ok(1 + recs.into_iter().max().unwrap())
    }
    fn on_eq(&mut self, _: &Term, _: &Term, _: &Term, a: usize, b: usize) -> Result<usize, Bottom> { Ok(1 + a.max(b)) }
    fn on_not(&mut self, _: &Term, _: &Term, r: usize) -> Result<usize, Bottom> { Ok(1 + r) }
    fn on_and(&mut self, _: &Term, _: &[Term], r: Vec<usize>) -> Result<usize, Bottom> { Ok(1 + r.into_iter().max().unwrap()) }
    fn on_or(&mut self, _: &Term, _: &[Term], r: Vec<usize>) -> Result<usize, Bottom> { Ok(1 + r.into_iter().max().unwrap()) }
    fn on_xor(&mut self, _: &Term, _: &[Term], r: Vec<usize>) -> Result<usize, Bottom> { Ok(1 + r.into_iter().max().unwrap()) }
    fn on_distinct(&mut self, _: &Term, _: &[Term], r: Vec<usize>) -> Result<usize, Bottom> { Ok(1 + r.into_iter().max().unwrap()) }
    fn on_implies(&mut self, _: &Term, _: &[Term], _: &Term, ps: Vec<usize>, c: usize) -> Result<usize, Bottom> {
        Ok(1 + ps.into_iter().chain([c]).max().unwrap())
    }
    fn on_ite(&mut self, _: &Term, _: &Term, _: &Term, _: &Term, b: usize, t: usize, e: usize) -> Result<usize, Bottom> {
        Ok(1 + b.max(t.max(e)))
    }

    // Scoped constructs
    fn setup_let_scope(&mut self, _: &Term, _: &[VarBinding<Str, Term>], _: &Term, _: &[usize]) -> Result<(), Bottom> { Ok(()) }
    fn on_let_binding(&mut self, _: &Term, _: &[VarBinding<Str, Term>], _: &Term, _: usize, r: usize) -> Result<usize, Bottom> { Ok(r) }
    fn on_let(&mut self, _: &Term, _: &[VarBinding<Str, Term>], _: &Term, vs: Vec<usize>, body: usize) -> Result<usize, Bottom> {
        Ok(1 + vs.into_iter().chain([body]).max().unwrap())
    }
    fn setup_quantifier_scope(&mut self, _: &Term, _: &[VarBinding<Str, Sort>], _: &Term, _: bool) -> Result<(), Bottom> { Ok(()) }
    fn on_forall(&mut self, _: &Term, _: &[VarBinding<Str, Sort>], _: &Term, r: usize) -> Result<usize, Bottom> { Ok(1 + r) }
    fn on_exists(&mut self, _: &Term, _: &[VarBinding<Str, Sort>], _: &Term, r: usize) -> Result<usize, Bottom> { Ok(1 + r) }
    fn setup_match_case_scope(&mut self, _: &Term, _: &Term, _: &[PatternArm<Str, Term>], _: &usize, _: usize) -> Result<(), Bottom> { Ok(()) }
    fn on_match_arm(&mut self, _: &Term, _: &Term, _: &[PatternArm<Str, Term>], _: usize, r: usize) -> Result<usize, Bottom> { Ok(r) }
    fn on_match(&mut self, _: &Term, _: &Term, _: &[PatternArm<Str, Term>], s: usize, arms: Vec<usize>) -> Result<usize, Bottom> {
        Ok(1 + arms.into_iter().chain([s]).max().unwrap())
    }
    fn on_annotated(&mut self, _: &Term, _: &Term, _: &[Attribute<Str, Term>], r: usize, _: Vec<()>) -> Result<usize, Bottom> { Ok(1 + r) }

    // Attributes
    fn on_attribute_keyword(&mut self, _: &Term, _: &yaspar::ast::Keyword) -> Result<(), Bottom> { Ok(()) }
    fn on_attribute_constant(&mut self, _: &Term, _: &yaspar::ast::Keyword, _: &Constant<Str>) -> Result<(), Bottom> { Ok(()) }
    fn on_attribute_symbol(&mut self, _: &Term, _: &yaspar::ast::Keyword, _: &Str) -> Result<(), Bottom> { Ok(()) }
    fn on_attribute_named(&mut self, _: &Term, _: &Str) -> Result<(), Bottom> { Ok(()) }
    fn on_attribute_pattern(&mut self, _: &Term, _: &[Term], r: Vec<usize>) -> Result<(), Bottom> {
        Ok(())
    }
}

impl TypedTermRecursor for TermDepth {}
```

To use it:

```rust
let depth = TermDepth.recurse_on_term_no_err(&some_term);
```

The `recurse_on_term_no_err` method is available when setting `Err` to `Bottom`. 
It returns the output directly without wrapping in `Result`.

The convenience trait `TypedTermRecursor` is a marker for recursors specialized to the typed AST
(`Str`, `Sort`, `Term`). An analogous `UntypedTermRecursor` exists for untyped ASTs.

### Memoized term recursion with `Memoize`

Because typed terms are hashconsed, structurally identical sub-terms share the same identity. A
plain `TermRecursor` traversal will re-visit such shared sub-terms every time they appear. The
`Memoize` wrapper caches the `Out` result for each term node, so repeated encounters return the
cached value immediately — skipping the entire sub-tree.

Wrap any recursor with `Memoize::new(recursor)` to get automatic caching backed by a `HashMap`:

```rust
use yaspar_ir::ast::{Memoize, TermRecursor};

// assuming TermDepth from the previous section
let mut memo = Memoize::new(TermDepth);
let depth = memo.recurse_on_term(&some_term).unwrap();
```

The cache is stored in the public `cache` field, so it can be reused across multiple traversals.
Pass a pre-populated cache via `Memoize::with_cache` to avoid recomputing results for terms that
were already visited:

```rust
// first traversal populates the cache
let mut memo = Memoize::new(TermDepth);
let _ = memo.recurse_on_term(&term_a).unwrap();

// second traversal reuses the cache — shared sub-terms are not re-visited
let mut memo2 = Memoize::with_cache(TermDepth, &mut memo.cache);
let _ = memo2.recurse_on_term(&term_b).unwrap();
```

This is particularly beneficial for analyses over assertions that share many common sub-terms,
where a non-memoized traversal would perform redundant work proportional to the number of
shared occurrences.

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
10. Stack-free recursors: see `ast::TermRecursor`, `ast::TypedTermRecursor`, `ast::u::UntypedTermRecursor` and `ast::Memoize`.
    This functionality provides a stack-free, visitor-based implementation of a depth first traversal of `Term`s. General
    recursions are still available, but for deeply nested terms, general recursions could hit the stack limit of the
    operating system. Stack-free recursors do not have such risk. Plug-in memoization is also available.  
11. NNF and CNF conversion: see `ast::CNFConversion` . This functionality requires the feature `cnf`.
12. Implicant computation: see `ast::FindImplicant`. This functionality requires the feature `implicant-generation`.
13. Translation to cvc5: see the `cvc5` module and the `ConvertToCvc5` trait. This functionality requires the feature
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

#### `is` is not a permitted symbol

When the theory of datatypes is active, `is` cannot be used as a user-declared symbol (e.g. via `declare-const`,
`declare-fun`, or as a bound variable name). This is because `is` serves as the head symbol of the indexed identifier
`(_ is X)` for datatype constructor testers. Allowing `is` as a regular symbol would create ambiguity between a
user-defined symbol and the built-in tester operator.

This restriction is consistent with how other indexed-identifier head symbols are treated. For example, in the theory
of bitvectors, symbols of the form `bvN` (where `N` is a numeral) are reserved because they denote bitvector literals.
Similarly, symbols like `extract`, `zero_extend`, `sign_extend`, and `rotate_left` are recognized as heads of indexed
bitvector operators (e.g. `(_ extract 7 4)`). In each case, the symbol has special meaning when it appears as the head
of an indexed identifier, and reserving it prevents confusion with user-defined names.

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
