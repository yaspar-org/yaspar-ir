# stack_safe regression

Does every function `#[stack_safe]` rewrites still compute what its plain recursion computes, and
what does the rewrite cost?

The macro keeps, beside every function it rewrites, a copy as written: `<name>_orig`. That copy
recurses on the native stack and calls the other `_orig` copies of its scope. The harness runs the
rewritten function (`stacksafe`) and its `_orig` copy (`native`) in one process, on one input, in
one context, and compares their results as values. It also times both sides.

This needs a yaspar-macros that emits the copies (0.1.4 or later). By default the harness uses
the version `Cargo.toml` resolves; see `MACROS_REPO` below to try a local checkout instead.

## Commands

From this directory:

```sh
./run.sh check      # what CI runs: coverage, then equivalence at full sizes, then a summary table
./run.sh coverage   # every covered function (every `_orig`) is entered by some case
./run.sh verify     # both sides return equal results on every case, on every run
./run.sh bench      # criterion timings of both sides (~1 h)
./run.sh compare    # results/summary.md and results/summary.csv from the last bench
./run.sh status     # progress of a running verify/bench, from any shell
```

There is no separate setup step. Each command re-exports yaspar-ir whenever any of these changed
since the last run:

- your working tree, uncommitted edits included;
- the macros under test;
- these scripts.

Options, all set through the environment:

| variable | effect |
|---|---|
| `MACROS_REPO=path` (`MACROS_REV=rev`, default `HEAD`) | the yaspar-macros checkout to build against (default empty: the version `Cargo.toml` resolves) |
| `SSBENCH_FILTER=regex`, `SSBENCH_SKIP=regex` | select or skip cases by id `target/shape/size` |
| `SSBENCH_DEPTHS`, `_HEIGHTS`, `_WIDTHS`, `_LEVELS` | sizes (comma-separated) |
| `CVC5=0` | leave out the cvc5 cases (they are included whenever `$CVC5_DIR` exists) |
| `RESULTS=dir` | write somewhere other than `results/` |
| `CRITERION_ARGS="…"` | extra criterion flags for `bench` |

`coverage` also needs `cargo-llvm-cov` (`cargo install cargo-llvm-cov`, with
`rustup component add llvm-tools-preview`).

## How it is built

`setup.sh` exports your yaspar-ir with `git archive`; uncommitted changes go through
`git stash create`, which touches no ref and no file. `scripts/inject_shims.py` then appends an
`__ssbench` module to each file with covered functions, and generates one harness crate.

The appended modules are needed because Rust privacy leaves the harness no other way in. Most
covered functions, and therefore their `_orig` copies, are private to their module, and several
take crate-private types (`CNFEnv`, `AEqCtx`, `PrintSpace`, …). Only code inside that module can
call them. `ast::ctx` is itself private, hence the extra hop `ast::__ssbench_checked` /
`ast::__ssbench_dt`.

Each entry point is written once and compiled twice:

- in `__ssbench::stacksafe`, the covered names are the rewritten functions;
- in `__ssbench::native`, each is aliased to its `_orig` (`use f_orig as f`);
- `Context::scan_named` is a method, which a `use` can't alias, so its native side calls
  `scan_named_orig` directly.

Where yaspar-ir has a public entry point, `stacksafe` calls that public API instead:

- `aeq`, `gsubst_with_names`, `maybe_sort`, `topo_let_intro`, `type_check`, `eval`;
- printing (`to_string()`);
- the cvc5 conversions.

So a native shim that drifts from the wrapper it mirrors makes the two sides differ, and `verify`
reports it.

## What is checked

**`coverage`** runs the native side of every case once, under `cargo llvm-cov`. It fails unless
every `_orig` function in yaspar-ir ran. The list of `_orig` functions comes from the compiler's
coverage map, so it matches the macro's own idea of what it rewrote.

**`verify`** runs each case's sides alternately. Each side repeats for up to 30 ms or 50 runs, and
every result is compared with the first stacksafe result:

- `==` for most results: both sides allocate into one hash-consed context, so equal terms are the
  same term;
- `==` or else alpha-equivalence for results that bind fresh variables (let-introduction, a
  translated quantifier);
- section by section for `find_sections`;
- translated back and compared in yaspar-ir for the forward sort translation, because each side
  declares its sorts into a solver of its own.

Any disagreement fails the run:

- `DIFFERENT`: the two sides disagree on the first run;
- `UNSTABLE`: a later run of either side disagrees with the first.

**`check`** writes a summary table to stdout, to `results/check.md`, and in CI (macOS) to the job
summary. For each target/shape it shows whether the results agreed at every size, and the
fastest run of each side at the largest size.

### What the native side is

An `_orig` copy's recursion is entirely native: calls within its `#[stack_safe]` item go to the
other `_orig` copies. A call out of the item, to a separately annotated function or through a
trait, reaches that function's rewrite. None of these calls are recursive, so each function's own
recursion is still compared in its own cases. Today there are three such calls:

- `write_term` → `write_sort`;
- `translate_term_from_cvc5` → `conv_csort`;
- `nnf_of` / `wrap_level` → `get_sort` → `term_maybe_sort`.

Coverage can't see these calls: rustc doesn't instrument code generated by a macro expansion,
which is what the rewritten functions are.

## Cases

Each case is `target/shape/size`. `harness/src/cases.rs` and `harness/src/cvc5_cases.rs` list
them.

The shapes (`harness/src/inputs.rs`):

- **chains**, 10 … 100 000 deep:
  - single-child, and/or;
  - `ite` rewritten into a fresh temporary (`data_in_frame`);
  - two calls per node behind `?`;
  - tail recursion;
  - term↔attribute and term↔definition mutual recursion;
  - binders (`forall`, `let`, `match`);
  - indexed operators, and sorts;
- **balanced** trees, height 4 … 16;
- **wide** nodes, 10 … 10 000 children;
- **shared_levels**, 10 … 1000: nested shared sub-terms, one let-introduction level each.

Everything runs on a thread with an 8 GiB stack (`SSBENCH_STACK_MB`), so native recursion can be
timed at depth instead of overflowing.

## Layout

```
config.sh, setup.sh, run.sh
scripts/        shims, coverage check, verify check, summary table, bench tables
harness/        the harness crate's sources (runs/harness compiles them)
variants/ runs/ results/   generated (git-ignored)
```

The cvc5 cases link cvc5 statically from `$CVC5_DIR`, which defaults to `target/cvc5-built`. CI
builds it with `.github/actions/setup-cvc5`.
