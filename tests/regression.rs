// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! SMT-LIB regression test driver.
//!
//! Reads `tests/resources/result.json` (a list of `{"include": "<logic>"}` entries),
//! then for each logic reads `tests/resources/<logic>/result.json` (a list of test
//! cases), and runs them in parallel across available CPU cores.
//!
//! # Tracing which case is responsible
//!
//! Cases are dispatched in a fixed order (sorted by name) off a shared cursor, and each one
//! prints twice: `START` when it begins and `DONE` when it returns. So a case that fails names
//! itself, and a case that *hangs* is the one whose `START` line has no `DONE` line with the
//! same index — which is what the previous version could not tell you, since it printed nothing
//! per case and a hung run gets killed before any summary.
//!
//! Progress goes to stderr as one `eprintln!` per line, which holds the stderr lock for the whole
//! line, so concurrent workers cannot interleave mid-line.
//!
//! `--nocapture` is REQUIRED for that progress to be visible. Spawning a thread does not escape
//! libtest's output capture -- `std::thread` propagates the capture sink to child threads -- so
//! without it every progress line sits in a buffer that is flushed only when the test function
//! returns, and is lost outright if the run is cancelled or killed. The CI workflow passes it.
//!
//! This test only runs in release mode with the `regression` feature enabled:
//! ```sh
//! cargo test --release --features regression --test regression -- --nocapture
//! ```

#![cfg(all(feature = "regression", not(debug_assertions)))]

use serde::Deserialize;
use std::fs;
use std::panic;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;
use yaspar_ir::ast::fv::FreeLocalVars;
use yaspar_ir::ast::{
    ACommand, CommandAllocator, Context, GlobalSubst, LetElim, Repr, Term, Typecheck,
};
use yaspar_ir::untyped::UntypedAst;

/// An entry in the root `result.json`.
#[derive(Deserialize)]
struct RootEntry {
    include: String,
}

/// A single test case in a logic's `result.json`.
///
/// Unknown fields are ignored, so a case may also carry a `"comment"` explaining why a step is
/// disabled for it — see the two `gsubst` exclusions in `QF_UFLRA/result.json`.
#[derive(Deserialize, Clone)]
struct TestCase {
    path: String,
    steps: Vec<String>,
}

/// Collect all test cases from the root result.json.
fn collect_tests(resources: &Path) -> Vec<(String, PathBuf, Vec<String>)> {
    let root_json = resources.join("result.json");
    let content = match fs::read_to_string(&root_json) {
        Ok(c) => c,
        Err(_) => return vec![],
    };
    let entries: Vec<RootEntry> = match serde_json::from_str(&content) {
        Ok(e) => e,
        Err(_) => return vec![],
    };

    let mut tests = Vec::new();
    for entry in &entries {
        let logic_dir = resources.join(&entry.include);
        let logic_json = logic_dir.join("result.json");
        let content = match fs::read_to_string(&logic_json) {
            Ok(c) => c,
            Err(_) => continue,
        };
        let cases: Vec<TestCase> = match serde_json::from_str(&content) {
            Ok(c) => c,
            Err(_) => continue,
        };
        for case in cases {
            let full_path = logic_dir.join(&case.path);
            tests.push((
                format!("{}::{}", entry.include, case.path),
                full_path,
                case.steps,
            ));
        }
    }
    tests
}

/// Execute the steps for a single test case. Returns an error message on failure.
fn run_test(path: &Path, steps: &[String]) -> Result<(), String> {
    let content =
        fs::read_to_string(path).map_err(|e| format!("failed to read {}: {e}", path.display()))?;

    let commands = UntypedAst
        .parse_script_str(&content)
        .map_err(|e| format!("parse error: {e}"))?;

    let mut context = Context::new();
    let mut typed = None;

    for step in steps {
        match step.as_str() {
            "typecheck" => {
                let t = commands
                    .type_check(&mut context)
                    .map_err(|e| format!("typecheck error: {e}"))?;
                typed = Some(t);
            }
            "letelim" => {
                let t = typed.ok_or("letelim requires a preceding typecheck step")?;
                let mut eliminated = Vec::with_capacity(t.len());
                for c in t {
                    if let ACommand::Assert(term) = c.repr() {
                        let r = term.let_elim(&mut context);
                        // Every local variable in a well-formed assertion is bound, and
                        // let-elimination deletes the `let` binders. So a let-bound variable it
                        // failed to replace would be left dangling — visible right here as a
                        // free local variable.
                        let free = r.free_loc_vars();
                        if !free.is_empty() {
                            let mut names: Vec<_> =
                                free.iter().map(|(n, id)| format!("{n}#{id}")).collect();
                            names.sort();
                            return Err(format!(
                                "let-elimination left free local variable(s): {}",
                                names.join(", ")
                            ));
                        }
                        eliminated.push(context.assert(r));
                    } else {
                        eliminated.push(c);
                    }
                }
                typed = Some(eliminated);
            }
            // Expand every global definition (`define-fun` and friends) in each assertion.
            //
            // Enabled only for the cases that actually carry definitions, since on a file with
            // none this is a full traversal for no coverage. See the `steps` in each logic's
            // `result.json`.
            //
            // KNOWN GAP — `gsubst` overflows the stack on two QF_UFLRA cases, so they run
            // `typecheck` + `letelim` only:
            //
            // * `cpachecker-induction-svcomp14/cpachecker-induction.cs_fib_true-unreach-call.i.smt2`
            //   (1,805,110 definitions, 90 MB)
            // * `cpachecker-induction-svcomp14/cpachecker-induction.Problem08_60_false-unreach-call.c.smt2`
            //   (1,696,948 definitions, 82 MB)
            "gsubst" => {
                let t = typed.ok_or("gsubst requires a preceding typecheck step")?;
                // Expand every assertion in ONE batched call, not one call per assertion.
                //
                // `gsubst_all` resolves the set of defined symbols by scanning the whole symbol
                // table, so calling it per assertion is quadratic in script size. The two 93 MB
                // labyrinth cases are the worst shape possible for that: 1,324,671 assertions
                // over a 419,215-entry symbol table holding exactly 2 definitions, so each of
                // those 1.3M calls spent ~3.3 ms rebuilding a 2-element set — measured at over
                // an hour per file, versus 0.8 s batched. Batching also shares one memo cache across
                // assertions, which is most of the 60x on the Certora QF_UFLIA cases.
                let terms: Vec<Term> = t
                    .iter()
                    .filter_map(|c| match c.repr() {
                        ACommand::Assert(term) => Some(term.clone()),
                        _ => None,
                    })
                    .collect();
                let mut substituted = terms.as_slice().gsubst_all(&mut context).into_iter();
                let mut expanded = Vec::with_capacity(t.len());
                for c in t {
                    if matches!(c.repr(), ACommand::Assert(_)) {
                        let r = substituted
                            .next()
                            .ok_or("gsubst returned fewer terms than assertions")?;
                        expanded.push(context.assert(r));
                    } else {
                        expanded.push(c);
                    }
                }
                typed = Some(expanded);
            }
            other => {
                return Err(format!("unknown step: {other}"));
            }
        }
    }
    Ok(())
}

/// Describe a caught panic payload as a string.
fn panic_message(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        s.to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "unknown panic".to_string()
    }
}

#[test]
fn smtlib_regression() {
    let resources = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/resources");
    let mut tests = collect_tests(&resources);

    if tests.is_empty() {
        eprintln!(
            "No regression tests found. Run tests/resources/setup.sh to download benchmarks."
        );
        return;
    }

    // Fixed order: sort by case name so the dispatch order is reproducible across runs.
    tests.sort_by(|a, b| a.0.cmp(&b.0));

    let total = tests.len();
    let tests = Arc::new(tests);
    // Shared cursor rather than contiguous chunks: per-case cost ranges from 0 ms to ~80 s, so
    // handing out the next case on demand both keeps dispatch in order and balances the load.
    let cursor = Arc::new(AtomicUsize::new(0));
    let failures = Arc::new(Mutex::new(Vec::new()));

    let num_threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);

    // Use 64 MB stacks so deeply nested files trigger a catchable panic
    // instead of an uncatchable SIGABRT.
    const STACK_SIZE: usize = 64 * 1024 * 1024;

    let handles: Vec<_> = (0..num_threads)
        .map(|_| {
            let tests = Arc::clone(&tests);
            let cursor = Arc::clone(&cursor);
            let failures = Arc::clone(&failures);
            std::thread::Builder::new()
                .stack_size(STACK_SIZE)
                .spawn(move || {
                    loop {
                        let i = cursor.fetch_add(1, Ordering::Relaxed);
                        let Some((name, path, steps)) = tests.get(i) else {
                            break;
                        };
                        let n = i + 1;

                        eprintln!("[{n:>4}/{total}] START {name}");

                        let start = Instant::now();
                        let result =
                            panic::catch_unwind(panic::AssertUnwindSafe(|| run_test(path, steps)));
                        let ms = start.elapsed().as_millis();

                        match result {
                            Ok(Ok(())) => eprintln!("[{n:>4}/{total}] DONE  {name} ok ({ms} ms)"),
                            Ok(Err(e)) => {
                                eprintln!("[{n:>4}/{total}] DONE  {name} FAIL ({ms} ms): {e}");
                                failures
                                    .lock()
                                    .expect("failure list poisoned")
                                    .push((i, format!("{name}: {e}")));
                            }
                            Err(payload) => {
                                let msg = panic_message(&*payload);
                                eprintln!("[{n:>4}/{total}] DONE  {name} PANIC ({ms} ms): {msg}");
                                failures
                                    .lock()
                                    .expect("failure list poisoned")
                                    .push((i, format!("{name}: panic: {msg}")));
                            }
                        }
                    }
                })
                .expect("failed to spawn regression worker thread")
        })
        .collect();

    for h in handles {
        h.join().expect("regression worker thread panicked");
    }

    let mut failures = Arc::into_inner(failures)
        .expect("all workers joined")
        .into_inner()
        .expect("failure list poisoned");
    // Report in dispatch order, not the order the workers happened to finish in.
    failures.sort_by_key(|(i, _)| *i);
    let failures: Vec<String> = failures.into_iter().map(|(_, msg)| msg).collect();

    let passed = total - failures.len();
    eprintln!(
        "\nSMT-LIB regression: {passed} passed, {} failed, {total} total",
        failures.len()
    );

    if !failures.is_empty() {
        eprintln!("\nFailures:");
        for msg in &failures {
            eprintln!("  FAIL {msg}");
        }
        panic!("{} regression test(s) failed", failures.len());
    }
}
