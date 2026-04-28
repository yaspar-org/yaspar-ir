// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! SMT-LIB regression test driver.
//!
//! Reads `tests/resources/result.json` (a list of `{"include": "<logic>"}` entries),
//! then for each logic reads `tests/resources/<logic>/result.json` (a list of test
//! cases), and runs them in parallel across available CPU cores.
//!
//! Run `tests/resources/setup.sh` first to download and unpack the benchmarks.
//!
//! This test only runs in release mode with the `regression` feature enabled:
//! ```sh
//! cargo test --release --features regression --test regression
//! ```

#![cfg(all(feature = "regression", not(debug_assertions)))]

use serde::Deserialize;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::panic;
use yaspar_ir::ast::{ACommand, CommandAllocator, Context, LetElim, Repr, Typecheck};
use yaspar_ir::untyped::UntypedAst;

/// An entry in the root `result.json`.
#[derive(Deserialize)]
struct RootEntry {
    include: String,
}

/// A single test case in a logic's `result.json`.
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
                typed = Some(
                    t.into_iter()
                        .map(|c| {
                            if let ACommand::Assert(term) = c.repr() {
                                let r = term.let_elim(&mut context);
                                context.assert(r)
                            } else {
                                c
                            }
                        })
                        .collect(),
                );
            }
            other => {
                return Err(format!("unknown step: {other}"));
            }
        }
    }
    Ok(())
}

#[test]
fn smtlib_regression() {
    let resources = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/resources");
    let tests = collect_tests(&resources);

    if tests.is_empty() {
        eprintln!(
            "No regression tests found. Run tests/resources/setup.sh to download benchmarks."
        );
        return;
    }

    let total = tests.len();
    let passed = Arc::new(AtomicUsize::new(0));
    let failed = Arc::new(AtomicUsize::new(0));

    let num_threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);

    // Use 64 MB stacks so deeply nested files trigger a catchable panic
    // instead of an uncatchable SIGABRT.
    const STACK_SIZE: usize = 64 * 1024 * 1024;

    // Partition tests into chunks for parallel execution
    let chunk_size = total.div_ceil(num_threads);
    let chunks: Vec<Vec<_>> = tests
        .chunks(chunk_size)
        .map(|c| c.to_vec())
        .collect();

    let handles: Vec<_> = chunks
        .into_iter()
        .map(|chunk| {
            let passed = Arc::clone(&passed);
            let failed = Arc::clone(&failed);
            std::thread::Builder::new()
                .stack_size(STACK_SIZE)
                .spawn(move || {
                    let mut local_failures = Vec::new();
                    for (name, path, steps) in &chunk {
                        let result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
                            run_test(path, steps)
                        }));
                        match result {
                            Ok(Ok(())) => {
                                passed.fetch_add(1, Ordering::Relaxed);
                            }
                            Ok(Err(e)) => {
                                failed.fetch_add(1, Ordering::Relaxed);
                                local_failures.push(format!("FAIL {name}: {e}"));
                            }
                            Err(panic_info) => {
                                failed.fetch_add(1, Ordering::Relaxed);
                                let msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                                    s.to_string()
                                } else if let Some(s) = panic_info.downcast_ref::<String>() {
                                    s.clone()
                                } else {
                                    "unknown panic".to_string()
                                };
                                local_failures.push(format!("FAIL {name}: panic: {msg}"));
                            }
                        }
                    }
                    local_failures
                })
                .expect("failed to spawn thread")
        })
        .collect();

    let mut all_failures = Vec::new();
    for h in handles {
        all_failures.extend(h.join().unwrap());
    }

    let p = passed.load(Ordering::Relaxed);
    let f = failed.load(Ordering::Relaxed);
    eprintln!("\nSMT-LIB regression: {p} passed, {f} failed, {total} total");

    if !all_failures.is_empty() {
        eprintln!("\nFailures:");
        for msg in &all_failures {
            eprintln!("  {msg}");
        }
        panic!("{f} regression test(s) failed");
    }
}
