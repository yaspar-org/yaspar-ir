// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! SMT-LIB regression test driver.
//!
//! Reads `tests/resources/result.json` (a list of `{"include": "<logic>"}` entries),
//! then for each logic reads `tests/resources/<logic>/result.json` (a list of test
//! cases), and runs them one at a time in a fixed, sorted order.
//!
//! Each case is printed before it runs, so the run is reproducible and a failing — or
//! hanging — case can be pinpointed from the log: the last `RUNNING` line without a matching
//! result is the culprit. (Progress is printed from a spawned worker thread, which bypasses
//! libtest's per-test output capture and so streams live even when a case never returns.)
//!
//! This test only runs in release mode with the `regression` feature enabled:
//! ```sh
//! cargo test --release --features regression --test regression
//! ```

#![cfg(all(feature = "regression", not(debug_assertions)))]

use serde::Deserialize;
use std::fs;
use std::io::Write;
use std::panic;
use std::path::{Path, PathBuf};
use std::time::Instant;
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

    // Fixed order: sort by case name so runs are reproducible and the log is easy to scan.
    tests.sort_by(|a, b| a.0.cmp(&b.0));

    // Use a 64 MB stack so deeply nested files trigger a catchable panic instead of an
    // uncatchable SIGABRT. Running on this spawned thread also means the progress printed
    // below escapes libtest's per-test output capture and shows live — so a case that hangs
    // leaves its `RUNNING` line as the last thing in the log.
    const STACK_SIZE: usize = 64 * 1024 * 1024;

    let handle = std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(move || {
            let total = tests.len();
            let mut failures = Vec::new();

            for (i, (name, path, steps)) in tests.iter().enumerate() {
                // Print before running and flush, so a hang leaves this line visible.
                eprint!("[{:>4}/{total}] RUNNING {name} ... ", i + 1);
                std::io::stderr().flush().ok();

                let start = Instant::now();
                let result = panic::catch_unwind(panic::AssertUnwindSafe(|| run_test(path, steps)));
                let ms = start.elapsed().as_millis();

                match result {
                    Ok(Ok(())) => eprintln!("ok ({ms} ms)"),
                    Ok(Err(e)) => {
                        eprintln!("FAIL ({ms} ms): {e}");
                        failures.push(format!("{name}: {e}"));
                    }
                    Err(payload) => {
                        let msg = panic_message(&*payload);
                        eprintln!("PANIC ({ms} ms): {msg}");
                        failures.push(format!("{name}: panic: {msg}"));
                    }
                }
            }
            (total, failures)
        })
        .expect("failed to spawn regression worker thread");

    let (total, failures) = handle.join().expect("regression worker thread panicked");
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
