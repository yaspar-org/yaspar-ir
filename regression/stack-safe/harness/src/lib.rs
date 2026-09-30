// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! The regression harness: every function `#[stack_safe]` covers in yaspar-ir, run both as
//! rewritten (`stacksafe`) and as the `_orig` copy the macro keeps of it (`native`), in one build,
//! on one input, in one context (see `setup.sh` and `scripts/inject_shims.py`).
//!
//! The binary's mode is chosen by `SSBENCH_MODE`:
//!
//! * unset / `bench` — criterion timings of both sides; the usual `cargo bench` flags apply;
//! * `verify`        — run both sides of every case, repeatedly, and compare their results as
//!   values; print `id, verdict, stacksafe s, native s, runs` as TSV;
//! * `run`           — run one side (`SSBENCH_SIDE`, default `native`) of every case once, for the
//!   coverage run;
//! * `list`          — print every case id, building nothing.
//!
//! Every mode runs on a thread with a very large stack (`SSBENCH_STACK_MB`, default 8192): the
//! point is to *time* the native recursions at depth, not to watch them overflow.

pub mod cases;
#[cfg(feature = "cvc5")]
pub mod cvc5_cases;
pub mod inputs;
pub mod registry;

pub use registry::Registry;

/// The entry point of the bench binary.
pub fn main() {
    let stack_mb: usize = std::env::var("SSBENCH_STACK_MB")
        .ok()
        .map(|s| s.parse().expect("SSBENCH_STACK_MB"))
        .unwrap_or(8192);
    let worker = std::thread::Builder::new()
        .name("ssbench".into())
        .stack_size(stack_mb << 20)
        .spawn(|| {
            let mut reg = Registry::from_env();
            cases::register(&mut reg);
            #[cfg(feature = "cvc5")]
            cvc5_cases::register(&mut reg);
            reg.finish();
        })
        .expect("spawn the benchmark thread");
    if worker.join().is_err() {
        std::process::exit(101);
    }
}
