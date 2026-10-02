// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Where cases are declared, and what running one means in each mode.
//!
//! A case is `(target, shape)` swept over a list of parameters (a depth, a height, a width), and
//! it has two sides: the rewritten functions, `stacksafe`, and the `_orig` copies #[stack_safe]
//! keeps of them, `native`. Both sides run in
//! this one process, on one input, in one context, so their results are compared as values with
//! the case's own `same` (usually `==`; alpha-equivalence where a result binds fresh variables).
//!
//! A case's id is `target/shape/param`; its criterion ids are `target/shape/param/<side>`. One
//! regex (`SSBENCH_FILTER`) selects the same cases in every mode, and `SSBENCH_SKIP` leaves some
//! out. Inputs are built lazily, so a filtered-out case never pays for building a 100 000-deep input.

use criterion::Criterion;
use regex::Regex;
use std::hint::black_box;
use std::io::Write;
use std::time::{Duration, Instant};

enum Mode {
    Bench(Box<Criterion>),
    Verify,
    List,
    /// Run one side of every case once, for the coverage run: 0 = stacksafe, 1 = native.
    Run(usize),
}

pub struct Registry {
    mode: Mode,
    filter: Option<Regex>,
    skip: Option<Regex>,
    group: Option<String>,
    pub depths: Vec<usize>,
    pub heights: Vec<usize>,
    pub widths: Vec<usize>,
    pub levels: Vec<usize>,
    cases: usize,
    failures: usize,
}

fn list_env(name: &str, default: &[usize]) -> Vec<usize> {
    match std::env::var(name) {
        Ok(s) if !s.trim().is_empty() => s
            .split(',')
            .map(|x| x.trim().replace('_', "").parse().expect(name))
            .collect(),
        _ => default.to_vec(),
    }
}

fn regex_env(name: &str) -> Option<Regex> {
    std::env::var(name)
        .ok()
        .filter(|s| !s.is_empty())
        .map(|s| Regex::new(&s).unwrap_or_else(|e| panic!("{name}: {e}")))
}

/// Up to this many calls share one timer reading when a case needs no per-call setup, so the
/// cost of reading the clock is not charged to a sub-microsecond call.
const BATCH: u64 = 64;

/// In `verify`, each side runs again (alternating with the other) until it has spent
/// `VERIFY_BUDGET` or run `VERIFY_RUNS` times; every output is compared with the first one, and
/// the fastest run of each side is reported.
const VERIFY_RUNS: usize = 50;
const VERIFY_BUDGET: Duration = Duration::from_millis(30);

/// One side of a case: run it `iters` times on the state, and say how long the measured part took,
/// with the last output.
type Side<'a, S, O> = &'a mut dyn FnMut(&mut S, u64) -> (Duration, Option<O>);

impl Registry {
    pub fn from_env() -> Self {
        let mode = match std::env::var("SSBENCH_MODE").as_deref() {
            Ok("verify") => Mode::Verify,
            Ok("list") => Mode::List,
            Ok("run") => Mode::Run(match std::env::var("SSBENCH_SIDE").as_deref() {
                Ok("stacksafe") => 0,
                Ok("native") | Err(_) => 1,
                Ok(other) => panic!("unknown SSBENCH_SIDE {other}"),
            }),
            Ok("bench") | Err(_) => Mode::Bench(Box::new(
                Criterion::default()
                    .warm_up_time(Duration::from_millis(500))
                    .measurement_time(Duration::from_secs(2))
                    .sample_size(20)
                    .configure_from_args(),
            )),
            Ok(other) => panic!("unknown SSBENCH_MODE {other}"),
        };
        Registry {
            mode,
            filter: regex_env("SSBENCH_FILTER"),
            skip: regex_env("SSBENCH_SKIP"),
            // exactly one `target/shape`; set by run.sh to run one group per process
            group: std::env::var("SSBENCH_GROUP").ok().filter(|s| !s.is_empty()),
            // A chain of this many nested nodes: where native recursion is the expensive part.
            depths: list_env("SSBENCH_DEPTHS", &[10, 100, 1_000, 10_000, 100_000]),
            // A complete binary tree of this height: many calls, shallow stack.
            heights: list_env("SSBENCH_HEIGHTS", &[4, 8, 12, 16]),
            // One node with this many children: recursion from inside a loop, depth 2.
            widths: list_env("SSBENCH_WIDTHS", &[10, 100, 1_000, 10_000]),
            // For shapes whose work is quadratic in their nesting (see `inputs::shared_levels`).
            levels: list_env("SSBENCH_LEVELS", &[10, 100, 1_000]),
            cases: 0,
            failures: 0,
        }
    }

    fn selected(&self, id: &str) -> bool {
        self.filter.as_ref().is_none_or(|r| r.is_match(id))
            && !self.skip.as_ref().is_some_and(|r| r.is_match(id))
    }

    /// A case whose calls need no setup of their own: each side is called repeatedly on one state.
    #[allow(clippy::too_many_arguments)]
    pub fn pair<S, O>(
        &mut self,
        target: &'static str,
        shape: &'static str,
        params: &[usize],
        build: impl Fn(usize) -> S,
        mut stacksafe: impl FnMut(&mut S) -> O,
        mut native: impl FnMut(&mut S) -> O,
        same: impl Fn(&O, &O) -> bool,
    ) {
        fn batched<S, O>(f: &mut impl FnMut(&mut S) -> O) -> impl FnMut(&mut S, u64) -> (Duration, Option<O>) + '_ {
            move |s, iters| {
                let mut total = Duration::ZERO;
                let mut outs = Vec::with_capacity(BATCH as usize);
                let mut last = None;
                let mut left = iters;
                while left > 0 {
                    let n = left.min(BATCH);
                    let t0 = Instant::now();
                    for _ in 0..n {
                        outs.push(black_box(f(s)));
                    }
                    total += t0.elapsed();
                    // dropped outside the timed region
                    last = outs.pop();
                    outs.clear();
                    left -= n;
                }
                (total, last)
            }
        }
        self.drive(
            target,
            shape,
            params,
            build,
            [&mut batched(&mut stacksafe), &mut batched(&mut native)],
            &same,
        );
    }

    /// A case whose calls need fresh setup each time (a cache that must start cold, an input a
    /// call consumes). Each side does that setup itself and returns only the time of the part
    /// being measured, alongside its output.
    #[allow(clippy::too_many_arguments)]
    pub fn pair_timed<S, O>(
        &mut self,
        target: &'static str,
        shape: &'static str,
        params: &[usize],
        build: impl Fn(usize) -> S,
        mut stacksafe: impl FnMut(&mut S) -> (Duration, O),
        mut native: impl FnMut(&mut S) -> (Duration, O),
        same: impl Fn(&O, &O) -> bool,
    ) {
        fn repeated<S, O>(f: &mut impl FnMut(&mut S) -> (Duration, O)) -> impl FnMut(&mut S, u64) -> (Duration, Option<O>) + '_ {
            move |s, iters| {
                let mut total = Duration::ZERO;
                let mut last = None;
                for _ in 0..iters {
                    let (d, o) = f(s);
                    total += d;
                    last = Some(black_box(o));
                }
                (total, last)
            }
        }
        self.drive(
            target,
            shape,
            params,
            build,
            [&mut repeated(&mut stacksafe), &mut repeated(&mut native)],
            &same,
        );
    }

    #[allow(clippy::too_many_arguments)]
    fn drive<S, O>(
        &mut self,
        target: &'static str,
        shape: &'static str,
        params: &[usize],
        build: impl Fn(usize) -> S,
        sides: [Side<'_, S, O>; 2],
        same: &dyn Fn(&O, &O) -> bool,
    ) {
        let group_name = format!("{target}/{shape}");
        if self.group.as_ref().is_some_and(|g| *g != group_name) {
            return;
        }
        let params: Vec<usize> = params
            .iter()
            .copied()
            .filter(|p| self.selected(&format!("{group_name}/{p}")))
            .collect();
        if params.is_empty() {
            return;
        }
        self.cases += params.len();
        let [ss, nat] = sides;
        match &mut self.mode {
            Mode::List => {
                for p in params {
                    println!("{group_name}/{p}");
                }
            }
            Mode::Run(side) => {
                for p in params {
                    eprintln!("run {group_name}/{p}");
                    let mut s = build(p);
                    let _ = if *side == 0 { ss(&mut s, 1) } else { nat(&mut s, 1) };
                }
            }
            Mode::Verify => {
                for p in params {
                    let id = format!("{group_name}/{p}");
                    eprintln!("verify {id}");
                    let mut s = build(p);
                    let (d, first) = ss(&mut s, 1);
                    let first = first.expect("one call");
                    let mut best = [d, Duration::MAX];
                    let mut spent = [d, Duration::ZERO];
                    let mut runs = [1usize, 0];
                    let mut verdict = "same";
                    // alternate native, stacksafe, native, ... every output against the first
                    'runs: loop {
                        let mut ran = false;
                        for side in [1, 0] {
                            if runs[side] > 0 && (runs[side] >= VERIFY_RUNS || spent[side] >= VERIFY_BUDGET) {
                                continue;
                            }
                            let (d, o) = if side == 0 { ss(&mut s, 1) } else { nat(&mut s, 1) };
                            let o = o.expect("one call");
                            if !same(&first, &o) {
                                verdict = if side == 1 && runs[1] == 0 { "DIFFERENT" } else { "UNSTABLE" };
                            }
                            best[side] = best[side].min(d);
                            spent[side] += d;
                            runs[side] += 1;
                            ran = true;
                            drop(o);
                            if verdict != "same" {
                                break 'runs;
                            }
                        }
                        if !ran {
                            break;
                        }
                    }
                    if verdict != "same" {
                        self.failures += 1;
                    }
                    println!(
                        "{id}\t{verdict}\t{:.9}\t{:.9}\t{}+{}",
                        best[0].as_secs_f64(),
                        best[1].as_secs_f64(),
                        runs[0],
                        runs[1]
                    );
                    std::io::stdout().flush().ok();
                    drop(first);
                    drop(s);
                }
            }
            Mode::Bench(c) => {
                let mut group = c.benchmark_group(group_name);
                for p in params {
                    let mut state: Option<S> = None;
                    group.bench_function(format!("{p}/stacksafe"), |b| {
                        let s = state.get_or_insert_with(|| build(p));
                        b.iter_custom(|iters| ss(s, iters).0);
                    });
                    group.bench_function(format!("{p}/native"), |b| {
                        let s = state.get_or_insert_with(|| build(p));
                        b.iter_custom(|iters| nat(s, iters).0);
                    });
                    drop(state);
                }
                group.finish();
            }
        }
    }

    pub fn finish(self) {
        if let Mode::Bench(c) = self.mode {
            c.final_summary();
        }
        eprintln!("ssbench: {} case(s) selected, {} failed", self.cases, self.failures);
    }
}
