// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for issue #129: deeply nested AST nodes, typed and untyped, must not overflow
//! the native stack when they are deallocated.
//!
//! Each test runs on a thread with a deliberately small (1 MiB) stack, so a recursive teardown
//! aborts the process instead of quietly succeeding on the test harness's larger stack. Note that
//! a stack overflow is *not* a catchable panic: if these regress, the whole test binary dies with
//! `fatal runtime error: stack overflow`.

use dashu::integer::IBig;
use yaspar_ir::ast::{CheckedApi, Context, ObjectAllocatorExt, Typecheck};
use yaspar_ir::untyped::UntypedAst;

const STACK: usize = 1024 * 1024;
const DEPTH: usize = 20_000;

fn on_small_stack(name: &'static str, f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name(name.into())
        .stack_size(STACK)
        .spawn(f)
        .expect("failed to spawn thread")
        .join()
        .expect("test thread panicked")
}

#[test]
fn deep_term_chain_teardown() {
    on_small_stack("deep_term_chain_teardown", || {
        let mut context = Context::new();
        UntypedAst
            .parse_script_str("(set-logic ALL)\n(declare-const x Int)\n")
            .unwrap()
            .type_check(&mut context)
            .unwrap();

        // `mod` is deliberately not overloaded: an overloaded builtin would also exercise the
        // eager error formatting of issue #129's first site, which is a separate concern.
        let one = context.integer(IBig::from(1)).unwrap();
        let mut acc = context.typed_symbol("x").unwrap();
        for _ in 0..DEPTH {
            acc = context
                .typed_simp_app("mod", vec![acc, one.clone()])
                .unwrap();
        }

        // Dropping the handles frees at most one node each: the arena's hashconsing table still
        // holds a payload copy of every node. It is the arena teardown below that used to
        // cascade recursively through the whole chain.
        drop(acc);
        drop(one);
        drop(context);
    })
}

#[test]
fn deep_sort_teardown() {
    on_small_stack("deep_sort_teardown", || {
        let mut context = Context::new();
        let int = context.int_sort();
        let mut acc = context.int_sort();
        for _ in 0..DEPTH {
            acc = context.array_sort(int.clone(), acc);
        }
        drop(acc);
        drop(int);
        drop(context);
    })
}

#[test]
fn deep_untyped_term_drop() {
    on_small_stack("deep_untyped_term_drop", || {
        let mut s = String::from("x");
        for _ in 0..DEPTH {
            s = format!("(mod {s} 1)");
        }
        // The untyped AST has no hashconsing table pinning children, so dropping the root
        // handle alone used to cascade through the entire term.
        let term = UntypedAst.parse_term_str(&s).unwrap();
        drop(term);
    })
}

#[test]
fn deep_untyped_sort_drop() {
    on_small_stack("deep_untyped_sort_drop", || {
        let mut s = String::from("Int");
        for _ in 0..DEPTH {
            s = format!("(Array Int {s})");
        }
        let sort = UntypedAst.parse_sort_str(&s).unwrap();
        drop(sort);
    })
}
