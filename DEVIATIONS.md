# Deviations from SMT-LIB

This document lists where yaspar-ir knowingly departs from the
[SMT-LIB standard](https://smt-lib.org/language.shtml).

## `:global-declarations` is not supported

The option is accepted by `set-option` (and checked to be a Boolean), but it has no effect:
declarations and definitions always belong to the assertion level they are made in, as if
`:global-declarations` were `false`. Hence,

- `(pop n)` discards all sorts and symbols declared or defined in the popped levels, and
- `(reset-assertions)` discards all of them, including those of the first assertion level.

Scripts that rely on `:global-declarations true` to keep using a declaration after it has been
popped or reset are rejected by the type checker.

## cvc5 backend: `reset` is not supported

cvc5 cannot reset a solver in place, so translating a `(reset)` command with
`Command::to_cvc5` returns an error. To follow a `reset`, call `Cvc5Env::reset_env` and continue
with a fresh `cvc5::Solver`.

`push`, `pop` and `reset-assertions` are supported and follow the semantics above.
