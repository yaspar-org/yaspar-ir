#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Check that the cases reach every function #[stack_safe] covers, from LLVM coverage.

`run.sh coverage` runs the *native* side of every case once, under `cargo llvm-cov`, and exports
yaspar-ir's function-level counts as JSON. The functions under test are read off that export
rather than off the source: every `<name>_orig` in yaspar-ir is a copy #[stack_safe] kept of a
function it rewrote, so the set of `_orig` functions is exactly the set of covered functions.

Fails unless every `_orig` function ran. (Only the `_orig` copies are in the report at all: rustc
does not instrument the code a macro expansion generates, which the rewritten functions are.)

Usage: check_coverage.py <llvm-cov json> [--no-cvc5]
"""
import collections
import json
import re
import sys


class _V0:
    """Enough of the v0 mangling grammar (RFC 2603) to find a symbol's own identifier."""

    def __init__(self, s: str):
        self.s, self.i = s, 0

    def peek(self) -> str:
        return self.s[self.i] if self.i < len(self.s) else ""

    def take(self) -> str:
        c = self.peek()
        self.i += 1
        return c

    def base62(self) -> None:
        while self.take() != "_":
            pass

    def ident(self) -> str:
        if self.peek() == "s":
            self.take()
            self.base62()
        if self.peek() == "u":
            self.take()
        n = re.match(r"\d+", self.s[self.i:]).group(0)
        self.i += len(n)
        if self.peek() == "_":
            self.take()
        out = self.s[self.i:self.i + int(n)]
        self.i += int(n)
        return out

    def path(self) -> str:
        c = self.take()
        if c == "C":
            return self.ident()
        if c == "N":
            self.take()  # namespace
            self.path()
            return self.ident()
        if c in "MX":
            if self.peek() == "s":
                self.take()
                self.base62()
            self.path()
            self.type()
            if c == "X":
                return self.path()
            return ""
        if c == "Y":
            self.type()
            return self.path()
        if c == "I":
            name = self.path()
            while self.peek() != "E":
                self.generic_arg()
            self.take()
            return name
        if c == "B":
            self.base62()
            return ""
        raise ValueError(f"unexpected {c!r} at {self.i} in {self.s}")

    def generic_arg(self) -> None:
        c = self.peek()
        if c == "L":
            self.take()
            self.base62()
        elif c == "K":
            self.take()
            self.const()
        else:
            self.type()

    def const(self) -> None:
        if self.peek() in "pB":
            if self.take() == "B":
                self.base62()
            return
        self.type()
        if self.peek() == "n":
            self.take()
        while self.take() != "_":
            pass

    def type(self) -> None:
        c = self.peek()
        if c.islower():  # a basic type, `u` (the unit type) included
            self.take()
        elif c in "RQ":
            self.take()
            if self.peek() == "L":
                self.take()
                self.base62()
            self.type()
        elif c in "SPO":
            self.take()
            self.type()
        elif c == "A":
            self.take()
            self.type()
            self.const()
        elif c == "T":
            self.take()
            while self.peek() != "E":
                self.type()
            self.take()
        elif c == "B":
            self.take()
            self.base62()
        else:
            self.path()


def function_name(sym: str) -> str:
    """The function's own identifier, from a v0 (`_R...`) or legacy (`_ZN...E`) Rust symbol."""
    if sym.startswith("_R"):
        v = _V0(sym)
        v.i = 2
        while v.peek().isdigit():  # encoding version
            v.take()
        try:
            return v.path()
        except (ValueError, AttributeError):
            return sym
    m = re.match(r"_?_ZN(.*)E$", sym)
    if not m:
        return sym
    rest, parts = m.group(1), []
    while rest and rest[0].isdigit():
        n = re.match(r"\d+", rest).group(0)
        rest = rest[len(n):]
        parts.append(rest[: int(n)])
        rest = rest[int(n):]
    if parts and re.fullmatch(r"h[0-9a-f]{16}", parts[-1]):
        parts.pop()
    return parts[-1] if parts else sym


def load(path: str) -> dict[tuple[str, str], int]:
    """Calls per `(file, function)` of yaspar-ir, summed over instantiations."""
    counts: dict[tuple[str, str], int] = collections.defaultdict(int)
    for f in json.load(open(path))["data"][0]["functions"]:
        files = [x for x in f.get("filenames", []) if "/variants/yaspar-ir/src/" in x]
        if files:
            rel = "src/" + files[0].split("/variants/yaspar-ir/src/", 1)[1]
            counts[(rel, function_name(f["name"]))] += f["count"]
    return counts


def main() -> None:
    no_cvc5 = "--no-cvc5" in sys.argv
    counts = load(sys.argv[1])

    origs = {k: n for k, n in counts.items() if k[1].endswith("_orig")}
    if no_cvc5:
        origs = {k: n for k, n in origs.items() if k[0] != "src/cvc5.rs"}
    missing = sorted(k for k, n in origs.items() if n == 0)

    print(f"{'function (native side)':60} {'calls':>10}")
    for (rel, name), n in sorted(origs.items()):
        print(f"{rel + '::' + name:60} {n:10}")
    print(f"\n{len(origs)} covered functions, {len(origs) - len(missing)} entered"
          + ("; cvc5 functions not checked" if no_cvc5 else ""))
    if missing:
        print("\nCOVERAGE FAILED: no case enters\n  " + "\n  ".join(f"{r}::{n}" for r, n in missing))
        sys.exit(1)
    if not origs:
        sys.exit("COVERAGE FAILED: no `_orig` function in the report (is yaspar-macros new enough?)")
    print("coverage OK: every covered function is entered")


if __name__ == "__main__":
    main()
