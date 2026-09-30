#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""A markdown summary of a `check`: coverage, then one row per target/shape saying whether native
and stacksafe agreed at every size, with the times at the largest size.

The times come from `verify`: the fastest run of each side, each side repeated for up to 30 ms. They show where the
transform stands at depth; `run.sh bench` gives statistically sound numbers.

Usage: summary.py <results dir>
"""
import math
import pathlib
import sys


def fmt_s(x: float) -> str:
    for unit, scale in (("s", 1), ("ms", 1e-3), ("µs", 1e-6)):
        if x >= scale:
            return f"{x / scale:.3g} {unit}"
    return f"{x / 1e-9:.3g} ns"


def key(i: str):
    head, _, p = i.rpartition("/")
    return (head, int(p) if p.isdigit() else 0)


def main() -> None:
    res = pathlib.Path(sys.argv[1])
    out = ["## stack_safe regression", ""]

    cov = res / "coverage.out"
    if cov.exists():
        lines = cov.read_text().splitlines()
        picked = [l for l in lines if " covered functions, " in l
                  or l.startswith(("coverage OK", "COVERAGE FAILED"))]
        missing = [l.strip() for l in lines if l.startswith("  src/")]
        out += ["**Coverage:** " + " — ".join(picked)
                + (f" (not entered: {', '.join(missing)})" if missing else ""), ""]

    rows = {}
    vt = res / "verify.tsv"
    if vt.exists():
        for line in vt.read_text().splitlines():
            c = line.split("\t")
            if len(c) >= 4:
                rows[c[0]] = (c[1], float(c[2]), float(c[3]))
    bad = sum(1 for v in rows.values() if v[0] != "same")
    out += [f"**Equivalence:** {len(rows)} cases, each run on both sides in one process and "
            "compared as values: "
            + ("native and stacksafe agree on every one" if not bad else f"**{bad} disagree**"), ""]

    groups: dict[str, list[str]] = {}
    for i in sorted(rows, key=key):
        groups.setdefault(i.rsplit("/", 1)[0], []).append(i)
    out += ["| target/shape | sizes | results | largest | native | stacksafe | ss/nat |",
            "|---|---:|:---:|---:|---:|---:|---:|"]
    ratios = []
    for g, ids in groups.items():
        verdicts = {rows[i][0] for i in ids}
        mark = "✅" if verdicts == {"same"} else "❌ " + ",".join(sorted(verdicts - {"same"}))
        _, s, n = rows[ids[-1]]
        r = s / n if n > 0 and s > 0 else None
        if r:
            ratios.append(r)
        out.append(f"| {g} | {len(ids)} | {mark} | {ids[-1].rsplit('/', 1)[1]} "
                   f"| {fmt_s(n)} | {fmt_s(s)} | {'—' if r is None else f'{r:.2f}'} |")
    if ratios:
        gm = math.exp(sum(map(math.log, ratios)) / len(ratios))
        out += ["", f"Geometric mean of ss/nat at the largest size: {gm:.2f} ({len(ratios)} shapes); "
                "fastest run of each side (repeated for up to 30 ms); `run.sh bench` gives benchmarks."]
    print("\n".join(out))


if __name__ == "__main__":
    main()
