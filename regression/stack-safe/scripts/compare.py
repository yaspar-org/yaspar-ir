#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Tabulate criterion results of both sides.

Reads results/criterion/**/new/{benchmark,estimates}.json (ids `target/shape/param/<side>`), and
writes

  results/summary.csv   every id, both mean times (ns) and their ratio;
  results/summary.md    the same as a table, plus a per-target/shape geometric-mean roll-up.

The ratio is `stacksafe / native`: the cost of the transform on the same code. Below 1 means
`stacksafe` is faster.

Usage: compare.py <results dir>
"""
import csv
import json
import math
import pathlib
import sys



def load(root: pathlib.Path) -> dict[str, dict[str, float]]:
    """Mean time per case id and side, from criterion ids `target/shape/param/<side>`."""
    out: dict[str, dict[str, float]] = {}
    for bj in root.rglob("new/benchmark.json"):
        est = bj.parent / "estimates.json"
        if not est.exists():
            continue
        full_id = json.loads(bj.read_text())["full_id"]
        case, _, side = full_id.rpartition("/")
        out.setdefault(case, {})[side] = json.loads(est.read_text())["mean"]["point_estimate"]
    return out


def ratio(a, b):
    return a / b if a and b else None


def fmt_ns(x):
    if x is None:
        return "—"
    for unit, scale in (("s", 1e9), ("ms", 1e6), ("µs", 1e3)):
        if x >= scale:
            return f"{x / scale:.3g} {unit}"
    return f"{x:.3g} ns"


def fmt_r(x):
    return "—" if x is None else f"{x:.2f}"


def geomean(xs):
    xs = [x for x in xs if x]
    return math.exp(sum(map(math.log, xs)) / len(xs)) if xs else None


def sort_key(i):
    head, _, p = i.rpartition("/")
    return (head, int(p) if p.isdigit() else 0)


def main() -> None:
    results = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else "results")
    data = load(results / "criterion")
    ids = sorted(data, key=sort_key)
    if not ids:
        sys.exit(f"no criterion results under {results}/criterion")
    rows = []
    for i in ids:
        nat, ss = data[i].get("native"), data[i].get("stacksafe")
        rows.append((i, nat, ss, ratio(ss, nat)))

    with open(results / "summary.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["id", "native_ns", "stacksafe_ns", "stacksafe/native"])
        for r in rows:
            w.writerow([r[0]] + ["" if x is None else f"{x:.6g}" for x in r[1:]])

    lines = ["| id | native | stacksafe | ss/native |", "|---|---:|---:|---:|"]
    for i, nat, ss, rn in rows:
        lines.append(f"| {i} | {fmt_ns(nat)} | {fmt_ns(ss)} | {fmt_r(rn)} |")

    groups = {}
    for r in rows:
        groups.setdefault(r[0].rsplit("/", 1)[0], []).append(r)
    roll = ["", "Geometric mean over sizes, per target/shape:", "",
            "| target/shape | ss/native | ss/native at largest size |", "|---|---:|---:|"]
    for g, rs in groups.items():
        roll.append(f"| {g} | {fmt_r(geomean([r[3] for r in rs]))} | {fmt_r(rs[-1][3])} |")
    overall = ["", f"Overall geometric mean: ss/native {fmt_r(geomean([r[3] for r in rows]))} "
               f"({len(rows)} benchmarks)"]
    (results / "summary.md").write_text("\n".join(lines + roll + overall) + "\n")

    f = results / "failures.txt"
    if f.exists() and f.read_text().strip():
        overall.append("failed groups:\n  " + f.read_text().strip().replace("\n", "\n  "))
    print("\n".join(roll + overall))
    print(f"\nwrote {results / 'summary.md'} and {results / 'summary.csv'}")


if __name__ == "__main__":
    main()
