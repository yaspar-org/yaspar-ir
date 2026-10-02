#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Fail unless every case of a `verify` run said `same`.

Each line of the verify TSV is one case: `id, verdict, stacksafe s, native s, hits, runs`. The
verdict comes from comparing the two sides' results as values in one process: `DIFFERENT` when
the first native run disagrees with the first stacksafe run, `UNSTABLE` when a later run of either
side disagrees with the first. A case that is missing crashed the run (see verify.err).

Usage: compare_verify.py <verify tsv> <expected number of cases>
"""
import sys


def main() -> None:
    path, expected = sys.argv[1], int(sys.argv[2])
    rows = [l.split("\t") for l in open(path).read().splitlines() if l.strip()]
    bad = [r for r in rows if r[1] != "same"]
    print(f"{len(rows)} of {expected} cases ran; "
          + (f"{len(bad)} disagree" if bad else "native and stacksafe agree on every one"))
    for r in bad[:40]:
        print(f"  {r[1]}: {r[0]}")
    if len(rows) < expected:
        print(f"  MISSING: {expected - len(rows)} case(s) did not run; the last one started is in verify.err")
    sys.exit(1 if bad or len(rows) < expected else 0)


if __name__ == "__main__":
    main()
