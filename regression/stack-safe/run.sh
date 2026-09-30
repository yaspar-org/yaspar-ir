#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
# Run the regression. #[stack_safe] keeps, beside every function it rewrites, the function as
# written (`<name>_orig`), so each case runs the rewritten version (`stacksafe`) and the original
# recursion (`native`) in one process, on one input, and compares their results as values. The
# tree is (re-)exported automatically whenever yaspar-ir, the macros under test, or these scripts
# changed since the last export.
#
#   ./run.sh check      what CI runs: coverage, then equivalence at full sizes, then a summary table
#   ./run.sh coverage   every covered function is entered by some case (LLVM coverage)
#   ./run.sh verify     both sides of every case agree, every run (up to 3 runs a side)
#   ./run.sh bench      criterion timings of both sides, one process per case group
#   ./run.sh compare    tabulate the timings: results/summary.md, results/summary.csv
#   ./run.sh status     progress of a running verify/bench, from any shell
#
# Environment knobs (all optional):
#   SSBENCH_FILTER    regex over case ids `target/shape/param`, e.g. '^cnf\.' or '/100000$'
#   SSBENCH_SKIP      regex of case ids to leave out
#   SSBENCH_DEPTHS    chain depths          (default 10,100,1000,10000,100000)
#   SSBENCH_HEIGHTS   balanced-tree heights (default 4,8,12,16)
#   SSBENCH_WIDTHS    fan-outs              (default 10,100,1000,10000)
#   SSBENCH_LEVELS    shared_levels sizes   (default 10,100,1000)
#   SSBENCH_STACK_MB  stack of the benchmark thread (default 8192)
#   CVC5=0            leave out the cvc5 cases (default: included when $CVC5_DIR exists)
#   RESULTS           output directory (default results)
#   CRITERION_ARGS    extra criterion flags, e.g. "--measurement-time 5 --sample-size 50"
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
cd "$HERE"
source ./config.sh

: "${CVC5:=1}"
export CVC5_DIR="${CVC5_DIR:-$CVC5_DIR_DEFAULT}"
FEATURES=()
(( CVC5 )) && FEATURES=(--features cvc5)
# Without a built cvc5 there is nothing to link the cvc5 cases against: leave them out.
if (( CVC5 )) && [[ ! -d $CVC5_DIR ]]; then
    echo "note: no cvc5 at $CVC5_DIR; running without the cvc5 cases (set CVC5_DIR, or CVC5=0)" >&2
    CVC5=0
    FEATURES=()
fi

# Where everything goes; RESULTS=dir keeps a separate run from overwriting results/.
: "${RESULTS:=results}"
mkdir -p "$RESULTS"

# Re-export the trees if yaspar-ir, the macros, or the scripts changed since the last setup.
ensure_setup() {
    if [[ ! -f variants/FINGERPRINT || "$(fingerprint)" != "$(cat variants/FINGERPRINT)" ]]; then
        echo "== sources changed since the last setup; re-exporting"
        ./setup.sh > "$RESULTS/setup.log" 2>&1 \
            || { tail -n 30 "$RESULTS/setup.log" >&2; echo "setup failed ($RESULTS/setup.log)" >&2; exit 1; }
        sed -n '/^yaspar-ir current/,/^generated/p' variants/REVISIONS | sed 's/^/   /'
    fi
}

bench_bin() { # path of the (freshly built) bench binary
    local log="runs/harness/build.log"
    cargo bench --no-run --manifest-path runs/harness/Cargo.toml --bench stack_safe "${FEATURES[@]}" \
        --message-format=json-render-diagnostics 2> "$log" \
        | python3 -c 'import json,sys
exe=[m["executable"] for m in map(json.loads,sys.stdin) if m.get("reason")=="compiler-artifact" and m.get("executable")]
print(exe[-1])' || { tail -n 30 "$log" >&2; echo "build failed ($log)" >&2; exit 1; }
}

# ── progress ──────────────────────────────────────────────────────────────────
PROG=$RESULTS/progress
START=$(date +%s)
progress() { # phase done total current-step [watch-file] [watch-pattern] [matches-per-case]
    local now el eta=""
    now=$(date +%s); el=$(( now - START ))
    if (( $2 > 0 && $2 < $3 )); then eta=" eta≈$(( el * ($3 - $2) / $2 ))s"; fi
    cat > "$PROG.tmp" <<EOP
phase=$1
done=$2
total=$3
step=$4
watch=${5:-}
watch_pattern=${6:-}
watch_per=${7:-1}
started=$(date -r "$START" '+%F %T')
updated=$(date '+%F %T')
elapsed=${el}s$eta
pid=$$
EOP
    mv "$PROG.tmp" "$PROG"
    echo "$(date '+%F %T') [$1 $2/$3] $4" >> "$RESULTS/progress.log"
}

cmd="${1:-}"
case "$cmd" in
coverage | verify | bench) ensure_setup ;;
esac

case "$cmd" in
check)
    # What CI runs: coverage, then equivalence at full sizes (about three minutes). Every
    # SSBENCH_* knob can still be overridden, e.g. SSBENCH_SKIP='/100000$' for a quicker look. The summary table goes to stdout, to
    # $RESULTS/check.md, and to the GitHub job summary when run in Actions.
    status=0
    "$0" coverage 2>&1 | tee "$RESULTS/coverage.out" || status=1
    "$0" verify || status=1
    python3 scripts/summary.py "$RESULTS" > "$RESULTS/check.md"
    cat "$RESULTS/check.md"
    if [[ -n ${GITHUB_STEP_SUMMARY:-} ]]; then cat "$RESULTS/check.md" >> "$GITHUB_STEP_SUMMARY"; fi
    if (( status )); then echo "check FAILED"; else echo "check OK"; fi
    exit $status
    ;;
coverage)
    # the native side of every case, once, at small sizes, under LLVM coverage (always every
    # case: a filtered run would leave functions unentered)
    echo "== coverage run (native side of every case)"
    SSBENCH_FILTER= SSBENCH_SKIP= SSBENCH_MODE=run SSBENCH_SIDE=native SSBENCH_DEPTHS="${SSBENCH_DEPTHS:-10,200}" \
        SSBENCH_HEIGHTS="${SSBENCH_HEIGHTS:-4}" SSBENCH_WIDTHS="${SSBENCH_WIDTHS:-10}" \
        SSBENCH_LEVELS="${SSBENCH_LEVELS:-10}" \
        cargo llvm-cov run --release --manifest-path runs/harness/Cargo.toml --bin ssbench \
        "${FEATURES[@]}" --dep-coverage yaspar-ir --json --output-path "$RESULTS/coverage.json" \
        > "$RESULTS/coverage.log" 2>&1 \
        || { tail -n 30 "$RESULTS/coverage.log" >&2; echo "coverage run failed ($RESULTS/coverage.log)" >&2; exit 1; }
    python3 scripts/check_coverage.py "$RESULTS/coverage.json" $( (( CVC5 )) || echo --no-cvc5 )
    ;;
verify)
    : > "$RESULTS/progress.log"
    bin=$(bench_bin)
    total=$(SSBENCH_MODE=list "$bin" 2>/dev/null | wc -l | tr -d ' ')
    echo "== verify ($total cases, both sides each)"
    progress verify 0 "$total" "running" "$RESULTS/verify.tsv" "."
    SSBENCH_MODE=verify "$bin" > "$RESULTS/verify.tsv" 2> "$RESULTS/verify.err" \
        || echo "   !! verify exited with $? ($RESULTS/verify.err)"
    progress verify "$total" "$total" "finished"
    python3 scripts/compare_verify.py "$RESULTS/verify.tsv" "$total"
    ;;
bench)
    # One process per case group: a native recursion that still overflows the (large) stack kills
    # only its own group, and it is reported rather than taking the whole run down.
    : > "$RESULTS/progress.log"
    progress bench 0 1 "building"
    bin=$(bench_bin)
    ids=$(SSBENCH_MODE=list "$bin" 2>/dev/null | cut -f1)
    groups=$(echo "$ids" | sed 's#/[^/]*$##' | awk '!seen[$0]++')
    all=$(echo "$ids" | wc -l | tr -d ' ')
    n=0
    mkdir -p "$RESULTS/logs"
    : > "$RESULTS/failures.txt"
    for g in $groups; do
        echo "== $g"
        size=$(echo "$ids" | grep -c "^$g/" || true)
        log="$RESULTS/logs/${g//\//__}.log"
        # criterion prints one `time:` line per benchmark, i.e. two per case
        progress bench "$n" "$all" "$g ($size sizes)" "$log" "time:" 2
        set +e
        CRITERION_HOME="$HERE/$RESULTS/criterion" SSBENCH_GROUP="$g" \
            "$bin" --bench --noplot ${CRITERION_ARGS:-} > "$log" 2>&1
        status=$?
        set -e
        grep -E 'time:' "$log" | sed 's/^/   /' || true
        if (( status != 0 )); then
            echo "$g	exit $status" >> "$RESULTS/failures.txt"
            echo "   !! $g exited with $status (see $log)"
        fi
        n=$(( n + size ))
    done
    progress bench "$all" "$all" "finished"
    python3 scripts/compare.py "$RESULTS"
    ;;
compare)
    python3 scripts/compare.py "$RESULTS"
    ;;
status)
    [[ -f $PROG ]] || { echo "no run has started yet (no $PROG)"; exit 0; }
    # shellcheck disable=SC1090
    source <(sed 's/^\([a-z_]*\)=\(.*\)$/P_\1="\2"/' "$PROG")
    alive="finished"
    if [[ $P_step != finished ]]; then
        if kill -0 "$P_pid" 2>/dev/null; then alive="running (pid $P_pid)"; else alive="NOT running (pid $P_pid gone)"; fi
    fi
    live=""
    if [[ -n ${P_watch:-} && -f ${P_watch} && $P_step != finished ]]; then
        c=$(( $(grep -c -- "$P_watch_pattern" "$P_watch" || true) / ${P_watch_per:-1} ))
        live=" +$c in current step"
        P_done=$(( P_done + c ))
    fi
    pct=0; (( P_total > 0 )) && pct=$(( 100 * P_done / P_total ))
    echo "$P_phase: $alive"
    echo "  progress : $P_done/$P_total cases ($pct%)$live"
    echo "  step     : $P_step"
    echo "  elapsed  : $P_elapsed (started $P_started, updated $P_updated)"
    if [[ -s $RESULTS/failures.txt ]]; then echo "  failures:"; sed 's/^/    /' "$RESULTS/failures.txt"; fi
    echo "  last steps:"
    tail -n 5 "$RESULTS/progress.log" | sed 's/^/    /'
    ;;
*)
    sed -n '2,28p' "$0"
    exit 2
    ;;
esac
