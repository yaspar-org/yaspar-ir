# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
# Sourced by setup.sh and run.sh. Override any of these from the environment.

# The yaspar-ir repository under test: the one this directory lives in.
: "${IR_REPO:=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"

# The yaspar-ir tree under test. `WORKTREE` (the default) includes uncommitted changes to tracked
# files; any commit-ish (e.g. HEAD) exports exactly that commit instead.
: "${IR_CUR_REV:=WORKTREE}"

# The yaspar-macros under test. The harness needs the `<name>_orig` copies #[stack_safe] keeps of
# the functions it rewrites (yaspar-macros 3249514 and later). Empty: the version yaspar-ir's
# Cargo.toml resolves; a path: a checkout to export at $MACROS_REV. Defaults to a sibling checkout
# when there is one.
if [[ -z ${MACROS_REPO+set} && -d "$IR_REPO/../yaspar-macros/.git" ]]; then
    MACROS_REPO="$(cd "$IR_REPO/../yaspar-macros" && pwd)"
fi
: "${MACROS_REPO:=}"
: "${MACROS_REV:=HEAD}"

# A built cvc5, for the cvc5 cases (`run.sh` includes them when this exists, unless CVC5=0).
: "${CVC5_DIR_DEFAULT:=$IR_REPO/target/cvc5-built}"

# What the exported tree was made from: yaspar-ir, the macros, and the scripts that transform
# them. `run.sh` re-runs setup.sh whenever this changes, so a run always measures the code as it
# is now.
ir_tree() {
    local rev=$IR_CUR_REV
    if [[ $rev == WORKTREE ]]; then
        rev=$(git -C "$IR_REPO" stash create)
        [[ -n $rev ]] || rev=HEAD
    fi
    git -C "$IR_REPO" rev-parse "$rev^{tree}"
}
fingerprint() {
    local here
    here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
    echo "ir $(ir_tree)"
    if [[ -n $MACROS_REPO ]]; then
        echo "macros $(git -C "$MACROS_REPO" rev-parse "$MACROS_REV^{tree}")"
    fi
    cat "$here/setup.sh" "$here/scripts/inject_shims.py" | shasum | cut -d' ' -f1
}
