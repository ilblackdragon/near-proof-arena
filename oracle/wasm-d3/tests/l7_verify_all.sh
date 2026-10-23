#!/usr/bin/env bash
# L7's whole differential-verification sweep, as one reproducible command.
#
#   oracle/wasm-d3/tests/l7_verify_all.sh [--quick] [--out DIR] [--python-leg]
#
# Runs, in order, and stops at the first failure:
#   1. harness self-tests                      (python unittest, 28 tests)
#   2. UQ-014 LoadingError reproducer           (3 legs; exits 0 only when the divergence reproduces)
#   2b. UQ-014 wasmtime branch table             (resource LinkError reachable; both legs agree)
#   3. corpus content manifest + drift gate     (18 families, content hashes)
#   4. D1 regression  53,048 cases
#   5. D2 regression  67,384 cases
#   6. D3 regression  33,248 + 49,490 + 15,995 + 16,551 = 115,284 cases
#   7. make pin-check                           (signed-surface source pins)
#
# Every step's exit status is nonzero on disagreement, so this script's exit status is meaningful:
# "a harness that prints ok without comparing" cannot make this pass. See
# docs/evidence/lean-chunk-L7/readiness-assessment.md for what each comparison actually compares.
#
# Requirements: pinned nearcore at /data/illia/nearproof-deps/nearcore and the corpora at
# /data/illia/nearproof-deps/corpora; the Lean binaries built (see below); the nearcore difftest
# harness at /data/illia/nearproof-deps/target-wasm-d3/release/near-wasm-d3-harness.
#
# `--quick` samples each corpus instead of running it whole, for a smoke test only. It is NOT a
# substitute for the full sweep and prints a banner saying so.
#
# `--python-leg` additionally runs the independent Python checker as a third leg in the D3 step, so
# the Lean-vs-Python comparison is reproduced too. It is opt-in because it costs a second full Python
# run per corpus; without it the D3 step compares Lean against nearcore's recorded verdicts only.
set -u -o pipefail

# Resolve the repository root from this script's own location, but fall back to $PWD when the script
# is copied outside the tree for a wiring test. L7_REPO overrides both.
REPO="${L7_REPO:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." 2>/dev/null && pwd)}"
if [ -z "${REPO:-}" ] || [ ! -d "$REPO/spec/lean/v3" ]; then
  REPO="$PWD"
fi
[ -d "$REPO/spec/lean/v3" ] || { echo "FAIL: cannot locate the repository root; set L7_REPO" >&2; exit 2; }
CORPORA="${CORPORA:-/data/illia/nearproof-deps/corpora}"
OUT=""
QUICK=0
PYLEG=0
JOBS="${JOBS:-12}"

while [ $# -gt 0 ]; do
  case "$1" in
    --quick) QUICK=1; shift ;;
    --python-leg) PYLEG=1; shift ;;
    --out) OUT="$2"; shift 2 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done
OUT="${OUT:-$(mktemp -d -t l7verify-XXXXXX)}"
mkdir -p "$OUT"
echo "output directory: $OUT"

fail() { echo "FAIL: $*" >&2; exit 1; }
step() { echo; echo "=== $* ==="; }

LEAN_D1="$REPO/spec/lean/v3/.lake/build/bin/nearspec-v3-check-d1"
LEAN_D2="$REPO/spec/lean/v3/.lake/build/bin/nearspec-v3-check-d2"
LEAN_D3="$REPO/oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3"
LEAN_WASM="$REPO/oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-wasm"
HARNESS="${D3_HARNESS:-/data/illia/nearproof-deps/target-wasm-d3/release/near-wasm-d3-harness}"

for p in "$LEAN_D1" "$LEAN_D2" "$LEAN_D3" "$LEAN_WASM" "$HARNESS"; do
  [ -x "$p" ] || fail "missing executable: $p (build it first: see docs/logs/lean-chunk-L7-2026-10-23.md §8)"
done
[ -d "$CORPORA" ] || fail "corpora directory not found: $CORPORA"

step "1. harness self-tests"
cd "$REPO" || fail "cd"
python3 -m unittest discover -s oracle/tools -p 'test_*.py' 2>&1 | tail -3
[ "${PIPESTATUS[0]}" -eq 0 ] || fail "harness self-tests"

step "2. UQ-014 LoadingError reproducer"
python3 "$REPO/oracle/wasm-d3/tests/uq014_instance_size.py" 2>&1 | tail -8
[ "${PIPESTATUS[0]}" -eq 0 ] || fail "UQ-014 reproducer (the divergence no longer reproduces as documented)"

step "2b. UQ-014 wasmtime branch table (resource LinkError reachable, both legs agree)"
python3 "$REPO/oracle/wasm-d3/tests/uq014_wasmtime_branches.py" 2>&1 | tail -8
[ "${PIPESTATUS[0]}" -eq 0 ] || fail "UQ-014 branch table (a reachable LinkError branch changed behaviour)"

step "3. corpus content manifest"
python3 "$REPO/tools/d3/corpus_manifest.py" --corpora "$CORPORA" \
        --out "$OUT/corpus-manifest.json" 2>&1 | tail -10
[ "${PIPESTATUS[0]}" -eq 0 ] || fail "corpus manifest (a corpus no longer matches the plan's counts)"

# NOTE: difftest_v3_d1.py / _d2.py have NO --sample or --only switch (checked 2026-10-23: their
# argparse blocks are --cases/--lean/--python/--jobs/--report only), so both steps always run the
# whole corpus. --quick therefore only shortens step 6 (D3). Budget ~10 min for D1 and ~30 min for D2
# under load; a "quick" run that needs to skip them should comment these two steps out and say so.
step "4. D1 regression ($CORPORA/d1run) — full 53,048 cases, no sampling switch exists"
python3 "$REPO/oracle/tools/difftest_v3_d1.py" --cases "$CORPORA/d1run" \
        --lean "$LEAN_D1" --python "$REPO/oracle/tools/spec_check_v3_d1.py" \
        --jobs "$JOBS" --report "$OUT/d1.json" 2>&1 | tail -12
[ "${PIPESTATUS[0]}" -eq 0 ] || fail "D1 regression"

step "5. D2 regression ($CORPORA/d2corpus.v2) — full 67,384 cases, no sampling switch exists"
python3 "$REPO/oracle/tools/difftest_v3_d2.py" --cases "$CORPORA/d2corpus.v2" \
        --python "$REPO/oracle/tools/spec_check_v3_d2.py" --lean "$LEAN_D2" \
        --jobs "$JOBS" --report "$OUT/d2.json" 2>&1 | tail -14
[ "${PIPESTATUS[0]}" -eq 0 ] || fail "D2 regression"

step "6. D3 regression (four corpora, 115,284 cases)"
# The three-way comparison needs --python; without it this step only checks Lean against nearcore's
# recorded verdicts. Pass --python to reproduce the Lean-vs-Python leg as well (costs a second full
# Python run per corpus, so it is opt-in via --python-leg).
for c in d3c7 d3c8 d3c9 d3c10; do
  args=(--shards "$JOBS" --save "$OUT/$c")
  [ "$QUICK" -eq 1 ] && args+=(--sample 300)
  [ "$PYLEG" -eq 1 ] && args+=(--python)
  python3 "$REPO/oracle/v3-d3/tools/difftest_d3.py" "$CORPORA/$c" "${args[@]}" \
          2>&1 | tail -4
  [ "${PIPESTATUS[0]}" -eq 0 ] || fail "D3 regression on $c"
done

step "7. signed-surface pin check"
cd "$REPO" && make pin-check 2>&1 | tail -3
[ "${PIPESTATUS[0]}" -eq 0 ] || fail "make pin-check"

echo
if [ "$QUICK" -eq 1 ]; then
  echo "QUICK MODE: corpora were sampled (300 cases each), not run whole. This is a smoke test only;"
  echo "it does NOT establish the regression result. Re-run without --quick for the real sweep."
else
  echo "ALL STEPS PASSED (full sweep). Reports in $OUT"
fi
