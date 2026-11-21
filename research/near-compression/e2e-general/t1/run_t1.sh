#!/usr/bin/env bash
# M10 driver skeleton for T1 (docs/zk-formal/E2E-T1-CRITICAL-PATH.md).
#
#   run_t1.sh OUT_DIR [CASE_DIR]          extract, Lean run, calls, segment plan, components, report
#   PROVE=1 run_t1.sh OUT_DIR             also prove + verify every component that pre-checks
#   STEPS=K[,K2..]                    Wasm steps per segment (default 13,26: the plan cuts T1's 26-step call into 2 segments; 26 = the whole call is segchecked too)
#   MUTANTS=1 run_t1.sh OUT_DIR           also the statement mutants (Lean checker on each)
#
# Builds (fresh, from this tree; nothing under spec/ is rebuilt):
#   lane A prover  research/near-compression/native/wasm-base  -> $DEPS/e2e-t1/target-wb
#   lane B prover  research/near-compression/e2e-general/m5a/prover -> $DEPS/e2e-t1/target-m5a
# Lean tools come from the main checkout's .lake (override with LEAN_CHECK, WASMBASE_TOOL,
# WASMBASE_TAPE, M5A_TOOL; see t1.py). Box rules: <= 8 threads, <= 24 GB, temp under $DEPS.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
DEPS=/data/illia/nearproof-deps
OUT=${1:?out dir}
CASE=${2:-$DEPS/corpora/d3c8/d3/02-h10196-s3}
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8}
mkdir -p "$OUT" "$DEPS/e2e-t1"
if [ -z "${NOBUILD:-}" ]; then
  ( cd "$ROOT/research/near-compression/native/wasm-base" &&
    CARGO_TARGET_DIR=$DEPS/e2e-t1/target-wb nice -n 10 cargo build --release --offline -j 8 ) > "$OUT/build-wb.log" 2>&1
  ( cd "$ROOT/research/near-compression/e2e-general/m5a/prover" &&
    CARGO_TARGET_DIR=$DEPS/e2e-t1/target-m5a nice -n 10 cargo build --release --offline -j 8 ) > "$OUT/build-m5a.log" 2>&1
fi
# heavy steps inside a memory cap when systemd-run is available (shared host: <= 24 GB)
RUN=()
if command -v systemd-run >/dev/null && [ -z "${NOSCOPE:-}" ]; then
  RUN=(systemd-run --user --scope --quiet -p MemoryMax=24G -p MemorySwapMax=0)
fi
rc=0
"${RUN[@]}" python3 "$HERE/t1.py" run "$CASE" "$OUT" --steps "${STEPS:-13,26}" ${PROVE:+--prove} || rc=$?
if [ -n "${MUTANTS:-}" ]; then
  "${RUN[@]}" python3 "$HERE/t1.py" mutants "$CASE" "$OUT" --jobs 8 | tee "$OUT/mutants.txt" || rc=$?
fi
if [ "$rc" -ne 0 ]; then
  echo "run_t1.sh: FAILED (exit $rc): a component boundary disagrees with the Lean run, or a check failed; see $OUT/report.md" >&2
fi
exit "$rc"
