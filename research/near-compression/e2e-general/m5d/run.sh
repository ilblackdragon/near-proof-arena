#!/usr/bin/env bash
# E2E M5d (lane G): the FINAL template (class F1) of one corpus chunk, on the main PQ stack.
#   run.sh CASE_DIR OUT_DIR [check|prove|mutants]
#   MUTANTS="…" picks the mutant battery (default: every mutant of tracegen.py's MUTANTS).
# Box rules: ≤ 8 threads, prover ≤ 40 GB (HEAVY_MEM), temp files under /data/illia/nearproof-deps.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
CASE=$1; OUT=$2; MODE=${3:-prove}
DEPS=/data/illia/nearproof-deps/e2e-m5d
TARGET_DIR=${TARGET_DIR:-$DEPS/target}
HEAVY="env HEAVY_MEM=${HEAVY_MEM:-40G} RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8} /data/illia/nearproof-deps/bin/heavy"
TOOL=$HERE/lean/.lake/build/bin/m5d-tool
BIN=$TARGET_DIR/release/nearproof-e2e-m5d
mkdir -p "$OUT"
"$HERE/build.sh" >/dev/null
# 1. the Lean checker's own FINAL on the case (finK + tailNew), with recomputation self-checks
"$TOOL" dump "$CASE" "$OUT/dump.json"
# 2. the AIR, exported from Lean
"$TOOL" air-final "$OUT/final.json" "$OUT/final-names.json" > "$OUT/air.txt"
gen() { python3 "$HERE/tracegen.py" "$OUT/dump.json" "$OUT/final-names.json" "$1" "${@:2}"; }
if [ "$MODE" = mutants ]; then
  ALL=$(python3 -c "import sys; sys.path.insert(0, '$HERE'); import tracegen; print(' '.join(tracegen.MUTANTS))")
  for m in ${MUTANTS:-$ALL}; do
    rc=0; gen "$OUT/mut-$m" --mutant "$m" > "$OUT/mut-$m.gen.txt" || rc=$?
    if [ "$rc" = 3 ]; then echo "$m: NOT APPLICABLE"; continue; fi
    [ "$rc" = 0 ] || { echo "$m: tracegen failed (exit $rc)"; cat "$OUT/mut-$m.gen.txt"; exit "$rc"; }
    echo -n "$m: "
    nice -n 10 $HEAVY "$BIN" "$OUT/final.json" "$OUT/final-names.json" "$OUT/mut-$m" mutant > "$OUT/mut-$m.log" 2>&1 || true
    grep -E "PRECHECK FAIL|REJECTED|ACCEPTED" "$OUT/mut-$m.log" | tr '\n' ' ' | cut -c1-220; echo
    rm -rf "$OUT/mut-$m"
  done
else
  gen "$OUT/dump-final" | tee "$OUT/gen.txt"
  nice -n 10 $HEAVY "$BIN" "$OUT/final.json" "$OUT/final-names.json" "$OUT/dump-final" "$MODE" | tee "$OUT/$MODE.log"
fi
