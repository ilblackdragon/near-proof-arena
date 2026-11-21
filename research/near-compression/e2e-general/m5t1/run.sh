#!/usr/bin/env bash
# E2E M5-T1 (lane F): the runtime rows of a chunk's incoming FunctionCall receipts.
#   run.sh CASE_DIR OUT_DIR [check|prove|mutants]
# 1. the Lean run (`m5t1-tool dump`: the checker's own INTAKE + engine steps, every incoming receipt
#    through the oracle form of the receipt step, recorded);
# 2. the AIR, exported from Lean (`m5t1-tool air`);
# 3. the trace (`tracegen.py`, every value asserted against the Lean run);
# 4. the prover (main PQ stack: unified SWIRL, BabyBear Ext12, SHA-384 42-B digests, stacked WHIR).
# MUTANTS="…" picks the mutant battery. Box rules: ≤ 8 threads, HEAVY_MEM ≤ 40G, temp files under
# /data/illia/nearproof-deps.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
CASE=$1; OUT=$2; MODE=${3:-prove}
DEPS=/data/illia/nearproof-deps/e2e-m5t1
TARGET_DIR=${TARGET_DIR:-$DEPS/target}
HEAVY="env HEAVY_MEM=${HEAVY_MEM:-40G} RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8} /data/illia/nearproof-deps/bin/heavy"
mkdir -p "$OUT"
( cd "$HERE/lean" && lake build m5t1-tool >/dev/null )
TOOL="$HERE/lean/.lake/build/bin/m5t1-tool"
[ -f "$OUT/lean-run.json" ] || "$TOOL" dump "$CASE" "$OUT/lean-run.json"
"$TOOL" air "$OUT/m5t1.json" "$OUT/names.json" "$OUT/schema.json" > "$OUT/air.txt"
cat "$OUT/air.txt"
( cd "$HERE/prover" && CARGO_TARGET_DIR=$TARGET_DIR nice -n 10 $HEAVY cargo build --release --offline -j 8 2>/dev/null )
BIN=$TARGET_DIR/release/nearproof-e2e-m5t1
gen() { python3 "$HERE/tracegen.py" "$OUT/lean-run.json" "$OUT" "$1" "${@:2}"; }
if [ "$MODE" = mutants ]; then
  for m in ${MUTANTS:-gasburnt refund status rcptid statement acctpost logbyte vmburnt}; do
    rc=0; gen "$OUT/mut-$m" --mutant "$m" > "$OUT/mut-$m.gen.txt" || rc=$?
    if [ "$rc" = 3 ]; then echo "$m: NOT APPLICABLE"; continue; fi
    [ "$rc" = 0 ] || { echo "$m: tracegen failed (exit $rc)"; cat "$OUT/mut-$m.gen.txt"; exit "$rc"; }
    echo "== mutant $m: $(grep 'mutant applied' "$OUT/mut-$m.gen.txt")"
    nice -n 10 $HEAVY "$BIN" "$OUT/m5t1.json" "$OUT/mut-$m" mutant | tee "$OUT/mut-$m.log" | grep -E "PRECHECK|REJECTED|ACCEPTED|VERIFY"
  done
else
  gen "$OUT/dump" | tee "$OUT/gen.txt"
  nice -n 10 $HEAVY "$BIN" "$OUT/m5t1.json" "$OUT/dump" "$MODE" | tee "$OUT/$MODE.log"
fi
