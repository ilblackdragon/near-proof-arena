#!/usr/bin/env bash
# Milestone 1 of docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md: prove a real corpus call's Wasm execution
# on the main PQ stack (unified SWIRL, BabyBear Ext12, SHA-384/42-B, stacked WHIR).
#
#   run.sh CASE_DIR CALL_INDEX OUT_DIR
#
# 1. extract the chunk's VM calls with the independent clean-room checker (extract_calls.py);
# 2. run the Lean spec interpreter on that call's code, method, prepaid gas and input (wasmbase-tool
#    prepIf), from a freshly built tool;
# 3. compare the spec run against the chunk's outcome (compare.py);
# 4. export the IF+host AIR from Lean, prove and verify (nearproof-wasm-base prove), then run the
#    mutation suite (nearproof-wasm-base tamper).
# Heavy steps run under `heavy` with at most 12 CPUs. Builds must be fresh (HANDOVER: stale binaries).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
CASE=$1; IDX=$2; OUT=$3
mkdir -p "$OUT/codes"
TOOL=$ROOT/research/near-compression/wasm-base-lean/.lake/build/bin/wasmbase-tool
PROVER=${PROVER:-/data/illia/nearproof-deps/e2e-m1/target/release/nearproof-wasm-base}
HEAVY="env HEAVY_MEM=16G taskset -c 8-15,24-27 /data/illia/nearproof-deps/bin/heavy"

python3 "$HERE/extract_calls.py" "$CASE" --code-dir "$OUT/codes" > "$OUT/calls.json"
read -r SHA METHOD PREPAID INPUT < <(python3 -c "
import json,sys; c=json.load(open('$OUT/calls.json'))['calls'][$IDX]
print(c['code_sha256'], c['method'], c['prepaid'], c['input'] or '')")
WASM=$OUT/codes/$SHA.wasm
"$TOOL" prepIf "$WASM" "$METHOD" "$PREPAID" "$INPUT" > "$OUT/prep.json"
read -r NLOC NGL < <(python3 -c "
import json; p=json.load(open('$OUT/prep.json')); print(len(p['localTags']), p['ngl'])")
"$TOOL" airIfH "$NLOC" "$NGL" > "$OUT/air.json"
"$PROVER" hostb-dump "$OUT/air.json" "$OUT/prep.json" > "$OUT/hostb.log"
python3 "$HERE/compare.py" "$OUT/calls.json" "$IDX" "$OUT/prep.json" "$OUT/hostb.log" | tee "$OUT/compare.txt" || echo "compare: MISMATCH recorded in $OUT/compare.txt (continuing to prove the spec trace)"
"$PROVER" check "$OUT/air.json" "$OUT/prep.json" > "$OUT/check.log"
[ -n "${NOPROVE:-}" ] && exit 0
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-12}
WASMBASE_WASM=$WASM WASMBASE_PROOF_OUT=$OUT/proof.bin $HEAVY "$PROVER" prove "$OUT/air.json" "$OUT/prep.json" small \
  2>&1 | tee "$OUT/prove.log"
$HEAVY "$PROVER" tamper "$OUT/air.json" "$OUT/prep.json" 2>&1 | tee "$OUT/tamper.log"
