#!/usr/bin/env bash
# E2E M5a: INTAKE + working-set tree + FINAL for one corpus chunk's main transition.
#   run.sh CASE_DIR OUT_DIR [check|prove|mutants]      (D=5: working set ≤ 32 keys; D=6 for T2)
#   MUTANTS="…" picks the mutant battery (default: the four statement-level ones, the T2 row tampers
#   and the batched-FINAL ones); UNBATCHED=1 writes the first pass (every node hashed, as in M5a);
#   GENARGS="--segs S --extra-writes N" cuts the write log into S segments / adds intermediate writes
#   (M5a-3); TARGET_DIR picks the cargo target directory
# Box rules: ≤ 8 threads, HEAVY_MEM=32G, temp files under /data/illia/nearproof-deps.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
CASE=$1; OUT=$2; MODE=${3:-prove}; D=${D:-5}
DEPS=/data/illia/nearproof-deps/e2e-m5a
TARGET_DIR=${TARGET_DIR:-$DEPS/target}
HEAVY="env HEAVY_MEM=${HEAVY_MEM:-32G} RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8} /data/illia/nearproof-deps/bin/heavy"
LEAN_CHECK=${LEAN_CHECK:-/data/illia/nearproof/spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor}
mkdir -p "$OUT"
# 1. the Lean allFeatures run's write log, and the clean-room checker's access set (cross-checked)
#    (a synthetic case: write `synth.py NAME OUT_DIR/state.json` first; CASE_DIR is then unused)
[ -f "$OUT/state.json" ] || [ -f "$OUT/lean-full.json" ] || "$LEAN_CHECK" --tier allFeatures --emit-full "$CASE" > "$OUT/lean-full.json"
[ -f "$OUT/state.json" ] || python3 "$HERE/extract_state.py" "$CASE" "$OUT/lean-full.json" "$OUT/state.json"
# 2. the AIR, exported from Lean
( cd "$HERE/lean" && lake build m5a-tool >/dev/null )
"$HERE/lean/.lake/build/bin/m5a-tool" air "$D" "$OUT/m5a.json" "$OUT/names.json" > "$OUT/air.txt"
# 2b. the spec oracle: the Lean spec's applyChanges on the revealed pre-state reaches the claimed root
WANT=$(python3 -c "import json,sys; print(json.load(open(sys.argv[1]))['post_root'])" "$OUT/state.json")
GOT=$("$HERE/lean/.lake/build/bin/m5a-tool" apply "$OUT/state.json")
[ "$GOT" = "$WANT" ] || { echo "spec oracle: $GOT != $WANT"; exit 1; }
echo "spec oracle: post-state root $GOT (Lean applyChanges)"
# 3. prover
( cd "$HERE/prover" && CARGO_TARGET_DIR=$TARGET_DIR nice -n 10 $HEAVY cargo build --release --offline -j 8 2>/dev/null )
BIN=$TARGET_DIR/release/nearproof-e2e-m5a
gen() { python3 "$HERE/tracegen.py" "$OUT/state.json" "$OUT/names.json" "$1" "${@:2}" ${UNBATCHED:+--unbatched} ${GENARGS:-}; }
if [ "$MODE" = mutants ]; then
  for m in ${MUTANTS:-node prevalue omitwrite postroot absent extabsent branchval split splitext absdel squash chain verslot vernid vmcount finroot nidforge wsstale wssib wsdrop wsabsorb wsleaf}; do
    gen "$OUT/mut-$m" --mutant "$m" > "$OUT/mut-$m.gen.txt"
    nice -n 10 $HEAVY "$BIN" "$OUT/m5a.json" "$OUT/mut-$m" mutant | tee "$OUT/mut-$m.log" | grep -E "PRECHECK|REJECTED|ACCEPTED|VERIFY"
  done
else
  gen "$OUT/dump" | tee "$OUT/gen.txt"
  nice -n 10 $HEAVY "$BIN" "$OUT/m5a.json" "$OUT/dump" "$MODE" | tee "$OUT/$MODE.log"
fi
