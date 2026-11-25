#!/usr/bin/env bash
# E2E lane F: the `rt` templates of a chunk's FunctionCall receipt (M5-T1 rows, F-2 leaves).
#   run.sh CASE_DIR OUT_DIR [check|prove|mutants|leaves|leaf-mutants]
# 1. the Lean run (`m5t1-tool dump`: the checker's own INTAKE + engine steps, every incoming receipt
#    through the oracle form of the receipt step, recorded);
# 2. the AIRs, exported from Lean (`m5t1-tool air`: resume; `m5t1-tool air-ent`: enter);
# 3. the traces (`tracegen.py`, every value asserted against the Lean run; `entgen.py`); the public
#    boundary pairs come from lane I's driver plan (`PLAN`, `t1.py run` → plan.json) and are checked
#    against the Lean run and against the plan's digests (`rtbnd.py`);
# 4. the prover (main PQ stack: unified SWIRL, BabyBear Ext12, SHA-384 42-B digests, stacked WHIR).
# `leaves`: both T1 rt leaves (enter, resume) at their pinned templates (`templates/`, lane D's base
# configuration), proof + vk + statement saved under OUT/{enter,resume}-proof.
# F-4: the resume leaf adds `RB`, `ACC` and lane B's native SHA-512 chip (`comps.json`); `RESUME_ONLY=1`
# with `leaves` proves only the resume leaf (the enter AIR is unchanged since F-3).
# MUTANTS="…" picks the mutant battery. Box rules: ≤ 8 threads, HEAVY_MEM ≤ 40G, temp files under
# /data/illia/nearproof-deps.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
CASE=$1; OUT=$2; MODE=${3:-prove}
PLAN=${PLAN:-/data/illia/nearproof-deps/e2e-t1/run4/plan.json}
DEPS=/data/illia/nearproof-deps/e2e-m5t1
TARGET_DIR=${TARGET_DIR:-$DEPS/target-f2}
HEAVY="env HEAVY_MEM=${HEAVY_MEM:-40G} RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8} /data/illia/nearproof-deps/bin/heavy"
mkdir -p "$OUT"
( cd "$HERE/lean" && lake build m5t1-tool >/dev/null )
TOOL="$HERE/lean/.lake/build/bin/m5t1-tool"
[ -f "$OUT/lean-run.json" ] || "$TOOL" dump "$CASE" "$OUT/lean-run.json"
"$TOOL" air "$OUT/m5t1.json" "$OUT/names.json" "$OUT/schema.json" > "$OUT/air.txt"
"$TOOL" air-ent "$OUT/ent.json" "$OUT/ent-names.json" >> "$OUT/air.txt"
cat "$OUT/air.txt"
( cd "$HERE/prover" && CARGO_TARGET_DIR=$TARGET_DIR nice -n 10 $HEAVY cargo build --release --offline -j 8 2>/dev/null )
BIN=$TARGET_DIR/release/nearproof-e2e-m5t1
gen() { python3 "$HERE/tracegen.py" "$OUT/lean-run.json" "$OUT" "$1" --plan "$PLAN" "${@:2}"; }
case "$MODE" in
  mutants)
    for m in ${MUTANTS:-gasburnt refund status rcptid statement acctpost logbyte vmburnt bndgas bndprepaid bndburnt stcopy accnoappend rcptnoappend vmnoreset vminK ridxcopy prepaidout accitem}; do
      rc=0; gen "$OUT/mut-$m" --mutant "$m" > "$OUT/mut-$m.gen.txt" || rc=$?
      if [ "$rc" = 3 ]; then echo "$m: NOT APPLICABLE"; continue; fi
      [ "$rc" = 0 ] || { echo "$m: tracegen failed (exit $rc)"; cat "$OUT/mut-$m.gen.txt"; exit "$rc"; }
      echo "== mutant $m: $(grep 'mutant applied' "$OUT/mut-$m.gen.txt")"
      nice -n 10 $HEAVY "$BIN" "$OUT/m5t1.json" "$OUT/mut-$m" mutant | tee "$OUT/mut-$m.log" | grep -E "PRECHECK|REJECTED|ACCEPTED|VERIFY"
    done ;;
  leaves)
    if [ "${RESUME_ONLY:-0}" != 1 ]; then
      python3 "$HERE/entgen.py" "$PLAN" "$OUT/enter" --run "$OUT/lean-run.json" --template "$HERE/templates/rt-enter.json"
      nice -n 10 $HEAVY "$BIN" "$OUT/ent.json" "$OUT/enter" prove "$OUT/enter-proof" | tee "$OUT/enter.log"
    fi
    gen "$OUT/resume" --template "$HERE/templates/rt-resume-T1.json" | tee "$OUT/resume.gen.txt"
    nice -n 10 $HEAVY "$BIN" "$OUT/m5t1.json" "$OUT/resume" prove "$OUT/resume-proof" | tee "$OUT/resume.log" ;;
  leaf-mutants)
    for m in ${MUTANTS:-phase gas stroot clock coderoot prefuel gasleft framesdig outrcpt inphase}; do
      python3 "$HERE/entgen.py" "$PLAN" "$OUT/ent-mut-$m" --run "$OUT/lean-run.json" --template "$HERE/templates/rt-enter.json" --mutant "$m" > /dev/null
      echo "== enter mutant $m"
      nice -n 10 $HEAVY "$BIN" "$OUT/ent.json" "$OUT/ent-mut-$m" mutant | tee "$OUT/ent-mut-$m.log" | grep -E "PRECHECK FAIL|REJECTED|ACCEPTED"
    done ;;
  *)
    gen "$OUT/dump" | tee "$OUT/gen.txt"
    nice -n 10 $HEAVY "$BIN" "$OUT/m5t1.json" "$OUT/dump" "$MODE" | tee "$OUT/$MODE.log" ;;
esac
