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
# F-5: `PLAN` may be lane I's chain (`t1/chain.py plan OUT` -> OUT/chain.json): the enter / resume pairs
# are then the chain's c2 -> c3 / c6 -> c7 unchanged (`rtbnd.pair_chain`); `se-leaves` / `se-mutants`
# prove / attack the STATE engine half (`SE`, `segen.py`) on the chain's c1 -> c2, c7 -> c8, c8 -> c9;
# `stmcheck` compares the leaves' STMQ/STMA stand-in traffic with lane B's state halves (`LANEB_T1C`).
# F-7: `se-leaves` / `se-mutants` need F7EVAL (the opening rows' preimages, lean/join-check/f7-eval.sh).
# F-6: every public value is received on RNG by the boundary table (`Ids.pubBytes`); the enter AIR is
# `ENT` + `RNG`; every battery adds `nonbyte` (a non-byte copied value).
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
"$TOOL" air-se "$OUT/se.json" "$OUT/se-names.json" >> "$OUT/air.txt"
cat "$OUT/air.txt"
( cd "$HERE/prover" && CARGO_TARGET_DIR=$TARGET_DIR nice -n 10 $HEAVY cargo build --release --offline -j 8 2>/dev/null )
BIN=$TARGET_DIR/release/nearproof-e2e-m5t1
gen() { python3 "$HERE/tracegen.py" "$OUT/lean-run.json" "$OUT" "$1" --plan "$PLAN" "${@:2}"; }
case "$MODE" in
  mutants)
    for m in ${MUTANTS:-gasburnt refund status rcptid statement acctpost logbyte vmburnt bndgas bndprepaid bndburnt stcopy accnoappend rcptnoappend vmnoreset vminK ridxcopy prepaidout accitem finpre finpc finmem nonbyte}; do
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
    for m in ${MUTANTS:-phase gas stroot clock coderoot prefuel gasleft framesdig outrcpt inphase nonbyte}; do
      python3 "$HERE/entgen.py" "$PLAN" "$OUT/ent-mut-$m" --run "$OUT/lean-run.json" --template "$HERE/templates/rt-enter.json" --mutant "$m" > /dev/null
      echo "== enter mutant $m"
      nice -n 10 $HEAVY "$BIN" "$OUT/ent.json" "$OUT/ent-mut-$m" mutant | tee "$OUT/ent-mut-$m.log" | grep -E "PRECHECK FAIL|REJECTED|ACCEPTED"
    done ;;
  se-leaves|se-mutants)
    # F-7: the opening rows' preimages (lean/join-check/f7-eval.sh CASE IN OUT) and the SE column names
    SEARGS="--f7 ${F7EVAL:?set F7EVAL to the output of lean/join-check/f7-eval.sh} --names $OUT/se-names.json"
    for L in "STATE seg A" "STATE seg B" "finalize"; do
      s=$(echo "$L" | tr ' ' '-' | tr 'A-Z' 'a-z'); s=${s#state-}
      python3 "$HERE/segen.py" "$PLAN" "$L" "$OUT/se-$s" --template "$HERE/templates/state-eng.json" $SEARGS
      if [ "$MODE" = se-leaves ]; then
        nice -n 10 $HEAVY "$BIN" "$OUT/se.json" "$OUT/se-$s" prove "$OUT/se-$s-proof" | tee "$OUT/se-$s.log"
      else
        for m in ${MUTANTS:-phase vmacc prepaid gasburnt ctxcopy claimcopy clock incall stroot nonbyte tagin wsopen restin queue movein moveout tagout static finqueue finkeys}; do
          python3 "$HERE/segen.py" "$PLAN" "$L" "$OUT/se-$s-mut-$m" --template "$HERE/templates/state-eng.json" $SEARGS --mutant "$m" > /dev/null || continue
          echo "== [$L] mutant $m: $(nice -n 10 $HEAVY "$BIN" "$OUT/se.json" "$OUT/se-$s-mut-$m" mutant 2>&1 | grep -E 'PRECHECK FAIL|REJECTED|ACCEPTED' | head -1)"
        done
      fi
    done ;;
  stmcheck)
    python3 "$HERE/stmcheck.py" "${LANEB_T1C:-/data/illia/nearproof-deps/laneB-t1/t4/T1C}" \
      "$OUT/se-seg-a:seg0" "$OUT/resume:seg1" "$OUT/se-seg-b:seg2" "$OUT/se-finalize:seg3" ;;
  *)
    gen "$OUT/dump" | tee "$OUT/gen.txt"
    nice -n 10 $HEAVY "$BIN" "$OUT/m5t1.json" "$OUT/dump" "$MODE" | tee "$OUT/$MODE.log" ;;
esac
