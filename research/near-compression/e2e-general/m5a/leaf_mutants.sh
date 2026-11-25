#!/usr/bin/env bash
# B-T1: mutants of the template cut.  For each mutant the case is re-generated (`tracegen.py --split
# --template … --mutant M`) and every dump is handed to the prover's `mutant` mode (precheck without
# the assertion, then keygen / prove / native verify / statement check).  A mutant is rejected iff
# some dump is refused (precheck failure plus the prover's refusal or a failed verification), or
# the leaf chain (`leaf_chain.py`) fails.
#   leaf_mutants.sh STATE_JSON OUT_DIR TEMPLATE_JSON "m1 m2 …" [GENARGS…]
# (run `leaf.sh … check` first: it exports the AIRs into OUT_DIR/air and builds the prover)
# MUT_MODE=check: precheck only (every constraint and bus; no proof attempt).
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ST=$1; OUT=$2; TMPL=$3; MUTS=$4; shift 4
DEPS=/data/illia/nearproof-deps/laneB-t1
BIN=${TARGET_DIR:-$DEPS/target}/release/nearproof-e2e-m5a
HEAVY="env HEAVY_MEM=${HEAVY_MEM:-40G} RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8} /data/illia/nearproof-deps/bin/heavy"
TOOL=$HERE/lean/.lake/build/bin/m5a-tool
ORACLE=$("$TOOL" apply "$ST")
NAMES=$OUT/air/segc.names.json
case " $* " in *" --host "*) NAMES=$OUT/air/segh.names.json ;; esac
[ -n "${NO_STC:-}" ] && NAMES=$OUT/air/if.names.json
for m in $MUTS; do
  M=$OUT/mut-$m
  rm -rf "$M"; mkdir -p "$M"
  rc=0
  python3 "$HERE/tracegen.py" "$ST" "$NAMES" "$M" --split --template "$TMPL" --mutant "$m" "$@" > "$M/gen.txt" 2>&1 || rc=$?
  if [ "$rc" = 3 ]; then echo "MUTANT $m: NOT APPLICABLE"; continue; fi
  [ "$rc" = 0 ] || { echo "MUTANT $m: tracegen failed (rc $rc)"; tail -3 "$M/gen.txt"; continue; }
  verdict=ACCEPTED; why=""
  for d in "$M"/if "$M"/seg*; do
    [ -d "$d" ] || continue
    air=$OUT/air/seg.json; [ "$(basename "$d")" = if ] && air=$OUT/air/if.json
    [ -f "$d/hosttape.json" ] && air=$OUT/air/segh.json
    grep -q '"STC"' "$d/tables.json" && air=$OUT/air/segc.json
    if [ "${MUT_MODE:-mutant}" = check ]; then
      # check only: the precheck (every constraint, every bus) without proving
      nice -n 10 $HEAVY "$BIN" "$air" "$d" check > "$d/mutant.log" 2>&1
      pre=$(grep -oE "PRECHECK OK[^;]*|precheck: [^;]*" "$d/mutant.log" | head -1 | cut -c1-160)
      res=ACCEPTED; grep -q "PRECHECK OK" "$d/mutant.log" || res="REJECTED (precheck)"
    else
      nice -n 10 $HEAVY "$BIN" "$air" "$d" mutant "$d/out" > "$d/mutant.log" 2>&1
      pre=$(grep -oE "PRECHECK (OK|FAIL)[^;]*" "$d/mutant.log" | head -1 | cut -c1-160)
      res=$(grep -oE "REJECTED.*|ACCEPTED" "$d/mutant.log" | head -1 | cut -c1-120)
    fi
    if [ "$res" != ACCEPTED ]; then verdict=REJECTED; why="$why $(basename "$d"): [$pre] $res;"; fi
  done
  if [ "$verdict" = ACCEPTED ]; then
    if ! python3 "$HERE/leaf_chain.py" "$M" "$ORACLE" > "$M/chain.txt" 2>&1; then
      verdict=REJECTED; why="every proof verifies; leaf chain: $(grep -E 'MISMATCH|FAILED' "$M/chain.txt" | head -2 | tr '\n' ' ')"
    fi
  fi
  echo "MUTANT $m: $verdict —$why"
  rm -f "$M"/*/*.bin "$M"/*/out/STATE.vk.json
done
