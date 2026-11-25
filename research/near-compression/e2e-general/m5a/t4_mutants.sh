#!/usr/bin/env bash
# B-T4: mutants of lane B's T1 leaves cut at the rt boundaries (`--ifc --seg-keys t1cut/seg-keys.json
# --stc-meta t1cut/stc-meta.json`, template S).
#   t4_mutants.sh STATE_JSON OUT_DIR BIN [check|mutant] [MUTANT…]
# For each mutant: tracegen on the `tmpl-segc` names, then the prover on the dump the mutant targets
# (`if*` → the IF dump at `m5tIFC`, else seg0 at `m5tSegC`); `check` = constraints + bus balance only.
# The honest dumps run first and must pass. Box rules: HEAVY_MEM (default 4G for check).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ST=$1; OUT=$2; BIN=$3; MODE=${4:-check}; shift 4 || true
MUTS=${*:-"stctrie ifctrie ifcws ifcrout segsb0 stcrin stcrout stctag stcrest stcws stclen stcbig stcbyte"}
MEM=${HEAVY_MEM:-$([ "$MODE" = check ] && echo 4G || echo 12G)}
CUT="--seg-keys $HERE/t1cut/seg-keys.json --stc-meta $HERE/t1cut/stc-meta.json --ifc"
mkdir -p "$OUT/air"
TOOL=$HERE/lean/.lake/build/bin/m5a-tool
"$TOOL" tmpl-segc 5 "$OUT/air/segc.json" "$OUT/air/segc.names.json" > /dev/null
"$TOOL" tmpl-ifc 5 "$OUT/air/ifc.json" "$OUT/air/ifc.names.json" > /dev/null
run() {
  local d=$1 dump=$2 air=$OUT/air/segc.json
  [ "$dump" = if ] && air=$OUT/air/ifc.json
  env HEAVY_MEM="$MEM" RAYON_NUM_THREADS=8 /data/illia/nearproof-deps/bin/heavy "$BIN" "$air" "$d/$dump" "$MODE" > "$d.$dump.log" 2>&1 || true
  grep -E "PRECHECK|REJECTED|ACCEPTED|VERIFY|precheck:" "$d.$dump.log" | head -2 | cut -c1-170 | tr '\n' ' '
}
python3 "$HERE/tracegen.py" "$ST" "$OUT/air/segc.names.json" "$OUT/honest" --split --template "$HERE/templates/S.json" $CUT > /dev/null
for dump in if seg0 seg1 seg2 seg3; do echo "honest $dump: $(run "$OUT/honest" $dump)"; done
rm -rf "$OUT/honest"
for m in $MUTS; do
  dump=seg0; case $m in if*) dump=if ;; esac
  python3 "$HERE/tracegen.py" "$ST" "$OUT/air/segc.names.json" "$OUT/m-$m" --split --template "$HERE/templates/S.json" $CUT --mutant "$m" > /dev/null
  echo "$m ($dump): $(run "$OUT/m-$m" $dump)"
  rm -rf "$OUT/m-$m"
done
