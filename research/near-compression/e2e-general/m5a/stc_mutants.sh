#!/usr/bin/env bash
# B-T3: the `STC` mutants on T1's STATE segment (template S, `Stc.m5tSegC`).
#   stc_mutants.sh STATE_JSON OUT_DIR BIN [check|mutant] [MUTANT…]
# For each mutant: `tracegen.py --split --template templates/S.json --mutant M` on the `tmpl-segc`
# names, then the prover on the segment dump (`check`: constraints + bus balance only; `mutant`: a
# full proof attempt, `REJECTED (…)` / `ACCEPTED`). The honest dump is run first and must pass.
# KIND=segh (with GENARGS="--host --host-join join/t1-laneA-storage-write.json"): the HOST-fed template
# (`StHostIf.m5tSegH`) and its B2-4 mutants (hostnopfx hostrecv hostkind hostpl).
# Box rules: HEAVY_MEM (default 4G for check, 12G for mutant), temp files under /data/illia/nearproof-deps.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ST=$1; OUT=$2; BIN=$3; MODE=${4:-check}; shift 4 || true
KIND=${KIND:-segc}
if [ "$KIND" = segh ]; then DEF="hostnopfx hostrecv hostkind hostpl"; else DEF="stcrin stcrout stctag stcrest stcws stclen stcbig stcbyte"; fi
MUTS=${*:-$DEF}
MEM=${HEAVY_MEM:-$([ "$MODE" = check ] && echo 4G || echo 12G)}
mkdir -p "$OUT/air"
"$HERE/lean/.lake/build/bin/m5a-tool" "tmpl-$KIND" 5 "$OUT/air/$KIND.json" "$OUT/air/$KIND.names.json" > "$OUT/air/$KIND.txt"
run() {
  local d=$1
  env HEAVY_MEM="$MEM" RAYON_NUM_THREADS=8 /data/illia/nearproof-deps/bin/heavy "$BIN" "$OUT/air/$KIND.json" "$d/seg0" "$MODE" > "$d.log" 2>&1 || true
  grep -E "PRECHECK|REJECTED|ACCEPTED|VERIFY|precheck:" "$d.log" | head -2 | cut -c1-160 | tr '\n' ' '
}
python3 "$HERE/tracegen.py" "$ST" "$OUT/air/$KIND.names.json" "$OUT/honest" --split --template "$HERE/templates/S.json" ${GENARGS:-} > /dev/null
echo "honest: $(run "$OUT/honest")"
for m in $MUTS; do
  python3 "$HERE/tracegen.py" "$ST" "$OUT/air/$KIND.names.json" "$OUT/m-$m" --split --template "$HERE/templates/S.json" ${GENARGS:-} --mutant "$m" > /dev/null
  echo "$m: $(run "$OUT/m-$m")"
  rm -rf "$OUT/m-$m"
done
