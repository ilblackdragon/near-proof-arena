#!/usr/bin/env bash
# B-T3: the `STC` mutants on T1's STATE segment (template S, `Stc.m5tSegC`).
#   stc_mutants.sh STATE_JSON OUT_DIR BIN [check|mutant] [MUTANT…]
# For each mutant: `tracegen.py --split --template templates/S.json --mutant M` on the `tmpl-segc`
# names, then the prover on the segment dump (`check`: constraints + bus balance only; `mutant`: a
# full proof attempt, `REJECTED (…)` / `ACCEPTED`). The honest dump is run first and must pass.
# Box rules: HEAVY_MEM (default 4G for check, 12G for mutant), temp files under /data/illia/nearproof-deps.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ST=$1; OUT=$2; BIN=$3; MODE=${4:-check}; shift 4 || true
MUTS=${*:-stcrin stcrout stctag stcrest stcws stclen stcbig stcbyte}
MEM=${HEAVY_MEM:-$([ "$MODE" = check ] && echo 4G || echo 12G)}
mkdir -p "$OUT/air"
"$HERE/lean/.lake/build/bin/m5a-tool" tmpl-segc 5 "$OUT/air/segc.json" "$OUT/air/segc.names.json" > "$OUT/air/segc.txt"
run() {
  local d=$1
  env HEAVY_MEM="$MEM" RAYON_NUM_THREADS=8 /data/illia/nearproof-deps/bin/heavy "$BIN" "$OUT/air/segc.json" "$d/seg0" "$MODE" > "$d.log" 2>&1 || true
  grep -E "PRECHECK|REJECTED|ACCEPTED|VERIFY|panicked" "$d.log" | head -2 | tr '\n' ' '
}
python3 "$HERE/tracegen.py" "$ST" "$OUT/air/segc.names.json" "$OUT/honest" --split --template "$HERE/templates/S.json" > /dev/null
echo "honest: $(run "$OUT/honest")"
for m in $MUTS; do
  python3 "$HERE/tracegen.py" "$ST" "$OUT/air/segc.names.json" "$OUT/m-$m" --split --template "$HERE/templates/S.json" --mutant "$m" > /dev/null
  echo "$m: $(run "$OUT/m-$m")"
  rm -rf "$OUT/m-$m"
done
