#!/usr/bin/env bash
# B-T4: import lane B's five T1 leaves (leaf.sh OUT, `--ifc --seg-keys`) into lane D's M8 leaf format
# (`m8-import`: TMPL.proof, TMPL.vk.json, INFO.json; `M8_TEMPLATE_PROVED <name>`), with the `STC`
# stand-in's messages (`htape.json`) next to each.
#   import.sh OUT
set -euo pipefail
OUT=${1:?out}
M8=${M8:-/data/illia/nearproof-deps/pq-e2e-m8/drv2/release/nearproof-chunk-e2e}
mkdir -p "$OUT/tmpl"
for p in if:state-if seg0:state-a seg1:state-resume seg2:state-b seg3:state-fin; do
  d=$OUT/${p%%:*}/out; t=${p##*:}
  n=$(python3 -c "import json,sys; print(','.join(a['name'] for a in json.load(open(sys.argv[1]))['airs']))" "$d/statement.json")
  RAYON_NUM_THREADS=1 HEAVY_MEM=${HEAVY_MEM:-4G} /data/illia/nearproof-deps/bin/heavy "$M8" m8-import "$d/STATE.vk.json" \
    "$d/STATE.proof" "$OUT/tmpl/$t" "$t" "$n" > "$OUT/import-$t.log" 2>&1
  cp "$d/htape.json" "$OUT/tmpl/$t/htape.json"
  grep -h M8_TEMPLATE_PROVED "$OUT/import-$t.log"
done
( cd "$OUT/tmpl" && sha256sum */TMPL.* */htape.json > SHA256SUMS )
