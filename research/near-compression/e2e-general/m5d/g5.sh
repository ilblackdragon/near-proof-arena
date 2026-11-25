#!/usr/bin/env bash
# G-5 (lane G): re-prove T1's INIT (big-endian `u32`, ViewE `ctxD (.raw)`) and FINAL (ViewE `ctxD (.header H)` / `outD (.done o)`, the two clear counters) leaves, import both into lane D's
# M8 leaf format (`m8-import`: TMPL.proof, TMPL.vk.json, INFO.json — the layout of
# research/near-compression/e2e/results/zk/m8/t1real/tmpl/*), then run both mutant batteries.
#   g5.sh OUT [CASE]
# Box rules: every prover under `heavy` (HEAVY_MEM, default 12G here), ≤ 8 threads, temp files
# under /data/illia/nearproof-deps. LEAN=0 by default (uses an already built m5d-tool).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${1:?out}; CASE=${2:-/data/illia/nearproof-deps/corpora/d3c8/d3/02-h10196-s3}
export LEAN=${LEAN:-0} HEAVY_MEM=${HEAVY_MEM:-12G} TMPDIR=${TMPDIR:-/data/illia/nearproof-deps/tmp-laneG}
M8=${M8:-/data/illia/nearproof-deps/pq-e2e-m8/drv2/release/nearproof-chunk-e2e}
mkdir -p "$OUT/tmpl" "$TMPDIR"
"$HERE/run.sh" "$CASE" "$OUT/t1f" prove > "$OUT/t1f.out" 2>&1
TEMPLATE=init "$HERE/run.sh" "$CASE" "$OUT/t1i" prove > "$OUT/t1i.out" 2>&1
for t in final init; do
  d=$OUT/t1${t:0:1}/proof-$t
  n=$(python3 -c "import json,sys; print(','.join(a['name'] for a in json.load(open(sys.argv[1]))['airs']))" "$d/statement.json")
  RAYON_NUM_THREADS=1 /data/illia/nearproof-deps/bin/heavy "$M8" m8-import "$d/STATE.vk.json" "$d/STATE.proof" \
    "$OUT/tmpl/$t" "$t" "$n" > "$OUT/import-$t.log" 2>&1
  grep -h M8_TEMPLATE_PROVED "$OUT/import-$t.log"
done
( cd "$OUT/tmpl" && sha256sum */TMPL.* > SHA256SUMS )
FSCOUNT= "$HERE/run.sh" "$CASE" "$OUT/mf" mutants > "$OUT/mf.out" 2>&1
FSCOUNT= TEMPLATE=init "$HERE/run.sh" "$CASE" "$OUT/mi" mutants > "$OUT/mi.out" 2>&1
echo "FINAL mutants rejected: $(grep -c REJECTED "$OUT/mf.out")  INIT: $(grep -c REJECTED "$OUT/mi.out")"
