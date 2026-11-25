#!/usr/bin/env bash
# G-4 (lane G): re-prove T1's INIT leaf on the G-4 AIR (main-slot selection in-circuit: `LAY` +
# `BLK` selection columns), import it into lane D's M8 leaf format (`m8-import`: TMPL.proof,
# TMPL.vk.json, INFO.json, as G-3), then run the INIT mutant battery with the prover.
#   g4.sh OUT [CASE]
# Box rules: every prover under `heavy` (HEAVY_MEM, default 10G here), <= 8 threads, temp files
# under /data/illia/nearproof-deps. LEAN=0 by default (uses an already built m5d-tool).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${1:?out}; CASE=${2:-/data/illia/nearproof-deps/corpora/d3c8/d3/02-h10196-s3}
export LEAN=${LEAN:-0} HEAVY_MEM=${HEAVY_MEM:-10G} TMPDIR=${TMPDIR:-/data/illia/nearproof-deps/tmp-laneG}
M8=${M8:-/data/illia/nearproof-deps/pq-e2e-m8/drv2/release/nearproof-chunk-e2e}
mkdir -p "$OUT/tmpl" "$TMPDIR"
TEMPLATE=init "$HERE/run.sh" "$CASE" "$OUT/t1i" prove > "$OUT/t1i.out" 2>&1
d=$OUT/t1i/proof-init
n=$(python3 -c "import json,sys; print(','.join(a['name'] for a in json.load(open(sys.argv[1]))['airs']))" "$d/statement.json")
RAYON_NUM_THREADS=1 /data/illia/nearproof-deps/bin/heavy "$M8" m8-import "$d/STATE.vk.json" "$d/STATE.proof" \
  "$OUT/tmpl/init" init "$n" > "$OUT/import-init.log" 2>&1
grep -h M8_TEMPLATE_PROVED "$OUT/import-init.log"
( cd "$OUT/tmpl" && sha256sum init/TMPL.* > SHA256SUMS )
FSCOUNT= TEMPLATE=init "$HERE/run.sh" "$CASE" "$OUT/mi" mutants > "$OUT/mi.out" 2>&1
echo "INIT mutants rejected: $(grep -c REJECTED "$OUT/mi.out") / $(grep -cE "^[a-z_0-9]+: " "$OUT/mi.out")"
