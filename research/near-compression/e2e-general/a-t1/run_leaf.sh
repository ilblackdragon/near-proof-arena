#!/usr/bin/env bash
# A-T1 item 3: T1's d3tiny.run call as pinned-shape tree leaves.
#   run_leaf.sh <work_dir> [K] [LOG_BLOWUP] [POW]
# 1. `segtemplate`: per-table maximum heights over T1's segments (cut every K steps);
# 2. the template file: those heights + the stack's base configuration (first-order DKT certificates,
#    m = 64, k_first 2) at LOG_BLOWUP and POW grinding bits;
# 3. `segleaf`: every segment proved at the template, one vk, proofs + vk + manifest saved;
# 4. `segleafverify`: reload vk and proofs from disk, verify, check public values and the chain.
# The prover is the segment prover built against the STACK's backend (`pq-chunk-e2e` deps):
#   WB_STACK=/data/illia/nearproof-deps/e2e-laneA/at1/target-stack/release/nearproof-wasm-base
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
. "${LANEA_ENV:-/data/illia/nearproof-deps/e2e-laneA/at1/env.sh}"
BS=${WB_STACK:-/data/illia/nearproof-deps/e2e-laneA/at1/target-stack/release/nearproof-wasm-base}
WD=${1:?work dir}; K=${2:-13}; LB=${3:-1}; POW=${4:-24}
PREP=${T1_PREP:-/data/illia/nearproof-deps/e2e-laneA/T1tape/prep.json}
mkdir -p "$WD"; cd "$WD"
cp "$PREP" t1.prep.json
$T airSegMP 0 0 > airSeg0.json
if [ -n "${AIR_PATCH:-}" ]; then python3 "$HERE/patch_air_json.py" airSeg0.json airSeg.json; else cp airSeg0.json airSeg.json; fi
NL=$(python3 -c "import json;p=json.load(open('t1.prep.json'));print(len(p['localTags']),p['ngl'])")
$T airM2 $NL > airM2.json
$CAP $BS segtemplate airSeg.json airM2.json t1.prep.json "$K" > template.log 2>&1
grep TEMPLATE_SEGMENTS template.log
tail -1 template.log | python3 -c "
import json,sys
t=json.load(sys.stdin)
t.update(name='t1-d3tiny-k$K', log_blowup=$LB, pow=$POW,
  certs='$ROOT/research/near-compression/final-soundness/calc/dkt_certs_o2.json',
  exclusions='$ROOT/research/near-compression/final-soundness/lean/DKTCertsO2_big.keys')
json.dump(t,open('template.json','w'),indent=1,sort_keys=True)"
$CAP $BS segleaf airSeg.json airM2.json t1.prep.json "$K" template.json leaf > segleaf.log 2>&1
grep -E 'PARAMS|KEYGEN|LEAF|SEGLEAF|panick' segleaf.log
N=$(ls leaf/seg-*.proof | wc -l)
$CAP $BS segleafverify airSeg.json leaf "$N" > segleafverify.log 2>&1
grep -E 'DISK|SEGLEAFVERIFY|panick' segleafverify.log
