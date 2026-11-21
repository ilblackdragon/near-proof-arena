#!/usr/bin/env bash
# A-T1 item 5: the joined segment AIR `wasmBaseSegAirMPJ` (`airSegMPJ`) on lane A's own traces.
#   run_j.sh <work_dir> <prep.json> [K]
# A call without storage_write/storage_remove pre-checks fully (the J columns are filled by the
# tracer); a call with them fails exactly on the storage HOSTQ/HOSTR/HB messages, which lane B's
# state rows supply in the joined trace.
set -uo pipefail
. /data/illia/nearproof-deps/e2e-laneA/at1/env.sh
WD=${1:?}; PREP=${2:?}; K=${3:-13}
mkdir -p "$WD"; cd "$WD"; cp "$PREP" p.json
$T airSegMPJ 0 0 > airJ.json
NL=$(python3 -c "import json;p=json.load(open('p.json'));print(len(p['localTags']),p['ngl'])")
$T airM2 $NL > airM2.json
$CAP $B segcheck airJ.json airM2.json p.json "$K" > segcheckJ.log 2>&1
echo "rc=$?"; grep -E 'PRECHECK|SEGCHECK|panick|unbalanced' segcheckJ.log | cut -c1-260 | head -12
