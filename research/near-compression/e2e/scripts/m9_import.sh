#!/usr/bin/env bash
# E2E-D M9: import every T1 leaf the lanes saved (no re-proving) into WORK/tmpl/:
#   lanes A / B (as M8, m8_import_real.sh): wasm0, wasm1, state_if, state_seg0
#   lane F F-2: rt_enter, rt_resume (RT.{vk.json,proof}, base configuration, pinned shapes)
#   lane G G-3: init, final (TMPL.{vk.json,proof}; lane G ran m8-import on them, re-verified here)
# Each is verified natively by lane D's driver and described in INFO.json (m8-import).
#   usage: m9_import.sh WORK
# M9 swap path: LANE_A_LEAF=<dir with SEG.vk.json + seg-<i>.proof> points the WASM leaves at lane A's
# re-proved (pinned-height) segments; everything else is unchanged.
set -euo pipefail
O=${1:?work}
S=$(cd "$(dirname "$0")" && pwd)
P=${PROVER:-/data/illia/nearproof-deps/pq-e2e-m8/drv2/release/nearproof-chunk-e2e}
LF=${LANE_F_LEAF:-/data/illia/nearproof-deps/e2e-m5t1/f2b}
LG=${LANE_G_LEAF:-/data/illia/nearproof-deps/e2e-m5d/g3/tmpl}
# INIT: lane G G-4 (main slot fixed in-circuit, table LAY; 355,691 B) by default; G-3 with LANE_G_INIT=.../g3/tmpl
LGI=${LANE_G_INIT:-/data/illia/nearproof-deps/e2e-m5d/g4/tmpl}
PROVER=$P "$S/m8_import_real.sh" "$O"
names() { python3 -c "import json,sys; print(','.join(a['name'] for a in json.load(open(sys.argv[1]))['airs']))" "$1"; }
imp() { RAYON_NUM_THREADS=1 taskset -c "${CPU:-9}" "$P" m8-import "$@" > "$O/import-$(basename "$3").log" 2>&1 || { tail -5 "$O/import-$(basename "$3").log"; exit 1; }; grep -h M8_TEMPLATE_PROVED "$O/import-$(basename "$3").log"; }
for t in enter resume; do imp "$LF/$t-proof/RT.vk.json" "$LF/$t-proof/RT.proof" "$O/tmpl/rt_$t" "rt_$t" "$(names "$LF/$t-proof/statement.json")"; done
INAMES=$(python3 -c "import json,sys; print(','.join(json.load(open(sys.argv[1]))['airs']))" "$LGI/init/INFO.json")
imp "$LGI/init/TMPL.vk.json" "$LGI/init/TMPL.proof" "$O/tmpl/init" init "$INAMES"
imp "$LG/final/TMPL.vk.json" "$LG/final/TMPL.proof" "$O/tmpl/final" final SHA,S384,RNG,STMT,FIN,BODY,SEG,RS,PART,SHD,OUTL,MRK,SHA512,SHA512T
# M9b: lane A's PREP leaf (A-T3, wasm kind) when LANE_A_PREP is set (dir with PREP.vk.json + prep.proof)
if [ -n "${LANE_A_PREP:-}" ]; then imp "$LANE_A_PREP/PREP.vk.json" "$LANE_A_PREP/prep.proof" "$O/tmpl/prep" wasm_prep PHDR,SHA256,CODE,FUNC; sha256sum "$LANE_A_PREP"/PREP.vk.json "$LANE_A_PREP"/prep.proof >> "$O/imported.sha256"; fi
sha256sum "$LF"/{enter,resume}-proof/RT.* "$LGI"/init/TMPL.* "$LG"/final/TMPL.* >> "$O/imported.sha256"
echo M9_IMPORT_OK
