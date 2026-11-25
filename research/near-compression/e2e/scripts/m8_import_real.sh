#!/usr/bin/env bash
# E2E-D M8: import the lanes' own saved T1 leaves (no re-proving) into WORK/tmpl/:
#   lane A A-T2 (pinned-shape Wasm segments, tight heights pinned, stack backend): SEG.vk.json + seg-<i>.proof
#   lane B B-T1 (pinned-shape state leaves, template T1/S): IF and seg0 STATE.{vk.json,proof}
# Each is verified natively by the driver and described in INFO.json (m8-import).
#   usage: m8_import_real.sh WORK
set -euo pipefail
O=${1:?work}
P=${PROVER:-/data/illia/nearproof-deps/pq-e2e-m8/drv2/release/nearproof-chunk-e2e}
LA=${LANE_A_LEAF:-/data/illia/nearproof-deps/e2e-laneA/at2/leaf-k13p/leaf}  # A-T2: tight heights pinned (A-T1: at1/leaf-k13c/leaf)
LB=${LANE_B_LEAF:-/data/illia/nearproof-deps/laneB-t1/t1b/T1S}
names() { python3 -c "import json,sys; print(','.join(a['name'] for a in json.load(open(sys.argv[1]))['airs']))" "$1"; }
mkdir -p "$O/tmpl"
imp() { RAYON_NUM_THREADS=1 taskset -c "${CPU:-9}" "$P" m8-import "$@" > "$O/import-$(basename "$3").log" 2>&1 || { tail -5 "$O/import-$(basename "$3").log"; exit 1; }; grep -h M8_TEMPLATE_PROVED "$O/import-$(basename "$3").log"; }
for i in 0 1; do imp "$LA/SEG.vk.json" "$LA/seg-$i.proof" "$O/tmpl/wasm$i" wasm_seg -; done
imp "$LB/if/out/STATE.vk.json" "$LB/if/out/STATE.proof" "$O/tmpl/state_if" state_if "$(names "$LB/if/out/statement.json")"
imp "$LB/seg0/out/STATE.vk.json" "$LB/seg0/out/STATE.proof" "$O/tmpl/state_seg0" state_seg "$(names "$LB/seg0/out/statement.json")"
sha256sum "$LA"/SEG.vk.json "$LA"/seg-*.proof "$LB"/if/out/STATE.* "$LB"/seg0/out/STATE.* > "$O/imported.sha256"
echo M8_IMPORT_OK
