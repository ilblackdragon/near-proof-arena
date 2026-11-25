#!/usr/bin/env bash
# A-T3: T1's PREP leaf (the `.pre → preConf q` step of the d3tiny call) at its pinned template.
#   run_prep.sh <work_dir> [prove|verify|tamper|all]
# 1. `wasmbase-tool airPrep` (or $AIR_PREP): the PREP AIR (WasmBase/PrepAir.lean) as JSON;
# 2. the PREP template: the segment template's commitment parameters (n_stack, w_stack, log_blowup,
#    pow, DKT certificates) with heights PHDR 4, SHA256 128, CODE/FUNC = the segment template's;
# 3. `prepleaf`: prove PREP (tight heights pinned), save PREP.vk.json, prep.proof, prep.pubs.json,
#    manifest.json; the cached CODE/FUNC commitments must equal the canonical code_root/func_root;
# 4. `prepleafverify`: reload, verify, pinned heights, public values, and R1: PREP's out roots =
#    every segment leaf's cached CODE/FUNC roots (A-T2's leaves, $SEG_LEAF);
# 5. `preptamper`: the mutant battery.
# Prover: the segment prover built against the stack backend (build_stack.sh), $WB_STACK.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
WD=${1:?work dir}; WHAT=${2:-all}
BS=${WB_STACK:-/data/illia/nearproof-deps/e2e-laneA/at3/nearproof-wasm-base-stack}
CODE=${T1_CODE:-/data/illia/nearproof-deps/e2e-laneA/T1c0/codes/8152bed25554d521d3fcdd919f4457b66e06b720906fdd40fd6fd0723ed36bf9.wasm}
PREP=${T1_PREP:-/data/illia/nearproof-deps/e2e-laneA/T1tape/prep.json}
SEG_TMPL=${SEG_TEMPLATE:-/data/illia/nearproof-deps/e2e-laneA/at2/leaf-k13p/template.json}
SEG_LEAF=${SEG_LEAF:-/data/illia/nearproof-deps/e2e-laneA/at2/leaf-k13p/leaf}
NSEG=${NSEG:-2}
CAP="${HEAVY:-/data/illia/nearproof-deps/bin/heavy}"
export HEAVY_MEM=${HEAVY_MEM:-12G} RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8}
mkdir -p "$WD"
if [ -n "${AIR_PREP:-}" ]; then cp "$AIR_PREP" "$WD/airPrep.json"; else "${T:?wasmbase-tool path in T}" airPrep > "$WD/airPrep.json"; fi
python3 - "$SEG_TMPL" "$WD/prep-template.json" "$HERE/../../final-soundness" <<'EOF'
import json, sys
t = json.load(open(sys.argv[1]))
fs = sys.argv[3]
t.update(name='t1-d3tiny-prep', certs=fs + '/calc/dkt_certs_o2.json', exclusions=fs + '/lean/DKTCertsO2_big.keys',
         heights={'PHDR': 4, 'SHA256': 128, 'CODE': t['heights']['CODE'], 'FUNC': t['heights']['FUNC']})
json.dump(t, open(sys.argv[2], 'w'), indent=1, sort_keys=True)
EOF
if [ "$WHAT" = prove ] || [ "$WHAT" = all ]; then
  rm -rf "$WD/leaf"
  $CAP "$BS" prepleaf "$WD/airPrep.json" "$CODE" "$PREP" "$WD/prep-template.json" "$WD/leaf" > "$WD/prepleaf.log" 2>&1
  grep -E 'PRECHECK|PARAMS|KEYGEN|PREPLEAF|code_root|func_root|panick' "$WD/prepleaf.log"
fi
if [ "$WHAT" = verify ] || [ "$WHAT" = all ]; then
  $CAP "$BS" prepleafverify "$WD/airPrep.json" "$WD/leaf" "$SEG_LEAF" "$NSEG" > "$WD/prepleafverify.log" 2>&1 || true
  grep -E 'PREPLEAFVERIFY|panick' "$WD/prepleafverify.log"
fi
if [ "$WHAT" = tamper ] || [ "$WHAT" = all ]; then
  $CAP "$BS" preptamper "$WD/airPrep.json" "$CODE" "$PREP" "$WD/prep-template.json" "$WD/leaf" "$SEG_LEAF" "$NSEG" > "$WD/preptamper.log" 2>&1 || true
  grep -E 'MUTANT|PREPTAMPER|panick' "$WD/preptamper.log"
fi
