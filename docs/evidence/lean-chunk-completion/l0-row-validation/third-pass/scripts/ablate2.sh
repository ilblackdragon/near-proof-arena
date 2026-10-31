#!/bin/bash
# Controls for W-005 / W-006 (wasm:prep / wasm:compile) and the D2-020/023/025 guards.
set -u
cd /data/illia/nearproof-deps/l0-validate/b4
W=/data/illia/nearproof/.claude/worktrees/agent-a8b3a000da794c665
CTL=/data/illia/nearproof-deps/l0-validate/tree-g/spec/lean/v3/.lake/build/bin/nearspec-v3-ctl-successor
python3 $W/tools/d3/l0_exercise.py map --trace trace-r2.jsonl --out map-r2-x.json \
  --exclude-sources 'nearcore(cold,tx_valid=claim)' derived > /dev/null
HEAVY_MEM=32G /data/illia/nearproof-deps/bin/heavy python3 $W/tools/d3/l0_exercise.py ablate --binary $CTL \
  --map map-r2-x.json --out ablate-r2.json --workdir abl-r2 --jobs 4 --targets wasm:prep wasm:compile
HEAVY_MEM=32G /data/illia/nearproof-deps/bin/heavy python3 $W/tools/d3/l0_exercise.py ablate --binary $CTL \
  --map map-r2-x.json --out ablate-r2g.json --workdir abl-r2g --jobs 4 --k-reject 12 --targets \
  "guard:invalid: new transaction exceeds max_transaction_size" "guard:invalid: slot count" \
  "guard:invalid: height_included above block height (block_congestion_info panics)"
