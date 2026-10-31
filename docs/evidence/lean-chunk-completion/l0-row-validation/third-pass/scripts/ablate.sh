#!/bin/bash
# Usage: ablate.sh NAME TARGET... -> map-NAME-x.json (tx_valid-flip / derived cases excluded),
# ablate-NAME.json (baseline + ablated replays of up to 12 accepted / 4 rejected exercising cases)
set -u
cd /data/illia/nearproof-deps/l0-validate/b4
W=/data/illia/nearproof/.claude/worktrees/agent-a8b3a000da794c665
CTL=/data/illia/nearproof-deps/l0-validate/tree-g/spec/lean/v3/.lake/build/bin/nearspec-v3-ctl-successor
N=$1; shift
python3 $W/tools/d3/l0_exercise.py map --trace trace-$N.jsonl --out map-$N-x.json \
  --exclude-sources 'nearcore(cold,tx_valid=claim)' derived > /dev/null
HEAVY_MEM=32G /data/illia/nearproof-deps/bin/heavy python3 $W/tools/d3/l0_exercise.py ablate --binary $CTL \
  --map map-$N-x.json --out ablate-$N.json --workdir abl-$N --jobs 4 --targets "$@"
