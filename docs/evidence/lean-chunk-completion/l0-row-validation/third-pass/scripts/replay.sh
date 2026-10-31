#!/bin/bash
# Usage: replay.sh NAME RUNDIR...  -> NAME.txt (case list), NAME-default/ (default checker replay),
# trace-NAME.jsonl (ctl-v3 trace), identity check, map-NAME.json
set -u
cd /data/illia/nearproof-deps/l0-validate/b4
W=/data/illia/nearproof/.claude/worktrees/agent-a8b3a000da794c665
FREEZE=/data/illia/nearproof-deps/gateb-freeze-2368b8713/checker
CTL=/data/illia/nearproof-deps/l0-validate/tree-g/spec/lean/v3/.lake/build/bin/nearspec-v3-ctl-successor
N=$1; shift
find "$@" -name meta.json -printf '%h\n' | sort > $N.txt
wc -l $N.txt
HEAVY_MEM=32G /data/illia/nearproof-deps/bin/heavy python3 $W/tools/d3/replay_successor.py --binary $FREEZE --tier allFeatures \
  --cases-file $N.txt --out $N-default --jobs 4 > $N-default.log 2>&1
echo "default rc=$?"; tail -3 $N-default.log
HEAVY_MEM=32G /data/illia/nearproof-deps/bin/heavy python3 $W/tools/d3/l0_exercise.py trace --binary $CTL --cases-file $N.txt \
  --out trace-$N.jsonl --jobs 4 > trace-$N.log 2>&1
echo "trace rc=$?"
python3 $W/tools/d3/l0_exercise.py identity --trace trace-$N.jsonl --reference $N-default/results.jsonl
python3 $W/tools/d3/l0_exercise.py map --trace trace-$N.jsonl --out map-$N.json | grep -v "^host:\|^act:" | head -60
