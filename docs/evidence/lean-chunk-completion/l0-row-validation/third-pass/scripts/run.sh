#!/bin/bash
# Usage: run.sh CHECKER TAG JOBS "LIST:TIER ..."  -> TAG-LIST-TIER/ (replay_successor reports)
set -u
cd /data/illia/nearproof-deps/l0-validate/b4/ba
W=/data/illia/nearproof/.claude/worktrees/agent-a8b3a000da794c665
B=$1; T=$2; J=$3; shift 3
for lt in $@; do
  l=${lt%%:*}; t=${lt##*:}
  HEAVY_MEM=32G /data/illia/nearproof-deps/bin/heavy python3 $W/tools/d3/replay_successor.py --binary $B --tier $t \
    --cases-file $l.txt --out $T-$l-$t --jobs $J --timeout 7200 > $T-$l-$t.log 2>&1
  echo "$T-$l-$t exit $? $(tail -1 $T-$l-$t.log | cut -c1-300)"
done
