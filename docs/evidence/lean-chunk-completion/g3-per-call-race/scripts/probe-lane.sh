#!/bin/bash
# probe-lane.sh : the regenerated pipeline-race family (forced schedules on every case), both binaries
cd /data/illia/nearproof/.claude/worktrees/agent-a4f67ff469dc3121d
D=/data/illia/nearproof-deps/g3-uncertain
for t in allFeatures signed; do
  for b in base after; do
    python3 tools/d3/replay_successor.py --binary $D/bin/$b --tier $t --cases-file $D/race-probe-family.txt \
      --out $D/rep/$b-raceprobe-$t --jobs 1 --timeout 7200 > $D/rep/$b-raceprobe-$t.log 2>&1
    echo "$b-raceprobe-$t exit $?" >> $D/rep/status
  done
done
