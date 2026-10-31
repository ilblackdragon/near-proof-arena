#!/bin/bash
# lane.sh BIN JOBS : every G3 population through the integrated harness with bin/BIN, both tiers
cd /data/illia/nearproof/.claude/worktrees/agent-a4f67ff469dc3121d
D=/data/illia/nearproof-deps/g3-uncertain
G=/data/illia/nearproof-deps/gateb-freeze-2368b8713
B=$1; J=${2:-4}
mkdir -p $D/rep
rp() {  # rp NAME LIST TIER
  python3 tools/d3/replay_successor.py --binary $D/bin/$B --tier $3 --cases-file $2 --out $D/rep/$B-$1-$3 \
    --jobs $J --timeout 7200 > $D/rep/$B-$1-$3.log 2>&1
  echo "$B-$1-$3 exit $?" >> $D/rep/status
}
for t in allFeatures signed; do
  rp fixtures $G/fixtures-final.txt $t
  rp census $G/census.txt $t
  rp race $D/race-family.txt $t
  rp w08 $D/w08-family.txt $t
  rp ethw /data/illia/nearproof-deps/ethw/all.txt $t
  $D/run.sh $D/bin/$B $t $G/shard13.txt $D/rep/$B-shard13-$t.jsonl $J
  echo "$B-shard13-$t done" >> $D/rep/status
done
for t in allFeatures signed; do
  rp corpus $G/corpus-cases.txt $t
done
echo "$B ALL" >> $D/rep/status
