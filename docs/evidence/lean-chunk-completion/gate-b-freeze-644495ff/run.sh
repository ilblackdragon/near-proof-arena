#!/bin/bash
cd /data/illia/nearproof
G=/data/illia/nearproof-deps/gateb-freeze-ca08fdf37
rp() { python3 tools/d3/replay_successor.py --binary $G/checker --tier $1 --cases-file $G/$2.txt --out $G/$2-$1 --jobs $3 --timeout 7200 > $G/$2-$1.log 2>&1; echo "$2-$1 exit $?" >> $G/status; }
for t in allFeatures signed; do rp $t fixtures-final 8; rp $t census 8; done
for t in allFeatures signed; do xargs -P 8 -n 20 $G/checker --tier $t < $G/shard13.txt > $G/shard13-$t.jsonl 2>/dev/null; echo "shard13-$t done" >> $G/status; done
for t in allFeatures signed; do rp $t corpus-cases 10; done
echo ALL >> $G/status
