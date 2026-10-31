#!/bin/bash
# gen.sh SEED... : regenerate the pipeline-race family with the forced eager/lazy schedules on every case
D=/data/illia/nearproof-deps/g3-uncertain
B=$D/oracle-target/release/near-arena-oracle-v3-successor
mkdir -p $D/probe
cd $D/probe
for S in "$@"; do
  NEAR_SUCCESSOR_SCENARIO=pipeline-race NEAR_SCHEDULE_PROBE_ALL=1 $B gen --domain d3 --seed $S --chains 1 \
    --blocks 110 --mutate-every 0 --code-mutant-p 0.3 --ood-cap 2000 --out race$S > race$S.log 2>&1
  echo "race$S exit $?" >> $D/probe/status
done
