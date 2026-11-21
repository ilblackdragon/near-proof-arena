#!/usr/bin/env bash
# lane I's M10 driver (t1/run_t1.sh) at lane A's head, with lane A's fresh Lean tool and prover
. /data/illia/nearproof-deps/e2e-laneA/at1/env.sh
export NOBUILD=1 PROVE=1 STEPS=${STEPS:-13}
export WASMBASE_TOOL=$T WB_PROVER=$B
OUT=/data/illia/nearproof-deps/e2e-laneA/at1/t1-harness-k$STEPS
rm -rf $OUT
bash $W/e2e-general/t1/run_t1.sh $OUT > $OUT.log 2>&1
echo rc=$?
tail -40 $OUT.log
