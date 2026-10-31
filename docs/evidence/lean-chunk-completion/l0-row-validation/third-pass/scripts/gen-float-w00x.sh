#!/bin/bash
# Cold-judged whole-chunk fixtures with full mutant sets for the float / W-005 / W-006 rows.
# The versioned generator replaces the `d3float` account's code with NEAR_SUCCESSOR_CONTRACT and
# calls its `run` method (oracle/v3-successor/src/d3gen.rs, d3contracts.rs). Same configuration as
# docs/evidence/lean-chunk-completion/float-input-mutants-350/generation.json (seed 17, 1 chain,
# 12 blocks, every case mutated).
set -u
cd /data/illia/nearproof-deps/l0-validate/b4
run() { # name contract
  rm -rf run-$1
  NEAR_SUCCESSOR_SCENARIO=${SCEN:-} NEAR_SUCCESSOR_CONTRACT=$2 HEAVY_MEM=24G /data/illia/nearproof-deps/bin/heavy ./oracle gen --domain d3 \
    --seed 17 --chains 1 --blocks 12 --mutate-every 1 --code-mutant-p 1 --out run-$1 > gen-$1.log 2>&1
  echo "$1 rc=$? $(tail -1 gen-$1.log)"
}
#run float floatc/float-17-success.wasm &
SCEN=runtime-errors run w005 w005.wasm &
SCEN=runtime-errors run w006 w006.wasm &
wait
