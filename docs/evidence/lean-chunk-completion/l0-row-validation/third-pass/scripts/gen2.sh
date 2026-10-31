#!/bin/bash
# Third-pass generator runs (oracle-l0: this worktree's generator, src/l0mut.rs + the relaxed
# precompile assertion for an injected contract). Each run: the `d3float` account's code replaced
# by a contract that fails preparation (w005) / Wasmtime compilation (w006), full mutant set on
# every case, plus the opt-in L0 witness+claim mutants (NEAR_L0_ROW_MUTANTS=1).
set -u
cd /data/illia/nearproof-deps/l0-validate/b4
run() { # name contract seed
  rm -rf run2-$1
  NEAR_L0_ROW_MUTANTS=1 NEAR_SUCCESSOR_CONTRACT=$2 HEAVY_MEM=24G /data/illia/nearproof-deps/bin/heavy ./oracle-l0 gen \
    --domain d3 --seed $3 --chains 1 --blocks 16 --p-missing 0.3 --mutate-every 1 --code-mutant-p 1 \
    --out run2-$1 > gen2-$1.log 2>&1
  echo "$1 rc=$? $(tail -1 gen2-$1.log)"
}
run w005 w005.wasm 17 &
run w006 w006.wasm 18 &
wait
