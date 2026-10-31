#!/bin/bash
# Contracts for the W-005 / W-006 rows (replace d3float via NEAR_SUCCESSOR_CONTRACT; method `run`).
set -eu
cd /data/illia/nearproof-deps/l0-validate/b4
cp /data/illia/nearproof-deps/l0-validate/hr/oracle ./oracle
sha256sum oracle > oracle.sha256
locs=$(python3 -c "print(' '.join(['i32']*49999))")
printf '(module\n  (func (export "run")\n    (local %s)\n    nop))\n' "$locs" > w006.wat
printf '(module\n  (import "env" "memory" (memory 1))\n  (func (export "run")))\n' > w005.wat
wasm-tools parse w006.wat -o w006.wasm
wasm-tools parse w005.wat -o w005.wasm
wasm-tools validate w006.wasm
wasm-tools validate w005.wasm
ls -la *.wasm
sha256sum *.wasm
