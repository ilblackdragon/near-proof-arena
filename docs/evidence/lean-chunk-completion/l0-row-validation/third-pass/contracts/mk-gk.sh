#!/bin/bash
# Gas-key function-call key with a non-UTF-8 method name (0xFF), injected as the `d3float`
# account's code (method `run`).
#  gkret:  the call returns normally after the host call.
#  gkcont: the contract keeps running after the host call (log_utf8, then unreachable).
set -eu
cd /data/illia/nearproof-deps/l0-validate/b4/gk
for v in ret cont; do
  if [ $v = ret ]; then tail='' ; else tail='(call $log (i64.const 5) (i64.const 400)) unreachable'; fi
  cat > gk$v.wat <<EOF
(module
  (import "env" "promise_batch_create" (func \$create (param i64 i64) (result i64)))
  (import "env" "promise_batch_action_add_gas_key_with_function_call" (func \$add_gas_key_fc (param i64 i64 i64 i64 i64 i64 i64 i64 i64)))
  (import "env" "log_utf8" (func \$log (param i64 i64)))
  (memory (export "memory") 1)
  (data (i32.const 32) "s0fl")
  (data (i32.const 256) "\\00\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08\\08")
  (data (i32.const 384) "\\ff")
  (data (i32.const 400) "after")
  (func (export "run") (local \$p i64)
    (local.set \$p (call \$create (i64.const 4) (i64.const 32)))
    (call \$add_gas_key_fc (local.get \$p) (i64.const 33) (i64.const 256) (i64.const 1) (i64.const 608)
                         (i64.const 4) (i64.const 32) (i64.const 1) (i64.const 384))
    $tail))
EOF
  wasm-tools parse gk$v.wat -o gk$v.wasm
  wasm-tools validate gk$v.wasm
done
sha256sum gk*.wasm
