;; d3tiny: the small contract the D3 oracle deploys at run time (DeployContract transactions and
;; `promise_batch_action_deploy_contract` from d3rich, whose data segment embeds these bytes).
;; `run` / `cb`: storage_write("t", input), log_utf8("tiny"), value_return(input).
(module
  (import "env" "input" (func $input (param i64)))
  (import "env" "register_len" (func $register_len (param i64) (result i64)))
  (import "env" "read_register" (func $read_register (param i64 i64)))
  (import "env" "storage_write" (func $storage_write (param i64 i64 i64 i64 i64) (result i64)))
  (import "env" "log_utf8" (func $log_utf8 (param i64 i64)))
  (import "env" "value_return" (func $value_return (param i64 i64)))
  (memory 1)
  (data (i32.const 0) "ttiny")
  (func $main (local $n i64)
    (call $input (i64.const 0))
    (local.set $n (call $register_len (i64.const 0)))
    (if (i64.gt_u (local.get $n) (i64.const 60000)) (then (local.set $n (i64.const 60000))))
    (call $read_register (i64.const 0) (i64.const 16))
    (drop (call $storage_write (i64.const 1) (i64.const 0) (local.get $n) (i64.const 16) (i64.const 1)))
    (call $log_utf8 (i64.const 4) (i64.const 1))
    (call $value_return (local.get $n) (i64.const 16)))
  (export "run" (func $main))
  (export "cb" (func $main)))
