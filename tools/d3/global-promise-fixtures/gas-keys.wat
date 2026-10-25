(module
  (import "env" "promise_batch_create" (func $create (param i64 i64) (result i64)))
  (import "env" "promise_batch_action_transfer" (func $transfer (param i64 i64)))
  (import "env" "promise_batch_action_transfer_to_gas_key" (func $to_gas_key (param i64 i64 i64 i64)))
  (import "env" "promise_batch_action_add_gas_key_with_full_access" (func $add_gas_key_full (param i64 i64 i64 i64)))
  (import "env" "promise_batch_action_add_gas_key_with_function_call" (func $add_gas_key_fc (param i64 i64 i64 i64 i64 i64 i64 i64 i64)))
  (memory (export "memory") 1)
  ;; Receiver account IDs are the deterministic 42-byte IDs used by all-hosts-valid-receivers.wat.
  (data (i32.const 32) "0s4694c9c78c0e8c83afcf016f076b350a973f1964")
  (data (i32.const 128) "0s2546cf13f32c0dd47de558354e62a6f142b979b9")
  ;; 33-byte ED25519 PublicKeyBuffers in free memory: tag 0 + 32 bytes.
  (data (i32.const 256) "\00\07\07\07\07\07\07\07\07\07\07\07\07\07\07\07\07\07\07\07\07\07\07\07\07\07\07\07\07\07\07\07\07")
  (data (i32.const 320) "\00\08\08\08\08\08\08\08\08\08\08\08\08\08\08\08\08\08\08\08\08\08\08\08\08\08\08\08\08\08\08\08\08")
  (data (i32.const 384) "f,g,m")
  ;; u128 little-endian amounts read by the promise hosts: 16 and 32 yoctoNEAR.
  (data (i32.const 416) "\10\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  (data (i32.const 432) "\20\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
  ;; Allowance stays zero, so the function-call permission encodes `None` (`logic/logic.rs:3145`).
  (func (export "run") (export "main") (export "cb") (local $a i64) (local $b i64)
    ;; Two receipts: transfer first (so ordinal assertions have something to count), then one action
    ;; from each gas-key host.
    (local.set $a (call $create (i64.const 42) (i64.const 32)))
    (call $transfer (local.get $a) (i64.const 416))
    (local.set $b (call $create (i64.const 42) (i64.const 128)))
    (call $transfer (local.get $b) (i64.const 416))
    ;; Receipt a: fund a gas key (tag 12) and add a full-access gas key (tag 5, permission tag 3).
    (call $to_gas_key (local.get $a) (i64.const 33) (i64.const 256) (i64.const 416))
    (call $add_gas_key_full (local.get $a) (i64.const 33) (i64.const 320) (i64.const 4))
    ;; Receipt b: add a function-call gas key (tag 5, permission tag 2) with zero allowance.
    (call $add_gas_key_fc (local.get $b) (i64.const 33) (i64.const 320) (i64.const 2) (i64.const 608)
                         (i64.const 42) (i64.const 32) (i64.const 5) (i64.const 384))))
