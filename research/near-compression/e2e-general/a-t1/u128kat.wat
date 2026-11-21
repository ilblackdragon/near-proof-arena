;; A-T1 write-coverage KAT: the `setU128H` hosts write 16 bytes of linear memory.
;; Memory at 96..175 is first filled with 0xAB so every written byte differs from the old one,
;; then account_balance(96), attached_deposit(112), account_locked_balance(128),
;; validator_total_stake(144) write u128 values, and the call returns a sum of loads of the
;; written bytes (so the Wasm run observes the writes).
(module
  (import "env" "account_balance" (func $bal (param i64)))
  (import "env" "attached_deposit" (func $dep (param i64)))
  (import "env" "account_locked_balance" (func $lck (param i64)))
  (import "env" "validator_total_stake" (func $vts (param i64)))
  (memory 1)
  (func (export "run") (result i64) (local i32)
    ;; fill 96..175 with 0xAB
    i32.const 96
    local.set 0
    (block $done
      (loop $l
        local.get 0
        i32.const 176
        i32.ge_u
        br_if $done
        local.get 0
        i64.const 0xabababababababab
        i64.store
        local.get 0
        i32.const 8
        i32.add
        local.set 0
        br $l))
    i64.const 96
    call $bal
    i64.const 112
    call $dep
    i64.const 128
    call $lck
    i64.const 144
    call $vts
    i32.const 96
    i64.load
    i32.const 104
    i64.load
    i64.add
    i32.const 112
    i64.load
    i64.add
    i32.const 128
    i64.load8_u
    i64.add
    i32.const 152
    i64.load
    i64.add))
