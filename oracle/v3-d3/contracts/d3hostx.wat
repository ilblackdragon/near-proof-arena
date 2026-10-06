;; d3hostx: imports the curve host function `ecrecover` and host functions of the state-init,
;; global-contract and gas-key families, and builds VM-created key actions from its input.
;; Importing an excluded host function is in D3α; calling one is not
;; (spec/near-chunk-validation-d3.md §10.0a P3). A VM-created Stake / AddKey / DeleteKey action
;; with an ML-DSA-65 key is out of D3α (P4).
;;   `run`, `cb`: storage_write("x", input), no excluded host function called (in D3α)
;;   `curve`:  ecrecover of a zero hash / signature (returns 0), storage_write("e", result)
;;   `glob`:   promise_batch_create(self) + promise_batch_action_use_global_contract(zero hash)
;;   `stinit`: promise_batch_create(self) + promise_batch_action_state_init(zero hash, amount 0)
;;   `gaskey`: promise_batch_create(self) + promise_batch_action_add_gas_key_with_full_access(
;;             input = borsh public key, 1 nonce)
;;   `mlkey`:  input = op ‖ borsh public key; promise_batch_create(self) + op 0: AddKey (full
;;             access, nonce 0), op 1: Stake (amount 0), op 2: DeleteKey
(module
  (import "env" "input" (func $input (param i64)))
  (import "env" "register_len" (func $register_len (param i64) (result i64)))
  (import "env" "read_register" (func $read_register (param i64 i64)))
  (import "env" "storage_write" (func $storage_write (param i64 i64 i64 i64 i64) (result i64)))
  (import "env" "current_account_id" (func $current_account_id (param i64)))
  (import "env" "promise_batch_create" (func $promise_batch_create (param i64 i64) (result i64)))
  (import "env" "ecrecover" (func $ecrecover (param i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_batch_action_use_global_contract" (func $use_global (param i64 i64 i64)))
  (import "env" "promise_batch_action_state_init" (func $state_init (param i64 i64 i64 i64) (result i64)))
  (import "env" "promise_batch_action_add_gas_key_with_full_access" (func $add_gas_key (param i64 i64 i64 i64)))
  (import "env" "promise_batch_action_add_key_with_full_access" (func $add_key (param i64 i64 i64 i64)))
  (import "env" "promise_batch_action_stake" (func $stake (param i64 i64 i64 i64)))
  (import "env" "promise_batch_action_delete_key" (func $delete_key (param i64 i64 i64)))
  (memory 1)
  ;; 0: "x", 1: "e"; 100..132: zero hash; 200..216: zero amount; 300..: own account id;
  ;; 1024..: input
  (data (i32.const 0) "xe")
  ;; input into 1024.., returns its length (at most 8192)
  (func $read_input (result i64) (local $n i64)
    (call $input (i64.const 0))
    (local.set $n (call $register_len (i64.const 0)))
    (if (i64.gt_u (local.get $n) (i64.const 8192)) (then (local.set $n (i64.const 8192))))
    (call $read_register (i64.const 0) (i64.const 1024))
    (local.get $n))
  ;; promise_batch_create(current account)
  (func $self_batch (result i64)
    (call $current_account_id (i64.const 1))
    (call $read_register (i64.const 1) (i64.const 300))
    (call $promise_batch_create (call $register_len (i64.const 1)) (i64.const 300)))
  (func $run (local $n i64)
    (local.set $n (call $read_input))
    (drop (call $storage_write (i64.const 1) (i64.const 0) (local.get $n) (i64.const 1024) (i64.const 2))))
  (func $curve
    (i64.store (i32.const 8)
      (call $ecrecover (i64.const 32) (i64.const 100) (i64.const 64) (i64.const 100) (i64.const 0) (i64.const 0) (i64.const 3)))
    (drop (call $storage_write (i64.const 1) (i64.const 1) (i64.const 8) (i64.const 8) (i64.const 2))))
  (func $glob
    (call $use_global (call $self_batch) (i64.const 32) (i64.const 100)))
  (func $stinit
    (drop (call $state_init (call $self_batch) (i64.const 32) (i64.const 100) (i64.const 200))))
  (func $gaskey (local $n i64)
    (local.set $n (call $read_input))
    (call $add_gas_key (call $self_batch) (local.get $n) (i64.const 1024) (i64.const 1)))
  (func $mlkey (local $n i64) (local $p i64) (local $op i32)
    (local.set $n (call $read_input))
    (local.set $op (i32.load8_u (i32.const 1024)))
    (local.set $p (call $self_batch))
    (if (i32.eq (local.get $op) (i32.const 0))
      (then (call $add_key (local.get $p) (i64.sub (local.get $n) (i64.const 1)) (i64.const 1025) (i64.const 0))))
    (if (i32.eq (local.get $op) (i32.const 1))
      (then (call $stake (local.get $p) (i64.const 200) (i64.sub (local.get $n) (i64.const 1)) (i64.const 1025))))
    (if (i32.ge_u (local.get $op) (i32.const 2))
      (then (call $delete_key (local.get $p) (i64.sub (local.get $n) (i64.const 1)) (i64.const 1025)))))
  (export "run" (func $run))
  (export "cb" (func $run))
  (export "curve" (func $curve))
  (export "glob" (func $glob))
  (export "stinit" (func $stinit))
  (export "gaskey" (func $gaskey))
  (export "mlkey" (func $mlkey)))
