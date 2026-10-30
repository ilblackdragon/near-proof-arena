;; hostrows: calls the host functions no other fixture calls (`host-rows` scenario, src/xfam.rs).
;; Input is loaded at 1024; output is built at 2048. Methods:
;;   `ccc`   r := current_contract_code(1); value := [r] ‖ register 1 (if r ≠ 0); storage "c"
;;   `rta`   refund_to_account_id(1); value := register 1; storage "r"
;;   `psr`   input [mode][tlen][target][rlen][refund]: p := promise_batch_create(target), then
;;           mode 1: function_call(p, "rta", 1000 yocto, 5 Tgas), otherwise transfer(p, 1000 yocto);
;;           mode 2: p := 7 (no such promise); mode 3: p := promise_and(p, a second transfer batch);
;;           then promise_set_refund_to(p, refund); storage "p" := refund
;;   `itp` / `itr` / `itn`  storage "i" := "i", then storage_iter_prefix / _range / _next
;;   `itok`  storage "i" := "i" only
;;   `gas`   input u32 LE k: gas(k) (the `env.gas` import, i32 parameter), then storage "g" := k
(module
  (import "env" "input" (func $input (param i64)))
  (import "env" "register_len" (func $rl (param i64) (result i64)))
  (import "env" "read_register" (func $rr (param i64 i64)))
  (import "env" "value_return" (func $vr (param i64 i64)))
  (import "env" "storage_write" (func $sw (param i64 i64 i64 i64 i64) (result i64)))
  (import "env" "current_contract_code" (func $ccc (param i64) (result i64)))
  (import "env" "refund_to_account_id" (func $rta (param i64)))
  (import "env" "promise_batch_create" (func $pbc (param i64 i64) (result i64)))
  (import "env" "promise_batch_action_transfer" (func $ptr (param i64 i64)))
  (import "env" "promise_batch_action_function_call" (func $pfc (param i64 i64 i64 i64 i64 i64 i64)))
  (import "env" "promise_and" (func $pand (param i64 i64) (result i64)))
  (import "env" "promise_set_refund_to" (func $psr (param i64 i64 i64)))
  (import "env" "storage_iter_prefix" (func $itp (param i64 i64) (result i64)))
  (import "env" "storage_iter_range" (func $itr (param i64 i64 i64 i64) (result i64)))
  (import "env" "storage_iter_next" (func $itn (param i64 i64 i64) (result i64)))
  (import "env" "gas" (func $gas (param i32)))
  (memory 1)
  ;; 0: keys "crigp"; 16: 1000 yocto (u128 LE); 32: "rta"
  (data (i32.const 0) "crigp")
  (data (i32.const 16) "\e8\03")
  (data (i32.const 32) "rta")
  (func $load (result i64) (local $n i64)
    (call $input (i64.const 0))
    (local.set $n (call $rl (i64.const 0)))
    (if (i64.gt_u (local.get $n) (i64.const 1000)) (then (local.set $n (i64.const 1000))))
    (call $rr (i64.const 0) (i64.const 1024))
    (local.get $n))
  (func (export "ccc") (local $r i64) (local $n i64)
    (local.set $r (call $ccc (i64.const 1)))
    (i32.store8 (i32.const 2048) (i32.wrap_i64 (local.get $r)))
    (if (i64.ne (local.get $r) (i64.const 0)) (then
      (local.set $n (call $rl (i64.const 1)))
      (call $rr (i64.const 1) (i64.const 2049))))
    (drop (call $sw (i64.const 1) (i64.const 0) (i64.add (local.get $n) (i64.const 1)) (i64.const 2048) (i64.const 3)))
    (call $vr (i64.add (local.get $n) (i64.const 1)) (i64.const 2048)))
  (func (export "rta") (local $n i64)
    (call $rta (i64.const 1))
    (local.set $n (call $rl (i64.const 1)))
    (call $rr (i64.const 1) (i64.const 2048))
    (drop (call $sw (i64.const 1) (i64.const 1) (local.get $n) (i64.const 2048) (i64.const 3)))
    (call $vr (local.get $n) (i64.const 2048)))
  (func (export "psr") (local $mode i32) (local $tl i64) (local $rlen i64) (local $rp i64) (local $p i64) (local $q i64)
    (drop (call $load))
    (local.set $mode (i32.load8_u (i32.const 1024)))
    (local.set $tl (i64.extend_i32_u (i32.load8_u (i32.const 1025))))
    ;; refund length at 1026 + tl, refund bytes from 1027 + tl
    (local.set $rp (i64.add (i64.const 1027) (local.get $tl)))
    (local.set $rlen (i64.extend_i32_u (i32.load8_u (i32.wrap_i64 (i64.sub (local.get $rp) (i64.const 1))))))
    (local.set $p (call $pbc (local.get $tl) (i64.const 1026)))
    (if (i32.eq (local.get $mode) (i32.const 1))
      (then (call $pfc (local.get $p) (i64.const 3) (i64.const 32) (i64.const 0) (i64.const 0) (i64.const 16) (i64.const 5000000000000)))
      (else (call $ptr (local.get $p) (i64.const 16))))
    (if (i32.eq (local.get $mode) (i32.const 2)) (then (local.set $p (i64.const 7))))
    (if (i32.eq (local.get $mode) (i32.const 3)) (then
      (local.set $q (call $pbc (local.get $tl) (i64.const 1026)))
      (call $ptr (local.get $q) (i64.const 16))
      (i64.store (i32.const 3072) (local.get $p))
      (i64.store (i32.const 3080) (local.get $q))
      (local.set $p (call $pand (i64.const 3072) (i64.const 2)))))
    (call $psr (local.get $p) (local.get $rlen) (local.get $rp))
    (drop (call $sw (i64.const 1) (i64.const 4) (local.get $rlen) (local.get $rp) (i64.const 3))))
  (func $mark (drop (call $sw (i64.const 1) (i64.const 2) (i64.const 1) (i64.const 2) (i64.const 3))))
  (func (export "itp") (call $mark) (drop (call $itp (i64.const 1) (i64.const 0))))
  (func (export "itr") (call $mark) (drop (call $itr (i64.const 1) (i64.const 0) (i64.const 1) (i64.const 1))))
  (func (export "itn") (call $mark) (drop (call $itn (i64.const 0) (i64.const 1) (i64.const 2))))
  (func (export "itok") (call $mark))
  (func (export "gas")
    (drop (call $load))
    (call $gas (i32.load (i32.const 1024)))
    (drop (call $sw (i64.const 1) (i64.const 3) (i64.const 4) (i64.const 1024) (i64.const 3)))))
