;; d3ed: imports `ed25519_verify` (inside D3α as the Lean WASM spec models it — `curveHosts`,
;; spec/lean/v3/NearSpecV3/Wasm/Exec.lean — but listed as a D3γ import in
;; docs/requirements/D3_WASM_REQUIREMENTS.md §1.1; the oracle records it as a feature).
;; `run`: input = sig(64) ‖ pk(32) ‖ msg; storage_write("v", verify result); shorter input:
;; a 0-length signature (host error).
(module
  (import "env" "input" (func $input (param i64)))
  (import "env" "register_len" (func $register_len (param i64) (result i64)))
  (import "env" "read_register" (func $read_register (param i64 i64)))
  (import "env" "ed25519_verify" (func $ed25519_verify (param i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "storage_write" (func $storage_write (param i64 i64 i64 i64 i64) (result i64)))
  (memory 1)
  (data (i32.const 0) "v")
  (func $run (local $n i64) (local $sl i64)
    (call $input (i64.const 0))
    (local.set $n (call $register_len (i64.const 0)))
    (if (i64.gt_u (local.get $n) (i64.const 4096)) (then (local.set $n (i64.const 4096))))
    (call $read_register (i64.const 0) (i64.const 1024))
    (local.set $sl (i64.const 64))
    (if (i64.lt_u (local.get $n) (i64.const 96)) (then (local.set $sl (i64.const 0)) (local.set $n (i64.const 96))))
    (i64.store (i32.const 8)
      (call $ed25519_verify (local.get $sl) (i64.const 1024) (i64.sub (local.get $n) (i64.const 96)) (i64.const 1120) (i64.const 32) (i64.const 1088)))
    (drop (call $storage_write (i64.const 1) (i64.const 0) (i64.const 8) (i64.const 8) (i64.const 1))))
  (export "run" (func $run))
  (export "cb" (func $run)))
