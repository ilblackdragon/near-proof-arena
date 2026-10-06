;; d3float: outside D3α (float opcodes and an f64 local). `run`: storage_write("f", i64 of
;; trunc(sqrt(len(input)) * 1.5)).
(module
  (import "env" "input" (func $input (param i64)))
  (import "env" "register_len" (func $register_len (param i64) (result i64)))
  (import "env" "storage_write" (func $storage_write (param i64 i64 i64 i64 i64) (result i64)))
  (memory 1)
  (data (i32.const 0) "f")
  (func $run (local $x f64)
    (call $input (i64.const 0))
    (local.set $x (f64.mul (f64.sqrt (f64.convert_i64_u (call $register_len (i64.const 0)))) (f64.const 1.5)))
    (i64.store (i32.const 8) (i64.trunc_f64_u (local.get $x)))
    (drop (call $storage_write (i64.const 1) (i64.const 0) (i64.const 8) (i64.const 8) (i64.const 1))))
  (export "run" (func $run))
  (export "cb" (func $run)))
