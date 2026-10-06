;; d3curve: outside D3α (imports the curve host function `ecrecover`). `run`: ecrecover of a
;; zero hash / signature (recovery fails: returns 0), storage_write("e", result).
(module
  (import "env" "ecrecover" (func $ecrecover (param i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "storage_write" (func $storage_write (param i64 i64 i64 i64 i64) (result i64)))
  (memory 1)
  (data (i32.const 0) "e")
  (func $run
    (i64.store (i32.const 8) (call $ecrecover (i64.const 32) (i64.const 64) (i64.const 64) (i64.const 128) (i64.const 0) (i64.const 0) (i64.const 1)))
    (drop (call $storage_write (i64.const 1) (i64.const 0) (i64.const 8) (i64.const 8) (i64.const 1))))
  (export "run" (func $run))
  (export "cb" (func $run)))
