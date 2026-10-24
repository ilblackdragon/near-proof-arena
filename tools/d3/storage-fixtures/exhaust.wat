(module
  (import "env" "storage_remove" (func $remove (param i64 i64 i64) (result i64)))
  (memory (export "memory") 1)
  (func (export "run") (local $i i32)
    (loop $again
      (drop (call $remove (i64.const 1) (i64.const 0) (i64.const 0)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if $again (i32.lt_u (local.get $i) (i32.const 2001))))))
