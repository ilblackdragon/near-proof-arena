(module
  (import "env" "storage_remove" (func $remove (param i64 i64 i64) (result i64)))
  (memory (export "memory") 1)
  (func (export "run")
    (drop (call $remove (i64.const 1) (i64.const 0) (i64.const 0))))
)
