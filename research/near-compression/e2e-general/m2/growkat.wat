(module
  (memory 1)
  (func (export "run") (result i64) (local i32 i64)
    ;; memory.size = 1
    memory.size
    local.set 0
    ;; grow by 2 pages: returns the old size 1
    i32.const 2
    memory.grow
    local.get 0
    i32.add
    local.set 0
    ;; write into the grown pages and read back
    i32.const 67108872
    i64.const 0x0123456789abcdef
    i64.store
    i32.const 67239934
    i32.const 0x7f
    i32.store8
    i32.const 67108872
    i64.load
    i32.const 67239934
    i64.load8_u
    i64.add
    ;; a zero byte of a grown page that was never written
    i32.const 67208864
    i64.load16_u
    i64.add
    local.set 1
    ;; a failing grow (beyond 2048 pages) returns -1
    i32.const 5000
    memory.grow
    local.get 0
    i32.add
    memory.size
    i32.add
    i64.extend_i32_u
    local.get 1
    i64.add))
