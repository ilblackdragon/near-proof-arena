;; Storage-heavy contract for the trie-accounting experiment (d3-ttn).
;; `run` interprets its input as 3-byte ops [op, k, c]:
;;   key   = "k" ++ [k] (2 bytes) or "k" ++ [k, 0x55] (3 bytes) when (c / 3) is odd
;;   vlen  = 1, 100 or 4500 for c % 3 = 0, 1, 2 (4500 > 4000: not inlined in flat
;;           storage / large-read overhead path)
;;   op%4  = 0 storage_write, 1 storage_read, 2 storage_has_key, 3 storage_remove
(module
  (import "env" "input" (func $input (param i64)))
  (import "env" "register_len" (func $register_len (param i64) (result i64)))
  (import "env" "read_register" (func $read_register (param i64 i64)))
  (import "env" "storage_write" (func $storage_write (param i64 i64 i64 i64 i64) (result i64)))
  (import "env" "storage_read" (func $storage_read (param i64 i64 i64) (result i64)))
  (import "env" "storage_has_key" (func $storage_has_key (param i64 i64) (result i64)))
  (import "env" "storage_remove" (func $storage_remove (param i64 i64 i64) (result i64)))
  (memory 1)
  (func (export "run")
    (local $n i32) (local $i i32) (local $op i32) (local $k i32) (local $c i32)
    (local $klen i64) (local $vlen i64)
    (call $input (i64.const 0))
    (local.set $n (i32.wrap_i64 (call $register_len (i64.const 0))))
    (if (i32.gt_u (local.get $n) (i32.const 2048)) (then (local.set $n (i32.const 2048))))
    (call $read_register (i64.const 0) (i64.const 0))
    (block $done
      (loop $next
        (br_if $done (i32.gt_u (i32.add (local.get $i) (i32.const 3)) (local.get $n)))
        (local.set $op (i32.load8_u (local.get $i)))
        (local.set $k (i32.load8_u (i32.add (local.get $i) (i32.const 1))))
        (local.set $c (i32.load8_u (i32.add (local.get $i) (i32.const 2))))
        (i32.store8 (i32.const 4096) (i32.const 107))
        (i32.store8 (i32.const 4097) (local.get $k))
        (i32.store8 (i32.const 4098) (i32.const 85))
        (local.set $klen
          (if (result i64) (i32.and (i32.div_u (local.get $c) (i32.const 3)) (i32.const 1))
            (then (i64.const 3)) (else (i64.const 2))))
        (local.set $vlen
          (if (result i64) (i32.eqz (i32.rem_u (local.get $c) (i32.const 3)))
            (then (i64.const 1))
            (else (if (result i64) (i32.eq (i32.rem_u (local.get $c) (i32.const 3)) (i32.const 1))
              (then (i64.const 100)) (else (i64.const 4500))))))
        ;; vary the value: first byte = op index
        (i32.store8 (i32.const 8192) (local.get $i))
        (block $sw
          (if (i32.eqz (i32.and (local.get $op) (i32.const 3)))
            (then (drop (call $storage_write (local.get $klen) (i64.const 4096)
                    (local.get $vlen) (i64.const 8192) (i64.const 1))) (br $sw)))
          (if (i32.eq (i32.and (local.get $op) (i32.const 3)) (i32.const 1))
            (then (drop (call $storage_read (local.get $klen) (i64.const 4096) (i64.const 1))) (br $sw)))
          (if (i32.eq (i32.and (local.get $op) (i32.const 3)) (i32.const 2))
            (then (drop (call $storage_has_key (local.get $klen) (i64.const 4096))) (br $sw)))
          (drop (call $storage_remove (local.get $klen) (i64.const 4096) (i64.const 1))))
        (local.set $i (i32.add (local.get $i) (i32.const 3)))
        (br $next)))))
