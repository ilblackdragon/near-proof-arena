import Conformance.Sha

/-!
`np-lean-shatrace <out.bin> <len>...` — dump the honest SHA-256 table trace
`ZkFormal.Sha.Gen.honestCell (toyMsgs lens)` (lane L5) for cross-checking the
Rust generator (src/sha.rs).

Output (little-endian u32): `width, log, nrows`, then `2^log · width` cells,
row-major (padding rows included).
-/

open Conformance.Sha ZkFormal.Sha.Gen

def putU32 (b : ByteArray) (x : Nat) : ByteArray :=
  (b.push (x % 256).toUInt8).push ((x / 256) % 256).toUInt8
    |>.push ((x / 65536) % 256).toUInt8 |>.push ((x / 16777216) % 256).toUInt8

def main (args : List String) : IO UInt32 := do
  match args with
  | out :: lens =>
    let some lens := lens.mapM String.toNat? | IO.eprintln "lengths must be naturals"; return 2
    let msgs := toyMsgs lens
    let rows := (honestRows msgs).toArray
    let log := honestLog msgs
    let w := ZkFormal.Sha.Layout.width
    let mut b := ByteArray.emptyWithCapacity (4 * (3 + 2 ^ log * w))
    b := putU32 (putU32 (putU32 b w) log) rows.size
    for r in [0:2 ^ log] do
      let row := rows.getD r .pad
      for c in [0:w] do
        b := putU32 b (rowCell row c)
    IO.FS.writeBinFile out b
    IO.eprintln s!"rows {rows.size} log {log}"
    return 0
  | _ => IO.eprintln "usage: np-lean-shatrace <out.bin> <len>..."; return 2
