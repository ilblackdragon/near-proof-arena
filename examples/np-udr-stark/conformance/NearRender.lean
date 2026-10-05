import ZkFormal.Near.Render.Trace
import ZkFormal.Near.Spec.Prune
import NearSpec.Codec

/-!
`np-lean-render <request.bin> <witness.bin> <out.bin>` — decode the inputs with
NearSpec's decoders (`Codec.decodeRequest`, `decodeWitness`, `buildWitness`),
derive the claim (`Codec.deriveClaim`), compute `extOf` and `Render.bundle`, and
dump (format `np-near-render-v1`, all integers u32 LE):

```
claim_len, claim bytes (c.encode)
nmsgs, then per SHA message (node, acct, mrk, rcpt order): id, len, bytes
ntables (= 6: node walk rcpt acct mrk sort), then per table:
  width, nrows, nrows·width cells row-major (`row.getD col 0`)
```

Compared byte for byte with `npudr nearrender` (examples/np-udr-stark/source).
-/

open NearSpec NearSpec.TransferV1 NearSpec.Codec ZkFormal.Near ZkFormal.Near.Render

def putU32 (b : ByteArray) (x : Nat) : ByteArray :=
  ((b.push (UInt8.ofNat (x % 256))).push (UInt8.ofNat (x / 256 % 256))).push
    (UInt8.ofNat (x / 65536 % 256)) |>.push (UInt8.ofNat (x / 16777216 % 256))

def main (args : List String) : IO UInt32 := do
  match args with
  | [rq, wt, out] =>
    let t0 ← IO.monoMsNow
    let req ← IO.FS.readBinFile rq
    let wit ← IO.FS.readBinFile wt
    match decodeRequest req.toList with
    | .error e => IO.eprintln s!"np-lean-render: request: {e}"; return 2
    | .ok r =>
    match decodeWitness wit.toList with
    | .error e => IO.eprintln s!"np-lean-render: witness: {e}"; return 2
    | .ok (_, vals) =>
    let w := buildWitness r vals
    match deriveClaim r w with
    | .error e => IO.eprintln s!"np-lean-render: {e}"; return 2
    | .ok c =>
    let e := extOf c w
    let B := bundle c e
    if !B.errors.isEmpty then IO.eprintln s!"np-lean-render: walk errors {B.errors}"
    let mut b := ByteArray.empty
    let cb := c.encode
    b := putU32 b cb.length
    for x in cb do b := b.push x
    b := putU32 b B.msgs.length
    for m in B.msgs do
      b := putU32 b m.id
      b := putU32 b m.bytes.length
      for x in m.bytes do b := b.push (UInt8.ofNat x)
    let tabs := B.tables
    b := putU32 b tabs.length
    for (_, T, rows) in tabs do
      b := putU32 b T.width
      b := putU32 b rows.size
      for row in rows do
        for col in List.range T.width do b := putU32 b (row.getD col 0)
    IO.FS.writeBinFile out b
    let t1 ← IO.monoMsNow
    IO.eprintln s!"np-lean-render: {e.ns.length} nodes, {e.rs.length} receipts, {B.msgs.length} msgs, rows {tabs.map (·.2.2.size)}, {t1 - t0} ms"
    return 0
  | _ => IO.eprintln "usage: np-lean-render <request.bin> <witness.bin> <out.bin>"; return 2
