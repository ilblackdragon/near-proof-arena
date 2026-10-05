import ZkFormal.Near.Render.Trace
import ZkFormal.Near.Spec.Prune
import NearSpec.Codec

/-!
`np-lean-render <request.bin> <witness.bin> <out.bin>` — decode the inputs with
NearSpec's decoders (`Codec.decodeRequest`, `decodeWitness`, `buildWitness`),
derive the claim (`Codec.deriveClaim`), compute `extOf` and `Render.bundle` (inlined:
above `walkNormMax` walk steps the walk table is `walkRowsFast`, since the normative
`walkRowsAll` is cubic in the step count; below it both are computed and compared), and
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

/-- `usesL st` computed in one pass (equal by definition: the number of earlier
steps with the same edge); `usesL` is cubic (`st.getD j` inside the filter). -/
def usesFast (st : List (Nat × WStep)) : List Nat :=
  (st.foldl (fun (acc : Std.HashMap Edge Nat × Array Nat) p =>
     let c := acc.1.getD p.2.edge 0
     (acc.1.insert p.2.edge (c + 1), acc.2.push c)) ({}, #[])).2.toList

/-- `walkRowsAll` with `usesFast` and array indexing (same cells, `walkCell`). -/
def walkRowsFast (ws : List (List WStep)) : Array Row :=
  let st := (walkSteps ws).toArray
  let us := (usesFast st.toList).toArray
  mkTab (2 ^ logOf st.size) WalkTab.width fun q col =>
    if q < st.size then walkCell (st.getD q default) (us.getD q 0) col else 0

/-- Normative `walkRowsAll` is used up to this many walk steps (and compared
with `walkRowsFast`); above it only `walkRowsFast`. -/
def walkNormMax : Nat := 3000

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
    if (← IO.getEnv "NEAR_RENDER_TIMING").isSome then
      -- per-generator timings (each forced separately)
      let I := mkInfo c e
      let err ← IO.getStderr
      let tick (nm : String) (f : Unit → Nat) : IO Unit := do
        let a ← IO.monoMsNow
        let n := f ()
        err.putStrLn s!"  {nm}: {n}, {(← IO.monoMsNow) - a} ms"
        err.flush
      tick "info" fun _ => I.pre.size + I.post.size
      let ws := walksOf I
      tick "walks" fun _ => ws.length
      let uses := edgeUses ws
      tick "node" fun _ => (nodeRowsAll I uses).size
      tick "walkFast" fun _ => (walkRowsFast ws).size
      tick "acct" fun _ => (acctRowsAll I).size
      tick "mrk" fun _ => (mrkRowsAll I).size
      tick "sort" fun _ => (sortRowsAll I).size
      tick "msgs" fun _ => (nodeMsgs I ++ acctMsgs I ++ mrkMsgs I).length
      tick "rcptMsgs" fun _ => (rcptMsgs I).length
      tick "rcpt" fun _ => (rcptRowsAll I).size
    -- `Render.bundle c e`, inlined, except that the walk table of a batch
    -- with more than `walkNormMax` walk steps is `walkRowsFast`
    let I := mkInfo c e
    let ws := walksOf I
    let uses := edgeUses ws
    let nsteps := (walkSteps ws).length
    let wf := walkRowsFast ws
    let walk ← if nsteps ≤ walkNormMax then do
        let wn := walkRowsAll ws
        if wn != wf then IO.eprintln "np-lean-render: walkRowsFast != walkRowsAll"; return 3
        pure wn
      else pure wf
    let B : Bundle :=
      { info := I, walks := ws, node := nodeRowsAll I uses, walk, rcpt := rcptRowsAll I,
        acct := acctRowsAll I, mrk := mrkRowsAll I, sort := sortRowsAll I,
        msgs := nodeMsgs I ++ acctMsgs I ++ mrkMsgs I ++ rcptMsgs I, errors := walkErrors I }
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
