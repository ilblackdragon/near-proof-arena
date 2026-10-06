import NearSpecV3.ChallengeChunkV3
import ReexecV3D3.Canon

/-!
# `prove` (Lean, compiled with the verifier model)

`prove --public DIR --request FILE --witness FILE --claim-out FILE --proof-out FILE`

`claim.bin` = `request.bin` (the request IS the claim, `near-arena-claim-v3`).
`proof.bin` = `ReexecV3D3.proveW` of the witness file (`Canon.lean`): its **normal form** computed by
the verifier model's own normaliser `canonW` (ignored fields zeroed, receipt proofs one per key in
key order, `base_state`s cut to their reachable values in SHA-256 order, exactly the needed code
blobs in SHA-256 order: one `checkD3` run per candidate blob), provided that is usable (`canonOkOf`:
`checkD3` accepts it and it is a fixed point — `1 + k` more runs), else the witness unchanged. For
every `RelD3` witness the verifier accepts the output (`Obligations.lean`: `check_proveW`). A request that is not a well-formed claim, or a
witness that is not a `near-arena-witness-v3` file, is refused with exit 2.
-/

open NearSpec NearSpecV3 ReexecV3D3

def argOf (args : List String) (name : String) : Option String :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => some v
  | _ => none

def normalProof (cb w : Bytes) : Except String Bytes := do
  let c ← match WfClaim.decode cb with
    | some c => pure c
    | none => throw "request: not a well-formed near-arena-claim-v3 claim"
  match decodeWitnessFile w with
  | .error e => throw s!"witness: {e}"
  | .ok _ => pure (proveW c.encode w)

def main (args : List String) : IO UInt32 := do
  match argOf args "--public", argOf args "--request", argOf args "--witness",
      argOf args "--claim-out", argOf args "--proof-out" with
  | some _, some rq, some wt, some co, some po =>
    if args.length != 10 then
      IO.eprintln "usage: prove --public DIR --request FILE --witness FILE --claim-out FILE --proof-out FILE"
      return 2
    try
      let cb ← IO.FS.readBinFile rq
      let w ← IO.FS.readBinFile wt
      match normalProof cb.toList w.toList with
      | .error e =>
        IO.eprintln s!"error: {e}"
        return 2
      | .ok p =>
        IO.FS.writeBinFile co cb
        IO.FS.writeBinFile po (ByteArray.mk p.toArray)
        return 0
    catch e =>
      IO.eprintln s!"error: {e}"
      return 2
  | _, _, _, _, _ =>
    IO.eprintln "usage: prove --public DIR --request FILE --witness FILE --claim-out FILE --proof-out FILE"
    return 2
