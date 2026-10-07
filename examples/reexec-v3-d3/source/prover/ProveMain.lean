import NearSpecV3.ChallengeChunkV3
import ReexecV3D3.ReadCanonDefs

/-!
# `prove` (Lean, compiled with the verifier model)

`prove --public DIR --request FILE --witness FILE --claim-out FILE --proof-out FILE`

`claim.bin` = `request.bin` (the request IS the claim, `near-arena-claim-v3`).
`proof.bin` = `ReexecV3D3.Read.canonW` of the witness: one logged validator
execution, then canonical encoding of exactly its recorded-store answers. Every
`RelD3` witness yields accepted bytes of no greater length (`ReadComplete`).
Malformed or invalid input is refused with exit 2; normalization reuses the
single successful logged execution.
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
  | .ok _ =>
    match Logged.checkD3Reads c.encode w with
    | (.error e, _) => throw s!"witness: {e}"
    | (.ok (), keys) => pure (Read.encodeReads c.encode w keys)

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
