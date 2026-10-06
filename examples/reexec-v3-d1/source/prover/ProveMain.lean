import NearSpecV3.ChallengeV3
import ReexecV3D1.NormBytesDefs

/-!
# `prove` (Lean, compiled with the verifier model)

`prove --public DIR --request FILE --witness FILE --claim-out FILE --proof-out FILE`

`claim.bin` = `request.bin` (the request IS the claim, `near-arena-claim-v3`).
`proof.bin` = the witness file with its state witness replaced by the output of the
verifier model's own normaliser `ReexecV3D1.normSW` (the keys and root from
`ReexecV3D1.keysD0`, as `ReexecV3D1.normalW` computes them). The certificate proves
that for every `RelD0` witness this output is accepted (`relD0_normal`). A witness the
normaliser cannot process (no `RelD0` keys: the claim is false or out of domain, or the
witness does not decode) is refused with exit 2.
-/

open NearSpec NearSpecV3 ReexecV3D1

def argOf (args : List String) (name : String) : Option String :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => some v
  | _ => none

/-- `ReexecV3D1.wrapW`: the witness file of a state witness with no contract code. -/
def wrapFile (c : Bytes) : Bytes := borshBytes witnessTag ++ (borshBytes c ++ encList borshBytes [])

def normalProof (cb w : Bytes) : Except String Bytes := do
  let c ← match WfClaim.decode cb with
    | some c => pure c
    | none => throw "request: not a well-formed near-arena-claim-v3 claim"
  let (sw, codes) ← decodeWitnessFile w
  if !codes.isEmpty then throw "witness: contract code (outside D0)"
  let (K, R) ← keysD0 c.encode w
  let n ← normSW K R sw
  pure (wrapFile n)

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
