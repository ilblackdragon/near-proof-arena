import Conformance.AirJson
import ZkFormal.V2.Verifier
import ZkFormal.V2.G.Defs
import ZkFormal.Stark.Instance
import ArenaCore.SHA256Fast

/-!
`np-lean-verify-v2 <auxGroup> <air.json> <pub.bin> <claim.bin> <proof.bin>`

Runs **the deployed Lean verifier model of `np-udr-stark-v2`**,
`ZkFormal.V2.verifierP Fp Fp8 AP (ZkFormal.V2.G.pg g)`, exactly as deployed:
`(verifierP …).toVerifier.deployed pub cb pb` (the hash-query tree run against
`Interp.deployedRO`).  `air.json` is `np-air-v2`.  Prints `accept` (exit 0) or
`reject` (exit 1); usage/input errors exit 2.  Timing goes to stderr.
-/

open Conformance ZkFormal ZkFormal.Stark ZkFormal.Algebra ArenaCore

def deployedVerifyP (AP : ZkFormal.V2.AirP) (g : Nat) (pub cb pb : Bytes) : Bool :=
  (ZkFormal.V2.verifierP Fp Fp8 AP (ZkFormal.V2.G.pg g)).toVerifier.deployed pub cb pb

def readBytes (p : String) : IO Bytes := return (← IO.FS.readBinFile p).toList

def main (args : List String) : IO UInt32 := do
  match args with
  | [gS, airP, pubP, cbP, pbP] =>
    let some g := gS.toNat? | IO.eprintln "np-lean-verify-v2: bad auxGroup"; return 2
    unless 1 ≤ g ∧ g ≤ 3 do IO.eprintln "np-lean-verify-v2: auxGroup not in 1..3"; return 2
    let AP ← match parseAirPChecked (← IO.FS.readFile airP) with
      | .ok (A, same) =>
        IO.eprintln s!"air: {A.tables.length} table(s), {A.pubSegs.length} pubSeg(s); re-export json-equal, byte-identical={same}"
        pure A
      | .error e => IO.eprintln s!"np-lean-verify-v2: {airP}: {e}"; return 2
    let pub ← readBytes pubP
    let cb ← readBytes cbP
    let pb ← readBytes pbP
    let t0 ← IO.monoNanosNow
    let ok ← IO.lazyPure fun _ => deployedVerifyP AP g pub cb pb
    let t1 ← IO.monoNanosNow
    IO.eprintln s!"verify: proof {pb.length} B, wall {(t1 - t0) / 1000000} ms"
    IO.println (if ok then "accept" else "reject")
    return (if ok then 0 else 1)
  | _ =>
    IO.eprintln "usage: np-lean-verify-v2 <auxGroup> <air.json> <pub.bin> <claim.bin> <proof.bin>"
    return 2
