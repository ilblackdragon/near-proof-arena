import Conformance.AirJson
import ZkFormal.Stark.Verifier
import ZkFormal.Stark.Instance
import ArenaCore.SHA256Fast

/-!
`np-lean-verify <air.json> <pub.bin> <claim.bin> <proof.bin>`

Runs **the deployed Lean verifier model** of `np-udr-stark-v1`,
`ZkFormal.Stark.verifier Fp Fp8 air Params.default` (lane L4), exactly as it
is deployed: `(verifier …).toVerifier.deployed pub cb pb`, i.e. the hash-query
tree run by `ZkFormal.runH` against `Interp.deployedRO`
(`m ↦ sha256("NPAI-RO-v1" ‖ m)`).  `ArenaCore.SHA256Fast` is imported so the
`@[csimp]` lemma `sha256_eq_sha256Fast` makes the compiled code call the fast
SHA-256.

Prints `accept` (exit 0) or `reject` (exit 1); usage/input errors exit 2.
Timing goes to stderr.
-/

open Conformance ZkFormal ZkFormal.Stark ZkFormal.Algebra ArenaCore

/-- The deployed decision function for an AIR (`OracleVerifier.deployed`). -/
def deployedVerify (A : ZkFormal.Air.Air) (pub cb pb : Bytes) : Bool :=
  (verifier Fp Fp8 A Params.default).toVerifier.deployed pub cb pb

def readBytes (p : String) : IO Bytes := return (← IO.FS.readBinFile p).toList

def main (args : List String) : IO UInt32 := do
  match args with
  | [airP, pubP, cbP, pbP] =>
    let A ← match parseAirChecked (← IO.FS.readFile airP) with
      | .ok (A, same) =>
        IO.eprintln s!"air: {A.tables.length} table(s); re-export json-equal, byte-identical={same}"
        pure A
      | .error e => IO.eprintln s!"np-lean-verify: {airP}: {e}"; return 2
    let pub ← readBytes pubP
    let cb ← readBytes cbP
    let pb ← readBytes pbP
    let t0 ← IO.monoNanosNow
    -- evaluated inside the timed window (not floated out by the compiler)
    let ok ← IO.lazyPure fun _ => deployedVerify A pub cb pb
    let t1 ← IO.monoNanosNow
    IO.eprintln s!"verify: proof {pb.length} B, wall {(t1 - t0) / 1000000} ms"
    unless ok do
      -- diagnostics only (pure, no hashing): how far the commit-phase parse gets
      let V := Iop.verifier Fp Fp8 A Params.default
      let hdr := readHeader V.numTables pb
      let pre := parsePrefix (F := Fp) V pb
      IO.eprintln s!"diag: header={(hdr.map (·.1))} headerOk={(hdr.map fun h => V.headerOk h.1)} parsePrefix={if pre.isSome then "ok" else "fail"}"
    IO.println (if ok then "accept" else "reject")
    return (if ok then 0 else 1)
  | _ =>
    IO.eprintln "usage: np-lean-verify <air.json> <pub.bin> <claim.bin> <proof.bin>"
    return 2
