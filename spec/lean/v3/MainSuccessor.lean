import Lean
import NearSpecV3.Successor.Config

/-! Explicit-tier driver. I/O failures are errors, never semantic rejections or exclusions.
JSON encoding uses Lean's encoder, including control characters in paths and error strings. -/
open NearSpecV3 NearSpecV3.Successor

def parseTier : String → Option Successor.Tier
  | "signed" => some .signed
  | "floats" => some .floats
  | "protoGas" => some .protoGas
  | "floatsProtoGas" => some .floatsProtoGas
  | "genesis" => some .genesis
  | "genesisFloatsProtoGas" => some .genesisFloatsProtoGas
  | "runtimeLimits" => some .runtimeLimits
  | "storageResolution" => some .storageResolution
  | "globalActions" => some .globalActions
  | "completeCodeGlobal" => some .completeCodeGlobal
  | "curveHosts" => some .curveHosts
  | "resharding" => some .resharding
  | "allFeatures" => some .allFeatures
  | _ => none

def resultRow (dir tier verdict reason : String) : String :=
  (Lean.Json.mkObj [("case", toJson dir), ("tier", toJson tier),
    ("verdict", toJson verdict), ("reason", toJson reason)]).compress
where
  toJson := Lean.Json.str

def hexOf (bs : List UInt8) : String :=
  let d := fun (n : Nat) => if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  String.ofList (bs.flatMap fun b => [d (b.toNat / 16), d (b.toNat % 16)])

/-- The computed outputs as JSON (hex for byte strings, decimal strings for u128-sized numbers). -/
def outputsJson (o : Observable) : Lean.Json :=
  let hx := fun (b : List UInt8) => Lean.Json.str (hexOf b)
  let num := fun (n : Nat) => Lean.Json.str (toString n)
  Lean.Json.mkObj [
    ("stateRoot", hx o.stateRoot), ("outcomeRoot", hx o.outcomeRoot),
    ("gasUsed", num o.gasBurnt), ("balanceBurnt", num o.balanceBurnt),
    ("outgoingReceiptsRoot", hx o.outgoingReceiptsRoot),
    ("proposals", Lean.Json.arr (o.proposals.map hx).toArray),
    ("txRoot", hx o.txRoot), ("encodedMerkleRoot", hx o.encodedMerkleRoot),
    ("encodedLength", num o.encodedLength),
    ("congestion", Lean.Json.mkObj [
      ("delayedReceiptsGas", num o.congestion.delayedGas),
      ("bufferedReceiptsGas", num o.congestion.bufferedGas),
      ("receiptBytes", num o.congestion.receiptBytes),
      ("allowedShard", num o.congestion.allowedShard)]),
    ("bwRequests", Lean.Json.arr (o.bwRequests.map fun r =>
      Lean.Json.mkObj [("toShard", num r.toShard), ("bitmap", hx r.bitmap)]).toArray),
    ("receiptCount", num o.receiptCount), ("wasmGas", num o.wasmGas)]

/-- `--emit` runs every comparison and adds the computed outputs; `--blind` skips the comparisons
against produced values (for inputs whose output fields were zeroed by the harness). -/
def outputRow (dir tier : String) (r : Except String Observable) : String :=
  let (verdict, reason, outs) := match Verdict.ofExcept (r.map fun _ => ()), r with
    | .accept, .ok o => ("accept", "", outputsJson o)
    | .reject e, _ => ("reject", e, Lean.Json.null)
    | .outOfDomain e, _ => ("out_of_domain", e, Lean.Json.null)
    | .accept, .error e => ("reject", e, Lean.Json.null)
  (Lean.Json.mkObj [("case", Lean.Json.str dir), ("tier", Lean.Json.str tier),
    ("verdict", Lean.Json.str verdict), ("reason", Lean.Json.str reason),
    ("outputs", outs)]).compress

def main (args : List String) : IO UInt32 := do
  let "--tier" :: tierName :: rest := args
    | IO.eprintln "usage: nearspec-v3-check-successor --tier TIER [--emit|--blind] CASE_DIR..."; return 2
  let some tier := parseTier tierName
    | IO.eprintln s!"unknown successor tier: {tierName}"; return 2
  let (mode, dirs) := match rest with
    | "--emit" :: ds => (some false, ds)
    | "--blind" :: ds => (some true, ds)
    | ds => (none, ds)
  if dirs.isEmpty then
    IO.eprintln "at least one case directory is required"
    return 2
  let mut failed := false
  for dir in dirs do
    try
      let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
      let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
      match mode with
      | some blind =>
        IO.println (outputRow dir tierName (checkSuccessorObs tier.cfg blind cb.toList wb.toList))
      | none =>
        let (verdict, reason) := match checkVerdict (Tier.checker tier) cb.toList wb.toList with
          | .accept => ("accept", "")
          | .reject e => ("reject", e)
          | .outOfDomain e => ("out_of_domain", e)
        IO.println (resultRow dir tierName verdict reason)
    catch e =>
      failed := true
      IO.println (resultRow dir tierName "io_error" e.toString)
  return if failed then 2 else 0
