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
  | _ => none

def resultRow (dir tier verdict reason : String) : String :=
  (Lean.Json.mkObj [("case", toJson dir), ("tier", toJson tier),
    ("verdict", toJson verdict), ("reason", toJson reason)]).compress
where
  toJson := Lean.Json.str

def main (args : List String) : IO UInt32 := do
  let "--tier" :: tierName :: dirs := args
    | IO.eprintln "usage: nearspec-v3-check-successor --tier TIER CASE_DIR..."; return 2
  let some tier := parseTier tierName
    | IO.eprintln s!"unknown successor tier: {tierName}"; return 2
  if dirs.isEmpty then
    IO.eprintln "at least one case directory is required"
    return 2
  let mut failed := false
  for dir in dirs do
    try
      let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
      let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
      let (verdict, reason) := match checkVerdict (Tier.checker tier) cb.toList wb.toList with
        | .accept => ("accept", "")
        | .reject e => ("reject", e)
        | .outOfDomain e => ("out_of_domain", e)
      IO.println (resultRow dir tierName verdict reason)
    catch e =>
      failed := true
      IO.println (resultRow dir tierName "io_error" e.toString)
  return if failed then 2 else 0
