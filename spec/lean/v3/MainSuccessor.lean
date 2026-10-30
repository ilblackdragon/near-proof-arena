import Lean
import NearSpecV3.Successor.Config
import NearSpecV3.Successor.SchemaVersion

/-! Explicit-tier driver. I/O failures are errors, never semantic rejections or exclusions.
JSON encoding uses Lean's encoder, including control characters in paths and error strings. -/
open NearSpec NearSpecV3 NearSpecV3.Successor

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

/-- `"system"`, the predecessor of every refund receipt (`AccountId::system_account`). -/
def systemAccount : List UInt8 := "system".toUTF8.toList

def statusJson : OStatus → Lean.Json
  | .value => Lean.Json.mkObj [("kind", "value"), ("value", "")]
  | .valueBytes v => Lean.Json.mkObj [("kind", "value"), ("value", Lean.Json.str (hexOf v))]
  | .receipt rid => Lean.Json.mkObj [("kind", "receipt"), ("receiptId", Lean.Json.str (hexOf rid))]
  | .failure => Lean.Json.mkObj [("kind", "failure")]

def rbodyKind : D2.RBody → String
  | .action false _ => "action"
  | .action true _ => "promise_yield"
  | .data false _ _ => "data"
  | .data true _ _ => "promise_resume"
  | .distribution _ => "global_contract_distribution"

/-- Version 2 detail (W01): every outcome, outgoing receipt and committed storage change, as the
checker computed them. Byte strings are hex; account ids are hex of their UTF-8 bytes. -/
def detailJson (o : Observable) : List (String × Lean.Json) :=
  let hx := fun (b : List UInt8) => Lean.Json.str (hexOf b)
  let num := fun (n : Nat) => Lean.Json.str (toString n)
  let lookup := fun {α : Type} (l : List (List UInt8 × α)) (id : List UInt8) =>
    (l.find? (·.1 == id)).map (·.2)
  let d := o.detail
  -- version 3 (W01): the failure kind inside a failed status, each outcome's compute usage
  let status := fun (x : OutD1) => match x.status, d with
    | .failure, some d => Lean.Json.mkObj [("kind", "failure"),
        ("error", match lookup d.failKinds x.o.id with
          | some k => Lean.Json.str k
          | none => Lean.Json.null)]
    | s, _ => statusJson s
  let outcome := fun (x : OutD1) => Lean.Json.mkObj ([
    ("id", hx x.o.id), ("executor", hx x.o.executorId), ("status", status x),
    ("gasBurnt", num x.o.gasBurnt), ("tokensBurnt", num x.o.tokensBurnt),
    ("logs", Lean.Json.arr (x.logs.map hx).toArray),
    ("receiptIds", Lean.Json.arr (x.o.receiptIds.map hx).toArray),
    ("leaf", hx x.leaf)] ++ (match d with
      | some d => [("computeUsage", match lookup d.outCompute x.o.id with
          | some c => num c
          | none => Lean.Json.null)]
      | none => []))
  let rcpt := fun (r : D2.Rcpt) => Lean.Json.mkObj [
    ("id", hx r.rid), ("predecessor", hx r.pred), ("receiver", hx r.recv),
    ("kind", Lean.Json.str (rbodyKind r.body)), ("hash", hx (sha256 r.encode)),
    ("refund", Lean.Json.bool (r.pred == systemAccount))]
  let change := fun ((k, v) : Bytes × Option Bytes) => Lean.Json.mkObj [
    ("key", hx k),
    ("valueHash", match v with | some x => hx (sha256 x) | none => Lean.Json.null),
    ("valueLen", match v with | some x => num x.length | none => Lean.Json.null)]
  [("outcomes", Lean.Json.arr (o.outcomes.map outcome).toArray),
   ("outgoingReceipts", Lean.Json.arr (o.outgoing.map rcpt).toArray),
   ("stateChanges", match o.stateChanges with
      | some cs => Lean.Json.arr (cs.map change).toArray
      | none => Lean.Json.null),
   ("computeUsage", match o.computeUsage with | some c => num c | none => Lean.Json.null),
   -- version 3 (W01): per processed transaction / receipt, the committed keys it changed
   -- (an entry behind the marker id lists keys whose pre-state value the witness does not reveal)
   ("receiptStateChanges", match d with
      | some d => Lean.Json.arr (d.attrib.map fun (ids, cs) =>
          let (pre, ids) := match ids with
            | m :: rest => if m == StorageExecution.unknownPreMarker then (false, rest) else (true, ids)
            | [] => (true, ids)
          Lean.Json.mkObj [
            ("ids", Lean.Json.arr (ids.map hx).toArray), ("preKnown", Lean.Json.bool pre),
            ("changes", Lean.Json.arr (cs.map change).toArray)]).toArray
      | none => Lean.Json.null)]

/-- The emitted detail is the list the checker hashed: the outcome root, gas, logs and receipt count
recomputed from it must equal the computed header-level values. A failure is a checker bug. -/
def detailSelfCheck (o : Observable) : List (String × Bool) :=
  [("outcomeRoot", outcomeRootD1 o.outcomes == o.outcomeRoot),
   ("gasUsed", (o.outcomes.map (·.o.gasBurnt)).foldl (· + ·) 0 == o.gasBurnt),
   ("logs", (o.outcomes.map (·.logs)).flatten == o.logs),
   ("receiptCount", o.outgoing.length == o.receiptCount)]

/-- `--emit-full` / `--blind-full`: the version-2 row (the version-1 fields plus `detailJson`). -/
def outputRowFull (dir tier : String) (r : Except String Observable) : String × Bool :=
  match Verdict.ofExcept (r.map fun _ => ()), r with
  | .accept, .ok o =>
    let sc := detailSelfCheck o
    let ok := sc.all (·.2)
    let outs := match outputsJson o with
      | .obj kvs => Lean.Json.obj (detailJson o |>.foldl (fun m (k, v) => m.insert k v) kvs)
      | j => j
    ((Lean.Json.mkObj [("case", Lean.Json.str dir), ("tier", Lean.Json.str tier),
      ("verdict", Lean.Json.str (if ok then "accept" else "internal_error")),
      ("reason", Lean.Json.str (if ok then "" else "emitted detail does not hash to the computed outputs")),
      ("outputsVersion", (if o.detail.isSome then 3 else 2 : Nat)),
      ("selfCheck", Lean.Json.mkObj (sc.map fun (k, b) => (k, Lean.Json.bool b))),
      ("outputs", outs)]).compress, ok)
  | v, _ =>
    let (verdict, reason) := match v, r with
      | .reject e, _ => ("reject", e)
      | .outOfDomain e, _ => ("out_of_domain", e)
      | _, .error e => ("reject", e)
      | _, _ => ("reject", "")
    ((Lean.Json.mkObj [("case", Lean.Json.str dir), ("tier", Lean.Json.str tier),
      ("verdict", Lean.Json.str verdict), ("reason", Lean.Json.str reason),
      ("outputsVersion", (2 : Nat)), ("outputs", Lean.Json.null)]).compress, true)

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
    | IO.eprintln "usage: nearspec-v3-check-successor --tier TIER [--ablate-loading-limits] [--ablate-reshard-handover] [--emit|--blind|--emit-full|--blind-full] CASE_DIR..."; return 2
  let some tier := parseTier tierName
    | IO.eprintln s!"unknown successor tier: {tierName}"; return 2
  -- `--ablate-loading-limits`: a deliberate-breakage control only (the pinned instance-loading rule
  -- switched off); every tier sets it since 2026-10-27, so no tier can serve as the control.
  let (ablate, rest) := match rest with
    | "--ablate-loading-limits" :: ds => (true, ds)
    | ds => (false, ds)
  -- `--ablate-reshard-handover`: a deliberate-breakage control only (UQ-010, 2026-10-29): the signed
  -- statement without the resharding hand-over, i.e. the legacy core `D3.checkD3Core`.
  let (ablateHandover, rest) := match rest with
    | "--ablate-reshard-handover" :: ds => (true, ds)
    | ds => (false, ds)
  let cfg := if ablate then { tier.cfg with loadingLimits := false } else tier.cfg
  let cfg := if ablateHandover then { cfg with reshardHandover := false } else cfg
  let (mode, full, dirs) := match rest with
    | "--emit" :: ds => (some false, false, ds)
    | "--blind" :: ds => (some true, false, ds)
    | "--emit-full" :: ds => (some false, true, ds)
    | "--blind-full" :: ds => (some true, true, ds)
    | ds => (none, false, ds)
  -- `--emit-full` / `--blind-full` also record the W01 detail (observation only, `observeDetail`)
  let cfg := if full then { cfg with observeDetail := true } else cfg
  if dirs.isEmpty then
    IO.eprintln "at least one case directory is required"
    return 2
  let mut failed := false
  for dir in dirs do
    try
      let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
      let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
      -- Every non-signed tier reads the versioned envelope (spec/claim-v3-versioning.md); unversioned
      -- files are schema version 3 and are passed through unchanged (`checkVersioned_legacy`).
      -- The signed tier keeps its exact signed byte format.
      let versioned := tierName != "signed"
      match mode with
      | some blind =>
        let r := if versioned then Schema.checkVersionedObs cfg blind cb.toList wb.toList
          else checkSuccessorObs cfg blind cb.toList wb.toList
        if full then
          let (row, ok) := outputRowFull dir tierName r
          if !ok then failed := true
          IO.println row
        else
          IO.println (outputRow dir tierName r)
      | none =>
        let chk := if versioned then Schema.checkVersioned cfg else checkSuccessor cfg
        let (verdict, reason) := match checkVerdict chk cb.toList wb.toList with
          | .accept => ("accept", "")
          | .reject e => ("reject", e)
          | .outOfDomain e => ("out_of_domain", e)
        IO.println (resultRow dir tierName verdict reason)
    catch e =>
      failed := true
      IO.println (resultRow dir tierName "io_error" e.toString)
  return if failed then 2 else 0
