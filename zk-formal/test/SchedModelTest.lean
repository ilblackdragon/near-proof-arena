import Lean.Data.Json
import ZkFormal.NearV3.Sched.Model

/-! Executable check of the scheduler event model (`lake env lean --run test/SchedModelTest.lean`).

For each of the 600 nearcore vectors (`oracle/fixtures/v3/vectors/scheduler.json`):
* `pub := pubOf pv86 …` (claim-only part), raw requests with resolved indices;
* `convRaw` (set-bit increases) equals `convertRaw pub.values base ids pub.raw` (what `runCore` converts);
* the previous state is canonicalised (`allow0` written as the layout's `n²` links in order, same
  sanity hash) — `runCore` gives the same output on both (the core depends on `prev` only through
  `allow0` and the hash);
* `coreEv` (link pass in closed form, rounds over a push log, sorted-grid distribute) gives the
  same state bytes and grants as `runCore`, and every structural check of the model passes
  (strictly decreasing round keys / 0-round ordinals, re-push to a smaller key, no `break`). -/

open Lean NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched

def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

def unhex (s : String) : List UInt8 :=
  let rec go : List Char → List UInt8
    | a :: b :: rest => UInt8.ofNat (hexVal a * 16 + hexVal b) :: go rest
    | _ => []
  go s.toList

def getStr (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
def getNat (j : Json) (k : String) : Nat := (j.getObjValAs? Nat k).toOption.getD 0
def getArr (j : Json) (k : String) : Array Json := (j.getObjValAs? (Array Json) k).toOption.getD #[]
def getDec (j : Json) (k : String) : Nat := (getStr j k).toNat!

def infoOf (c : Json) : CongestionInfo :=
  ⟨getDec c "delayed_receipts_gas", getDec c "buffered_receipts_gas",
   getNat c "receipt_bytes", getNat c "allowed_shard"⟩

def allow0Of (ids : List Nat) (prev : NearSpec.Bandwidth.State) : Array Nat :=
  let n := ids.length
  prev.links.foldl (fun (a : Array Nat) la =>
      match indexOf ids la.sender, indexOf ids la.receiver with
      | some s, some r => a.set! (s * n + r) la.allowance
      | _, _ => a) (Array.replicate (n * n) 0)

def canonOf (ids : List Nat) (prev : NearSpec.Bandwidth.State) : NearSpec.Bandwidth.State :=
  let n := ids.length
  let a := allow0Of ids prev
  ⟨(List.range (n * n)).map fun l => ⟨ids.getD (l / n) 0, ids.getD (l % n) 0, a[l]!⟩, prev.sanityHash⟩

def main : IO UInt32 := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "../oracle/fixtures/v3/vectors/scheduler.json"))
  let mut ok := 0
  let mut bad := 0
  let mut rounds := 0
  let mut maxRounds := 0
  let mut zeroRounds := 0
  let mut steps := 0
  for c in getArr j "cases" do
    let some ids := decodeShardLayoutV2 (unhex (getStr c "shard_layout_borsh"))
      | bad := bad + 1; IO.println "layout"; continue
    let prevB : Option (List UInt8) :=
      match c.getObjValAs? String "prev_state_borsh" with
      | .ok s => some (unhex s)
      | .error _ => none
    let congestion := (getArr c "congestion").toList.map fun x =>
      (getNat x "shard_id", infoOf x, getNat x "missed_chunks_count")
    let reqs := (getArr c "bandwidth_requests").toList.map fun x =>
      (getNat x "shard_id", decodeBandwidthRequests (unhex (getStr x "requests_borsh")))
    let some reqs := reqs.mapM (fun (s, r) => r.map (s, ·)) | bad := bad + 1; continue
    let seed := unhex (getStr c "prev_block_hash")
    let some pub := pubOf Config.pv86 CongestionConfig.pv86 ids congestion reqs seed
      | bad := bad + 1; IO.println "pubOf none"; continue
    let n := ids.length
    let raw : List RawReq := (toBTreeMap reqs).flatMap fun (sender, brs) =>
      brs.filterMap fun br => match indexOf ids sender, indexOf ids br.toShard with
        | some s, some r => some ⟨s, r, br.bitmap⟩
        | _, _ => none
    let conv := convRaw pub.params n raw
    let prevS? := match prevB with
      | none => some NearSpec.Bandwidth.State.initial
      | some b => NearSpec.Bandwidth.State.decode b
    let some prevS := prevS? | bad := bad + 1; IO.println "prev decode"; continue
    let canon := canonOf ids prevS
    let want := runCore pub prevB
    let wantC := runCore pub (if prevB.isNone then none else some canon.encode)
    let ev := coreEv ids pub.params pub.allowed raw pub.seed pub.allShardsHash
      (if prevB.isNone then NearSpec.Bandwidth.State.initial else canon)
    let good ← match want, wantC, ev with
      | some o, some oc, .ok e =>
        if conv != convertRaw pub.values pub.params.base pub.ids pub.raw then IO.println "convRaw differs"; pure false
        else if o.state != oc.state || o.granted != oc.granted then IO.println "canonical prev changes output"; pure false
        else if e.state != o.state then IO.println "state bytes differ"; pure false
        else if e.granted != o.granted.map (·.2) then IO.println "grants differ"; pure false
        else if o.state != unhex (getStr c "post_state_borsh") then IO.println "spec vs vector"; pure false
        else
          rounds := rounds + e.rounds.length
          maxRounds := Nat.max maxRounds e.rounds.length
          zeroRounds := zeroRounds + (e.rounds.filter (·.key == 0)).length
          steps := steps + (e.rounds.map (·.steps.length)).sum
          pure true
      | _, _, .error s => IO.println s!"model error: {s}"; pure false
      | _, _, _ => IO.println "spec none"; pure false
    if good then ok := ok + 1 else bad := bad + 1
  IO.println s!"scheduler model: {ok} ok, {bad} bad; rounds {rounds} (max {maxRounds}, key-0 {zeroRounds}), steps {steps}"
  return (if bad == 0 then 0 else 1)
