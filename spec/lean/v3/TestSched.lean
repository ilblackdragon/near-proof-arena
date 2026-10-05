import Lean.Data.Json
import NearSpecV3

/-!
Differential tests of `NearSpecV3.F64`, `NearSpecV3.Congestion` and
`NearSpecV3.Scheduler` against vectors produced by nearcore's own code
(`oracle/fixtures/v3/vectors/{congestion,scheduler}.json`).
Usage: `nearspec-v3-test-sched [DIR]`.
-/

open Lean NearSpecV3 NearSpecV3.Scheduler

def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

def unhex (s : String) : List UInt8 :=
  let rec go : List Char → List UInt8
    | a :: b :: rest => UInt8.ofNat (hexVal a * 16 + hexVal b) :: go rest
    | _ => []
  go s.toList

def hexNat (s : String) : Nat := s.toList.foldl (fun acc c => acc * 16 + hexVal c) 0

def getStr (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
def getNat (j : Json) (k : String) : Nat := (j.getObjValAs? Nat k).toOption.getD 0
def getBool (j : Json) (k : String) : Bool := (j.getObjValAs? Bool k).toOption.getD false
def getArr (j : Json) (k : String) : Array Json := (j.getObjValAs? (Array Json) k).toOption.getD #[]
/-- decimal string (u128 fields) -/
def getDec (j : Json) (k : String) : Nat := (getStr j k).toNat!

def infoOf (c : Json) : CongestionInfo :=
  ⟨getDec c "delayed_receipts_gas", getDec c "buffered_receipts_gas",
   getNat c "receipt_bytes", getNat c "allowed_shard"⟩

def configOf (j : Json) : CongestionConfig :=
  ⟨getNat j "max_congestion_incoming_gas", getNat j "max_congestion_outgoing_gas",
   getNat j "max_congestion_memory_consumption", getNat j "max_congestion_missed_chunks",
   getNat j "max_outgoing_gas", getNat j "min_outgoing_gas", getNat j "allowed_shard_outgoing_gas"⟩

def testCongestion (dir : String) : IO (Nat × Nat) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir ++ "/congestion.json")))
  let cfg := configOf ((j.getObjVal? "config").toOption.getD Json.null)
  let mut ok := 0
  let mut bad := 0
  if cfg != CongestionConfig.pv86 then
    IO.println "congestion: vector config differs from CongestionConfig.pv86"
    bad := bad + 1
  for c in getArr j "cases" do
    let info := infoOf c
    let missed := getNat c "missed_chunks_count"
    let lvl := Congestion.level cfg info missed
    let fully := Congestion.isFullyCongested cfg info missed
    let good :=
      F64.toBits lvl == hexNat (getStr c "level_bits") &&
      fully == getBool c "fully_congested" &&
      Congestion.fullyCongestedInt info missed == fully &&
      Congestion.outgoingGasLimit cfg info missed info.allowedShard ==
        getNat c "outgoing_gas_limit_from_allowed" &&
      Congestion.outgoingGasLimit cfg info missed (info.allowedShard + 1) ==
        getNat c "outgoing_gas_limit_from_other"
    if good then ok := ok + 1 else
      bad := bad + 1
      if bad ≤ 5 then IO.println s!"congestion mismatch: {c.compress}"
  return (ok, bad)

/-- Dense sweep of `fullyCongestedInt` against the float model around every
threshold (each field alone, others zero). -/
def sweepFully : IO (Nat × Nat) := do
  let cfg := CongestionConfig.pv86
  let mut ok := 0
  let mut bad := 0
  let mk (d b r : Nat) : CongestionInfo := ⟨d, b, r, 0⟩
  let ranges : List (Nat × (Nat → CongestionInfo × Nat)) :=
    [ (400000000000000000, fun v => (mk v 0 0, 0)),
      (10000000000000000, fun v => (mk 0 v 0, 0)),
      (1000000000, fun v => (mk 0 0 v, 0)),
      (125, fun v => (mk 0 0 0, v)) ]
  for (center, f) in ranges do
    for k in [0:4001] do
      if k ≤ center + 2000 then
        let v := center + 2000 - k
        let (info, missed) := f v
        if Congestion.isFullyCongested cfg info missed == Congestion.fullyCongestedInt info missed
        then ok := ok + 1 else
          bad := bad + 1
          IO.println s!"sweep mismatch at {v}"
  -- generic form `clampedIsOneInt` vs the float model on random-ish points
  for k in [0:20000] do
    let mx := 1 + (k * 2654435761 + 12345) % 18446744073709551615
    let v := mx - (k % 3000)
    let lhs := F64.beq (Congestion.clampedFraction v mx) F64.one
    if lhs == Congestion.clampedIsOneInt v mx then ok := ok + 1 else
      bad := bad + 1
      IO.println s!"clamped mismatch at {v} / {mx}"
  return (ok, bad)


/-- nearcore's deterministic unit tests of `distribute_remaining_bandwidth`
(`distribute_remaining.rs` tests `test_one_link` … `test_two_fully_congested`):
(sender budgets, receiver budgets, allowed links or all, expected grants). -/
def distributeCases : List (List Nat × List Nat × Option (List (Nat × Nat)) × List (Nat × Nat × Nat)) :=
  [ ([50], [100], none, [(0, 0, 50)]),
    ([50], [100], some [], []),
    ([300, 300, 300], [300, 300, 300], none,
      [(0,0,100),(0,1,100),(0,2,100),(1,0,100),(1,1,100),(1,2,100),(2,0,100),(2,1,100),(2,2,100)]),
    ([100, 100, 100], [100, 100, 100], some [(1,0),(1,2),(0,1),(2,1)],
      [(0,1,50),(1,0,50),(1,2,50),(2,1,50)]),
    ([300, 300, 300], [300, 300, 300], some [(0,0),(0,1),(1,0),(1,2),(2,0)],
      [(0,0,100),(0,1,200),(1,0,100),(1,2,200),(2,0,100)]) ]

def testDistribute : IO (Nat × Nat) := do
  let mut ok := 0
  let mut bad := 0
  for (sb, rb, al, want) in distributeCases do
    let n := sb.length
    let allowed : Array Bool := ((List.range (n * n)).map fun l =>
      match al with
      | none => true
      | some ls => ls.contains (l / n, l % n)).toArray
    let st : St := ⟨sb.toArray, rb.toArray, Array.replicate (n * n) 0,
      Array.replicate (n * n) 0, Rng.ofSeed (List.replicate 32 0)⟩
    let st := distribute n allowed st
    let got := (List.range (n * n)).filterMap fun l =>
      if st.granted[l]! = 0 then none else some (l / n, l % n, st.granted[l]!)
    if got == want then ok := ok + 1 else
      bad := bad + 1
      IO.println s!"distribute mismatch: got {got} want {want}"
  return (ok, bad)

def testScheduler (dir : String) : IO (Nat × Nat) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir ++ "/scheduler.json")))
  let mut ok := 0
  let mut bad := 0
  for c in getArr j "cases" do
    let ids := decodeShardLayoutV2 (unhex (getStr c "shard_layout_borsh"))
    let prev : Option (List UInt8) :=
      match c.getObjValAs? String "prev_state_borsh" with
      | .ok s => some (unhex s)
      | .error _ => none
    let congestion := (getArr c "congestion").toList.map fun x =>
      (getNat x "shard_id", infoOf x, getNat x "missed_chunks_count")
    let reqs := (getArr c "bandwidth_requests").toList.map fun x =>
      (getNat x "shard_id", decodeBandwidthRequests (unhex (getStr x "requests_borsh")))
    let reqs? := reqs.mapM fun (s, r) => r.map (s, ·)
    let want := unhex (getStr c "post_state_borsh")
    let got := match ids, reqs? with
      | some ids, some reqs =>
        (run Config.pv86 CongestionConfig.pv86 ids prev congestion reqs
          (unhex (getStr c "prev_block_hash"))).map (·.state)
      | _, _ => none
    if got == some want then ok := ok + 1 else
      bad := bad + 1
      if bad ≤ 3 then
        IO.println s!"scheduler mismatch (ids {ids}, reqs ok {reqs?.isSome}): {(c.getObjValAs? Nat "block_height").toOption}"
  return (ok, bad)

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "../../../oracle/fixtures/v3/vectors"
  let (ok1, bad1) ← testCongestion dir
  IO.println s!"congestion: {ok1} ok, {bad1} bad"
  let (ok2, bad2) ← sweepFully
  IO.println s!"fully-congested sweep: {ok2} ok, {bad2} bad"
  let (ok3, bad3) ← testScheduler dir
  IO.println s!"scheduler: {ok3} ok, {bad3} bad"
  let (ok4, bad4) ← testDistribute
  IO.println s!"distribute_remaining unit cases: {ok4} ok, {bad4} bad"
  return (if bad1 + bad2 + bad3 + bad4 == 0 then 0 else 1)
