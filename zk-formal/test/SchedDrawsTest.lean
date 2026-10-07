import Lean.Data.Json
import ZkFormal.NearV3.Sched.Gen.Run

/-! Executable measurement of the RNG words drawn by the scheduler's shuffles
(`lake env lean --run test/SchedDrawsTest.lean [limit]`). Not part of the library.

For each nearcore vector of `oracle/fixtures/v3/vectors/scheduler.json` (one instance, τ = 0),
`Gen.run`, then per round the `L − 1` `gen_index` calls of the shuffle replayed with `genAt 64`:
words drawn per call (`= 1 + rejections`), calls, words and ChaCha blocks per run; steps `S`,
rounds `Rd`, converted requests `C`, shards `n`. Prints min / median / max over the vectors and
the per-call draw histogram. -/

open Lean NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Sched.Gen ZkFormal.Chacha

/-! ## Vector parsing (as in SchedModelTest) -/

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

def inputOf (c : Json) : Except String Input := do
  let some ids := decodeShardLayoutV2 (unhex (getStr c "shard_layout_borsh")) | throw "layout"
  let prevB : Option (List UInt8) :=
    match c.getObjValAs? String "prev_state_borsh" with
    | .ok s => some (unhex s)
    | .error _ => none
  let congestion := (getArr c "congestion").toList.map fun x =>
    (getNat x "shard_id", infoOf x, getNat x "missed_chunks_count")
  let reqs := (getArr c "bandwidth_requests").toList.map fun x =>
    (getNat x "shard_id", decodeBandwidthRequests (unhex (getStr x "requests_borsh")))
  let some reqs := reqs.mapM (fun (s, r) => r.map (s, ·)) | throw "requests"
  let seed := unhex (getStr c "prev_block_hash")
  let some pub := pubOf Config.pv86 CongestionConfig.pv86 ids congestion reqs seed | throw "pubOf"
  let raw : List RawReq := (toBTreeMap reqs).flatMap fun (sender, brs) =>
    brs.filterMap fun br => match indexOf ids sender, indexOf ids br.toShard with
      | some s, some r => some ⟨s, r, br.bitmap⟩
      | _, _ => none
  let prev ← match prevB with
    | none => pure NearSpec.Bandwidth.State.initial
    | some b => match NearSpec.Bandwidth.State.decode b with
      | some s => pure (canonOf ids s)
      | none => throw "prev decode"
  return ⟨ids, pub.params, pub.allowed, raw, pub.seed, pub.allShardsHash, prev⟩


/-- Words drawn by each `gen_index` call of a round's shuffle (from position `k0`, `L` entries). -/
def callDraws (key : List Nat) (k0 L : Nat) : Except String (List Nat × Nat) := do
  let mut k := k0
  let mut ds : Array Nat := #[]
  for i in List.range (L - 1) do
    let q := L - 1 - i
    match genAt 64 (q + 1) key k with
    | none => throw "genAt fuel"
    | some (_, k') => ds := ds.push (k' - k); k := k'
  return (ds.toList, k)

def stats (xs : Array Nat) : String :=
  if xs.isEmpty then "-" else
  let s := xs.qsort (· < ·)
  s!"min {s[0]!}, median {s[s.size / 2]!}, max {s[s.size - 1]!}, total {s.foldl (· + ·) 0}"

def main (args : List String) : IO UInt32 := do
  let limit := (args.head?.bind String.toNat?).getD 600
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "../oracle/fixtures/v3/vectors/scheduler.json"))
  let cases := (getArr j "cases").toList.take limit
  let mut words : Array Nat := #[]
  let mut calls : Array Nat := #[]
  let mut blocks : Array Nat := #[]
  let mut steps : Array Nat := #[]
  let mut rds : Array Nat := #[]
  let mut convs : Array Nat := #[]
  let mut ns : Array Nat := #[]
  let mut hist : Array Nat := Array.replicate 65 0
  let mut bad := 0
  let mut idx := 0
  let mut maxRatio : Nat × Nat := (0, 1)
  for c in cases do
    idx := idx + 1
    let I ← match inputOf c with
      | .ok I => pure I
      | .error e => IO.println s!"vector {idx - 1}: input {e}"; bad := bad + 1; continue
    let R ← match run I with
      | .ok R => pure R
      | .error e => IO.println s!"vector {idx - 1}: run {e}"; bad := bad + 1; continue
    let mut nc := 0
    let mut S := 0
    for rd in R.rounds do
      S := S + rd.Lr
      match callDraws R.key rd.kst rd.Lr with
      | .error e => IO.println s!"vector {idx - 1}: {e}"; bad := bad + 1
      | .ok (ds, kend) =>
        if kend != rd.kend then IO.println s!"vector {idx - 1}: kend differs"; bad := bad + 1
        for d in ds do
          hist := hist.modify (min d 64) (· + 1)
          nc := nc + 1
    words := words.push R.kfin
    calls := calls.push nc
    blocks := blocks.push ((R.kfin + 15) / 16)
    steps := steps.push S
    rds := rds.push R.rounds.length
    convs := convs.push R.conv.length
    ns := ns.push R.n
    if nc > 0 && R.kfin * maxRatio.2 > maxRatio.1 * nc then maxRatio := (R.kfin, nc)
  IO.println s!"vectors: {words.size} ok, {bad} errors"
  IO.println s!"n (shards): {stats ns}"
  IO.println s!"C (converted requests): {stats convs}"
  IO.println s!"S (steps): {stats steps}"
  IO.println s!"Rd (rounds): {stats rds}"
  IO.println s!"gen_index calls per run (= S − Rd): {stats calls}"
  IO.println s!"words drawn per run (K): {stats words}"
  IO.println s!"ChaCha blocks per run (⌈K/16⌉): {stats blocks}"
  IO.println s!"max words / calls in a run: {maxRatio.1} / {maxRatio.2}"
  let tot := hist.foldl (· + ·) 0
  let mut line := "draws per call (histogram):"
  for d in List.range 65 do
    if hist[d]! > 0 then line := line ++ s!" {d}:{hist[d]!}"
  IO.println line
  IO.println s!"calls: {tot}; max draws in one call: {(List.range 65).foldl (fun m d => if hist[d]! > 0 then d else m) 0}"
  return (if bad = 0 then 0 else 1)
