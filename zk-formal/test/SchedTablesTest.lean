import Lean.Data.Json
import ZkFormal.NearV3.Sched.Gen.Cmp
import ZkFormal.NearV3.Sched.Gen.Mem
import ZkFormal.NearV3.Sched.Gen.Dist
import ZkFormal.NearV3.Sched.Gen.Proc
import ZkFormal.NearV3.Sched.Gen.Lane
import ZkFormal.NearV3.Sched.Render

/-! Executable check of the scheduler tables' honest traces
(`lake env lean --run test/SchedTablesTest.lean [limit]`). Not part of the library.

For each nearcore vector of `oracle/fixtures/v3/vectors/scheduler.json` (one instance, τ = 0):
`Gen.run` (checked against `processEv` / `coreEv`), the honest traces of `scpV3`, `smmV3`,
`ssdV3` (scan + distribute, width cut B), `sprV3` and of lane v3-chacha's `shufV3`, `genV3`,
`chachaV3` (scheduler buses); every constraint on every row, multiplicity bits 0/1, and balance
of the buses `SCMP`, `SOP`, `SFIN`, `SINC`, `SPUSH`, `SDLX`, `SDG`, the six shuffle buses and the
public buses `SPUBB` (key records), `SPAR` (tags 1–4) against the expected external traffic
(link INIT messages and finals of the codec, grid grants received by the codec, public records).
Then single-cell mutants per table on the largest vector. -/

open Lean NearSpecV3 NearSpecV3.Scheduler ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Sched.Gen

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

/-! ## Tables, constraints, messages -/

structure Tab where
  name : String
  tr : Trace Fp
  cs : Array Expr
  is : List Interaction

instance : Inhabited Tab := ⟨⟨"", ⟨fun _ => 0, fun _ _ _ => 0⟩, #[], []⟩⟩

def Tab.h (T : Tab) : Nat := T.tr.height 0

def checkRows (T : Tab) (rows : List Nat) : List (Nat × Nat) := Id.run do
  let mut bad := []
  for r in rows do
    for i in List.range T.cs.size do
      if (T.cs[i]!).eval T.tr 0 r [] != 0 then bad := (r, i) :: bad
  return bad.reverse

def violations (T : Tab) : List (Nat × Nat) := checkRows T (List.range T.h)

/-- Active messages `(bus, send, msg)` (repeated by multiplicity) and the number of non-0/1
multiplicity bits. -/
def msgs (T : Tab) : List (Nat × Bool × List Nat) × Nat := Id.run do
  let mut out := #[]
  let mut badBits := 0
  for r in List.range T.h do
    for it in T.is do
      for b in it.mult do
        let v := b.eval T.tr 0 r []
        if v != 0 && v != 1 then badBits := badBits + 1
      let m := it.multNat T.tr 0 r []
      for _ in List.range m do
        out := out.push (it.bus, it.send, it.msg.map fun e => (e.eval T.tr 0 r []).toNat)
  return (out.toList, badBits)

def ltL : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs => a < b || (a == b && ltL as bs)

def sortL (l : List (List Nat)) : List (List Nat) := (l.toArray.qsort ltL).toList

/-- Unbalanced messages on `bus`: (sent-not-received, received-not-sent) counts. -/
def imbalance (all : List (Nat × Bool × List Nat)) (bus : Nat) : Nat × Nat :=
  let on := all.filter (·.1 == bus)
  let s := sortL ((on.filter (·.2.1)).map (·.2.2))
  let r := sortL ((on.filter (!·.2.1)).map (·.2.2))
  -- merge-diff of sorted lists
  let rec go (fuel : Nat) (a b : List (List Nat)) (x y : Nat) : Nat × Nat :=
    match fuel, a, b with
    | 0, _, _ => (x + a.length, y + b.length)
    | _, [], _ => (x, y + b.length)
    | _, _, [] => (x + a.length, y)
    | f + 1, p :: ps, q :: qs =>
      if p == q then go f ps qs x y else if ltL p q then go f ps (q :: qs) (x + 1) y
      else go f (p :: ps) qs x (y + 1)
  go (s.length + r.length + 1) s r 0 0

def checkedBuses : List (String × Nat) :=
  [("SCMP", B_SCMP), ("SOP", B_SOP), ("SFIN", B_SFIN), ("SINC", B_SINC), ("SPUSH", B_SPUSH),
   ("SSIN", B_SSIN), ("SSOUT", B_SSOUT), ("SSMEM", B_SSMEM), ("SGEN", B_SGEN), ("SSHUF", B_SSHUF),
   ("SCHACHA", B_SCHACHA), ("SPUBB", B_SPUBB), ("SPAR", B_SPAR), ("SDLX", B_SDLX), ("SDG", B_SDG)]

def busImbalance (all : List (Nat × Bool × List Nat)) : List (String × Nat × Nat) :=
  (checkedBuses.map fun (nm, b) => (nm, imbalance all b)).filter fun (_, x, y) => x + y != 0

def pubOfI (I : Input) : InstPub :=
  ⟨I.ids, I.p, I.allowed, I.raw.filter (fun q => !(setBits q.bm).isEmpty), I.seed, I.ash⟩

/-- Expected external traffic: the codec's link INIT sends, public sends, the codec's link
`SFIN` receives and `SDG` receives (budgets are INIT / finalized by `ssdV3` itself). -/
def external (I : Input) (R : Run) (D : DistOut) : List (Nat × Bool × List Nat) :=
  let n := I.ids.length
  ((Gen.Mem.expectedInit I).take (n * n)).map (fun m => (B_SOP, true, m)) ++
  (Gen.Proc.expectedKey I.seed).map (fun m => (B_SPUBB, true, m)) ++
  (Gen.Scan.expectedPar I ++ Gen.Scan.expectedRaw I ++ shardRecs 0 (pubOfI I) ++
    linkRecs 0 (pubOfI I)).map (fun m => (B_SPAR, true, m)) ++
  ((Gen.Mem.expectedFin n R.fin).take (n * n)).map (fun m => (B_SFIN, false, m)) ++
  (List.range (n * n)).map (fun l => (B_SDG, false, [0, l, b2n I.allowed[l]!, D.gb[l]!]))

/-- The renderer of `Sched/Render.lean` gives the same public records. -/
def renderAgrees (I : Input) : Bool :=
  let P := pubOfI I
  keyRecs 0 I.seed == Gen.Proc.expectedKey I.seed &&
  (if P.raw.isEmpty then [] else [parScan 0 P]) == Gen.Scan.expectedPar I &&
  rawRecs 0 P == Gen.Scan.expectedRaw I

def tablesOf (R : Run) (D : DistOut) : Except String (List Tab) := do
  let (calls, res) ← Gen.Lane.genCalls R
  let ws := Gen.Lane.words R
  let insts := Gen.Lane.shufInsts R
  return [
    ⟨"scpV3", Gen.Cmp.trace (R.cmps ++ D.cmps), Cmp.constraints.toArray, Cmp.interactions B_SCMP⟩,
    ⟨"smmV3", Gen.Mem.trace R, Mem.constraints.toArray, Mem.interactions⟩,
    ⟨"ssdV3", sdTrace R D, ScanDist.constraints.toArray, ScanDist.interactions⟩,
    ⟨"sprV3", Gen.Proc.trace R, Proc.constraints.toArray, Proc.interactions⟩,
    ⟨"shufV3", Gen.Lane.shufTrace insts, ZkFormal.Chacha.Shuffle.Table.constraints.toArray,
      ZkFormal.Chacha.Shuffle.Table.interactions B_SSIN B_SSOUT B_SSMEM B_SGEN B_SSHUF⟩,
    ⟨"genV3", Gen.Lane.genTrace (Gen.Lane.genRows calls res fun k => ws.getD k 0),
      ZkFormal.Chacha.Rng.Table.constraints.toArray, ZkFormal.Chacha.Rng.Table.interactions B_SCHACHA B_SGEN⟩,
    ⟨"chachaV3", Gen.Lane.chachaTrace (Gen.Lane.chachaRows (Gen.Lane.chachaReqs R)),
      ZkFormal.Chacha.Table.constraints.toArray, ZkFormal.Chacha.Table.interactions B_SCHACHA⟩ ]

/-! ## Fast lane rows = lane generators (sample) -/

def laneCrossCheck (R : Run) : Except String (Nat × Nat × Nat) := do
  let insts := (Gen.Lane.shufInsts R).filter (·.vals.length ≤ 6) |>.take 3
  let rows := Gen.Lane.shufRows insts
  let lane := ZkFormal.Chacha.Shuffle.Gen.honestRows insts
  let mut nS := 0
  for r in List.range rows.size do
    for c in List.range ZkFormal.Chacha.Shuffle.Table.width do
      if rows[r]![c]! != ZkFormal.Chacha.Shuffle.Gen.rowCell (lane.getD r .pad) r c then
        throw s!"shuf row {r} col {c}"
      nS := nS + 1
  let (calls, res) ← Gen.Lane.genCalls R
  let calls := calls.take 4
  let ws := Gen.Lane.words R
  let grows := Gen.Lane.genRows calls (res.take 4) fun k => ws.getD k 0
  let glane := ZkFormal.Chacha.Rng.Gen.honestRows calls
  let mut nG := 0
  for r in List.range grows.size do
    for c in List.range ZkFormal.Chacha.Rng.Table.width do
      if grows[r]![c]! != ZkFormal.Chacha.Rng.Gen.rowCell (glane.getD r .pad) c then
        throw s!"gen row {r} col {c}"
      nG := nG + 1
  let reqs := (Gen.Lane.chachaReqs R).take 1
  let crows := Gen.Lane.chachaRows reqs
  let clane := ZkFormal.Chacha.Gen.honestRows reqs
  let mut nC := 0
  for r in [0, 1, 2, 9, 45, 81, 82, 83, 85] do
    if r < crows.size then
      for c in List.range ZkFormal.Chacha.Table.width do
        if crows[r]![c]! != ZkFormal.Chacha.Gen.rowCell (clane.getD r .pad) c then
          throw s!"chacha row {r} col {c}"
        nC := nC + 1
  return (nS, nG, nC)

/-! ## Main -/

def mutate (T : Tab) (r c : Nat) : Tab :=
  { T with tr := ⟨T.tr.log, fun t r' c' => if r' == r && c' == c then T.tr.cell t r' c' + 1 else T.tr.cell t r' c'⟩ }

def main (args : List String) : IO UInt32 := do
  let limit := (args.head?.bind String.toNat?).getD 600
  let t0 ← IO.monoMsNow
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "../oracle/fixtures/v3/vectors/scheduler.json"))
  let cases := (getArr j "cases").toList.take limit
  let mut okV := 0
  let mut badV := 0
  let mut viol : Array Nat := Array.replicate 7 0
  let mut rowsTot : Array Nat := Array.replicate 7 0
  let mut badBitsTot := 0
  let mut imbTot := 0
  let mut renderBad := 0
  let mut largest : Nat × Nat × List Nat := (0, 0, [])
  let mut crossDone := false
  let mut idx := 0
  for c in cases do
    idx := idx + 1
    let I ← match inputOf c with
      | .ok I => pure I
      | .error e => IO.println s!"vector {idx - 1}: input {e}"; badV := badV + 1; continue
    let R ← match run I with
      | .ok R => pure R
      | .error e => IO.println s!"vector {idx - 1}: run {e}"; badV := badV + 1; continue
    if !renderAgrees I then renderBad := renderBad + 1
    if !crossDone && R.rounds.any (fun rd => 3 ≤ rd.Lr && rd.Lr ≤ 6) then
      match laneCrossCheck R with
      | .ok (a, b, d) => IO.println s!"fast lane rows = lane generators (vector {idx - 1}): shuf {a}, gen {b}, chacha {d} cells"
      | .error e => IO.println s!"LANE MISMATCH: {e}"; badV := badV + 1
      crossDone := true
    let D ← match distRows I R with
      | .ok D => pure D
      | .error e => IO.println s!"vector {idx - 1}: dist {e}"; badV := badV + 1; continue
    let tabs ← match tablesOf R D with
      | .ok ts => pure ts
      | .error e => IO.println s!"vector {idx - 1}: tables {e}"; badV := badV + 1; continue
    let mut good := true
    let mut all := external I R D
    let mut i := 0
    for T in tabs do
      let v := violations T
      if !v.isEmpty then
        good := false
        IO.println s!"vector {idx - 1}: {T.name} {v.length} violations, first {v.take 5}"
      viol := viol.modify i (· + v.length)
      let (ms, bb) := msgs T
      if bb != 0 then good := false; IO.println s!"vector {idx - 1}: {T.name} {bb} non-0/1 mult bits"
      badBitsTot := badBitsTot + bb
      all := all ++ ms
      i := i + 1
    let imb := busImbalance all
    if !imb.isEmpty then
      good := false
      IO.println s!"vector {idx - 1}: imbalance {imb}"
      imbTot := imbTot + (imb.map fun (_, x, y) => x + y).sum
    -- rows (unpadded) per table
    let rs : List Nat := [R.cmps.length + D.cmps.length, (Gen.Mem.rows R).size, (sdRows R D).size,
      (Gen.Proc.rows R).size, (R.rounds.map (·.Lr)).sum, 0, 86 * ((R.kfin + 15) / 16)]
    let hs := tabs.map Tab.h
    rowsTot := (rowsTot.toList.zip hs).toArray.map fun (a, b) => a + b
    if rs.sum > largest.2.1 then largest := (idx - 1, rs.sum, hs)
    if good then okV := okV + 1 else badV := badV + 1
  let t1 ← IO.monoMsNow
  IO.println s!"vectors: {okV} ok, {badV} bad; time {(t1 - t0) / 1000}s"
  IO.println s!"tables: {["scpV3", "smmV3", "ssdV3", "sprV3", "shufV3", "genV3", "chachaV3"]}"
  IO.println s!"violations per table: {viol.toList}; non-0/1 mult bits {badBitsTot}; unbalanced messages {imbTot}"
  IO.println s!"padded rows per table (sum over vectors): {rowsTot.toList}"
  IO.println s!"render (Sched/Render keyRecs/parScan/rawRecs) disagreements: {renderBad}"
  IO.println s!"largest vector {largest.1}: unpadded rows {largest.2.1}, padded heights {largest.2.2}"
  -- mutants on the largest vector
  let c := (cases.toArray)[largest.1]!
  let I ← IO.ofExcept (inputOf c)
  let R ← IO.ofExcept (run I)
  let D ← IO.ofExcept (distRows I R)
  let tabs ← IO.ofExcept (tablesOf R D)
  let base := tabs.map fun T => (msgs T).1
  let ext := external I R D
  let d0 := (Gen.Scan.rows R).size
  let lastEntry := (Gen.Proc.rows R).size - 1
  let scanLast := (Gen.Scan.rows R).size - 1
  let memRows := (Gen.Mem.rows R).size
  -- (table index, row, column)
  let probes : List (Nat × Nat × Nat) :=
    [ (0, 0, Cmp.colX), (0, 0, Cmp.colB), (0, 1, Cmp.colD 3), (0, R.cmps.length + D.cmps.length, Cmp.colAct),
      (1, 0, Mem.v), (1, 1, Mem.t), (1, 1, Mem.vin), (1, 2, Mem.ok), (1, memRows - 1, Mem.w),
      (1, memRows - 1, Mem.lst), (1, 0, Mem.addr), (1, memRows, Mem.act),
      (2, 0, Scan.base), (2, 1, Scan.b0), (2, 3, Scan.q 0), (2, 5, Scan.cur), (2, 20, Scan.key),
      (2, 20, Scan.us0), (2, 1, Scan.s), (2, scanLast, Scan.m), (2, 7, Scan.rb0 2),
      (2, 0, Scan.chi), (2, 20, Scan.bvz), (2, 7, Dist.r1), (2, d0, Dist.q2), (2, d0, Dist.adr),
      (2, d0, Dist.bv), (2, d0, Dist.shd),
      (3, 0, Proc.sbIn), (3, 3, Proc.colL 0), (3, 16, Proc.K), (3, 16, Proc.kq), (3, 17, Proc.ein),
      (3, 17, Proc.eout), (3, 17, Proc.alOut), (3, 17, Proc.ok), (3, 17, Proc.cx), (3, 17, Proc.zn),
      (3, lastEntry, Proc.rem), (3, lastEntry + 1, Proc.Tq), (3, 16, Proc.T),
      (4, 0, ZkFormal.Chacha.Shuffle.Table.colV0), (5, 0, 21), (6, 0, 0) ]
  let mut caught := 0
  let mut missed := []
  for (ti, r, col) in probes do
    let T := mutate tabs[ti]! r col
    let h := T.h
    let v := checkRows T [(r + h - 1) % h, r]
    let ms := (msgs T)
    let all := ext ++ ((List.range tabs.length).flatMap fun k => if k == ti then ms.1 else base[k]!)
    let imb := busImbalance all
    if !v.isEmpty || ms.2 != 0 || !imb.isEmpty then caught := caught + 1
    else missed := (tabs[ti]!.name, r, col) :: missed
  IO.println s!"mutants caught {caught}/{probes.length}, missed {missed.reverse}"
  let t2 ← IO.monoMsNow
  IO.println s!"total time {(t2 - t0) / 1000}s"
  return (if badV == 0 && missed.isEmpty then 0 else 1)
