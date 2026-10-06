import Lean.Data.Json
import ZkFormal.NearV3.Sched.Gen.Cmp
import ZkFormal.NearV3.Sched.Gen.Mem
import ZkFormal.NearV3.Sched.Gen.Scan
import ZkFormal.NearV3.Sched.Gen.Proc
import ZkFormal.NearV3.Sched.Gen.Dist
import ZkFormal.NearV3.Sched.Gen.Codec
import ZkFormal.NearV3.Sched.Render

/-! Executable check of all six scheduler tables together (`lake env lean --run test/SchedFullTest.lean [limit]`).
Not part of the library.

For each nearcore vector (one instance, τ = 0): the honest traces of `schV3`, `sscV3`, `sprV3`,
`smmV3`, `scpV3`, `sdsV3` (codec and distribute generators from `Gen/Codec`, `Gen/Dist`); every
constraint on every row, multiplicity bits 0/1, balance of every scheduler bus that does not
involve lane v3-chacha (`SCMP`, `SOP`, `SFIN`, `SINC`, `SPUSH`, `SDL`, `SDLX`, `SDG`) against
the public records of `Sched/Render` (`SPUBB`, `SPAR`, `SRAW`, `SLINK`, `SSHD`, `SDL`) and the
expected external traffic: `VBYTES` = the canonical previous state's bytes, **`SPOST` = the
bytes of `runCore`'s new state**, SHA input `prev hash ‖ sha256(all_shards)` and its digest,
`S0F`. (The shuffle buses are checked with lane v3-chacha's tables in `SchedTablesTest`.)
Forwarding demands: half of each grant of sender 0. Then single-cell mutants of codec and
distribute rows. -/

open Lean NearSpecV3 NearSpecV3.Scheduler ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Sched.Gen

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
   ("SPUBB", B_SPUBB), ("SPAR", B_SPAR), ("SRAW", B_SRAW), ("SLINK", B_SLINK), ("SSHD", B_SSHD),
   ("SDL", B_SDL), ("SDLX", B_SDLX), ("SDG", B_SDG), ("S0F", B_S0F), ("SPOST", B_SPOST),
   ("VBYTES", ZkFormal.NearV3.B_VBYTES), ("BYTES", ZkFormal.Near.B_BYTES), ("DIGEST", ZkFormal.Near.B_DIGEST)]

def busImbalance (all : List (Nat × Bool × List Nat)) : List (String × Nat × Nat) :=
  (checkedBuses.map fun (nm, b) => (nm, imbalance all b)).filter fun (_, x, y) => x + y != 0

structure Full where
  tabs : List Tab
  ext : List (Nat × Bool × List Nat)
  post : List Nat

def fullOf (c : Json) : Except String Full := do
  let I ← inputOf c
  let R ← run I
  let present := (c.getObjValAs? String "prev_state_borsh").isOk
  let vidV := 777
  let D ← distRows I R
  -- forwarding demands: half of each grant of sender 0
  let n := I.ids.length
  let fwd : List (Nat × Nat) := (List.range n).map fun r =>
    let l := r
    let g := ((R.segs.getD l default).wfin) + D.gb[l]!
    (l, g / 2)
  let C ← codecRows I R present vidV D.gb fwd
  -- the spec's new state
  let some ids := decodeShardLayoutV2 (unhex (getStr c "shard_layout_borsh")) | throw "layout"
  let congestion := (getArr c "congestion").toList.map fun x =>
    (getNat x "shard_id", infoOf x, getNat x "missed_chunks_count")
  let reqs := (getArr c "bandwidth_requests").toList.map fun x =>
    (getNat x "shard_id", decodeBandwidthRequests (unhex (getStr x "requests_borsh")))
  let some reqs := reqs.mapM (fun (s, r) => r.map (s, ·)) | throw "requests"
  let some pub := pubOf Config.pv86 CongestionConfig.pv86 ids congestion reqs I.seed | throw "pubOf"
  let prevBytes : Option (List UInt8) := if present then some I.prev.encode else none
  let some out := runCore pub prevBytes | throw "runCore none"
  if C.post != out.state.map (·.toNat) then throw "codec post bytes ≠ runCore state"
  if present && C.pre != I.prev.encode.map (·.toNat) then throw "codec pre bytes ≠ canonical prev"
  let cmps := R.cmps ++ D.cmps ++ C.cmps
  let tabs : List Tab := [
    ⟨"schV3", mkTrace C.rows 1 codecPad, Codec.constraints.toArray, Codec.interactions⟩,
    ⟨"sscV3", Gen.Scan.trace R, Scan.constraints.toArray, Scan.interactions⟩,
    ⟨"sprV3", Gen.Proc.trace R, Proc.constraints.toArray, Proc.interactions⟩,
    ⟨"smmV3", Gen.Mem.trace R, Mem.constraints.toArray, Mem.interactions⟩,
    ⟨"scpV3", Gen.Cmp.trace cmps, Cmp.constraints.toArray, Cmp.interactions B_SCMP⟩,
    ⟨"sdsV3", mkTrace D.rows 1 distPad, Dist.constraints.toArray, Dist.interactions⟩ ]
  let P : InstPub := ⟨I.ids, I.p, I.allowed, I.raw.filter (fun q => !(setBits q.bm).isEmpty), I.seed, I.ash⟩
  let pubSends : List (Nat × List (List Nat)) :=
    [(B_SPUBB, keyRecs 0 I.seed ++ ashRecs 0 I.ash ++ fwdRecs P fwd),
     (B_SPAR, [parCodec 0 P] ++ (if P.raw.isEmpty then [] else [parScan 0 P])),
     (B_SRAW, rawRecs 0 P), (B_SLINK, linkRecs 0 P), (B_SSHD, shardRecs 0 P),
     (B_SDL, dlRecs 0 I.ids)]
  let ext : List (Nat × Bool × List Nat) :=
    (pubSends.flatMap fun (b, l) => l.map fun m => (b, true, m)) ++
    (dlRecs 1 I.ids).map (fun m => (B_SDL, false, m)) ++
    [(B_S0F, true, [0, b2n present, vidV])] ++
    (if present then (List.range C.pre.length).map fun p => (ZkFormal.NearV3.B_VBYTES, false, [vidV, p, C.pre[p]!]) else []) ++
    (List.range C.post.length).map (fun p => (B_SPOST, false, [0, p, C.post[p]!])) ++
    (List.range 64).map (fun j => (ZkFormal.Near.B_BYTES, false, [Codec.K_SCH, j, C.shaIn[j]!])) ++
    [(ZkFormal.Near.B_DIGEST, true, [Codec.K_SCH, 64] ++ C.digest)] ++
    -- the shuffle buses are lane v3-chacha's: take the process table's own messages as matched
    []
  return ⟨tabs, ext, C.post⟩

def shuffleBuses : List Nat := [B_SSIN, B_SSOUT, B_SSMEM, B_SGEN, B_SSHUF, B_SCHACHA]

def mutate (T : Tab) (r c : Nat) : Tab :=
  { T with tr := ⟨T.tr.log, fun t r' c' => if r' == r && c' == c then T.tr.cell t r' c' + 1 else T.tr.cell t r' c'⟩ }

def main (args : List String) : IO UInt32 := do
  let limit := (args.head?.bind String.toNat?).getD 600
  let t0 ← IO.monoMsNow
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "../oracle/fixtures/v3/vectors/scheduler.json"))
  let cases := (getArr j "cases").toList.take limit
  let mut okV := 0
  let mut badV := 0
  let mut viol : Array Nat := Array.replicate 6 0
  let mut idx := 0
  let mut sample : Option Json := none
  for c in cases do
    idx := idx + 1
    let F ← match fullOf c with
      | .ok F => pure F
      | .error e => IO.println s!"vector {idx - 1}: {e}"; badV := badV + 1; continue
    let mut good := true
    let mut all := F.ext
    let mut i := 0
    for T in F.tabs do
      let v := violations T
      if !v.isEmpty then
        good := false
        IO.println s!"vector {idx - 1}: {T.name} {v.length} violations, first {v.take 5}"
      viol := viol.modify i (· + v.length)
      let (ms, bb) := msgs T
      if bb != 0 then good := false; IO.println s!"vector {idx - 1}: {T.name} {bb} non-0/1 mult bits"
      all := all ++ ms.filter fun m => !shuffleBuses.contains m.1
      i := i + 1
    let imb := busImbalance all
    if !imb.isEmpty then
      good := false
      IO.println s!"vector {idx - 1}: imbalance {imb}"
    if good then okV := okV + 1 else badV := badV + 1
    if sample.isNone && idx > 50 then sample := some c
  let t1 ← IO.monoMsNow
  IO.println s!"vectors: {okV} ok, {badV} bad; time {(t1 - t0) / 1000}s"
  IO.println s!"violations per table (schV3, sscV3, sprV3, smmV3, scpV3, sdsV3): {viol.toList}"
  -- mutants of codec and distribute rows
  let some c := sample | return (if badV == 0 then 0 else 1)
  let F ← IO.ofExcept (fullOf c)
  let base := F.tabs.map fun T => (msgs T).1
  let probes : List (Nat × Nat × Nat) :=
    [ (0, 0, Codec.reg 1), (0, 1, Codec.bpost), (0, 5, Codec.bpost), (0, 6, Codec.bpre), (0, 21, Codec.bpost),
      (0, 21, Codec.ap), (0, 23, Codec.cb), (0, 28, Codec.a2), (0, 28, Codec.afin), (0, 28, Codec.gb),
      (0, 28, Codec.big), (0, 28, Codec.cx), (0, 7, Codec.kidx), (0, 3, Codec.reg 5),
      (5, 0, Dist.q2), (5, 0, Dist.L2), (5, 0, Dist.kp), (5, 1, Dist.r), (5, 2, Dist.da), (5, 3, Dist.cx),
      (5, 4, Dist.N1), (5, 5, Dist.gb), (5, 5, Dist.sL), (5, 5, Dist.llo), (5, 5, Dist.al), (5, 4, Dist.b) ]
  let mut caught := 0
  let mut missed := []
  for (ti, r, col) in probes do
    let T := mutate F.tabs[ti]! r col
    if r ≥ T.h then continue
    let h := T.h
    let v := checkRows T [(r + h - 1) % h, r]
    let ms := msgs T
    let all := F.ext ++ ((List.range F.tabs.length).flatMap fun k =>
      (if k == ti then ms.1 else base[k]!).filter fun m => !shuffleBuses.contains m.1)
    let imb := busImbalance all
    if !v.isEmpty || ms.2 != 0 || !imb.isEmpty then caught := caught + 1
    else missed := (F.tabs[ti]!.name, r, col) :: missed
  IO.println s!"mutants caught {caught}/{probes.length}, missed {missed.reverse}"
  let t2 ← IO.monoMsNow
  IO.println s!"total time {(t2 - t0) / 1000}s"
  return (if badV == 0 && missed.isEmpty then 0 else 1)
