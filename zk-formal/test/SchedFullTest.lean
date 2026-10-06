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

For each nearcore vector (one instance, τ = 0): the honest traces of `schV3`, `ssdV3` (scan +
distribute, width cut B), `sprV3`, `smmV3`, `scpV3` (codec and merged generators from `Gen/Codec`,
`Gen/Dist`); every constraint on every row, multiplicity bits 0/1, balance of every scheduler bus
that does not involve lane v3-chacha (`SCMP`, `SOP`, `SFIN`, `SINC`, `SPUSH`, `SDL`, `SDLX`,
`SDG`) against the public records of `Sched/Render` (`SPUBB`, `SPAR`, `SDL`) and the
expected external traffic: `VBYTES` = the canonical previous state's bytes, **`SPOST` = the
bytes of `runCore`'s new state**, SHA input `prev hash ‖ sha256(all_shards)` and its digest,
`S0F`. (The shuffle buses are checked with lane v3-chacha's tables in `SchedTablesTest`.)
Forwarding demands: half of each grant of sender 0. Then single-cell mutants of codec and
merged scan/distribute rows. -/

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

/-- Duplicate-id mode: shard id 1 is replaced by shard id 0 (a non-identity source map). -/
def dupIds (dup : Bool) (ids : List Nat) : List Nat :=
  if dup && ids.length ≥ 2 then ids.set 1 (ids.getD 0 0) else ids

def inputOf (c : Json) (dup : Bool := false) : Except String Input := do
  let some ids := decodeShardLayoutV2 (unhex (getStr c "shard_layout_borsh")) | throw "layout"
  let ids := dupIds dup ids
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
   ("SPUBB", B_SPUBB), ("SPAR", B_SPAR),
   ("SDL", B_SDL), ("SDLX", B_SDLX), ("SDG", B_SDG), ("S0F", B_S0F), ("SPOST", B_SPOST), ("SPLEN", B_SPLEN), ("SA0", B_SA0),
   ("VBYTES", ZkFormal.NearV3.B_VBYTES), ("BYTES", ZkFormal.Near.B_BYTES), ("DIGEST", ZkFormal.Near.B_DIGEST)]

def busImbalance (all : List (Nat × Bool × List Nat)) : List (String × Nat × Nat) :=
  (checkedBuses.map fun (nm, b) => (nm, imbalance all b)).filter fun (_, x, y) => x + y != 0

structure Full where
  tabs : List Tab
  ext : List (Nat × Bool × List Nat)
  post : List Nat

def fullOf (c : Json) (dup : Bool := false) : Except String Full := do
  let I ← inputOf c dup
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
  let ids := dupIds dup ids
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
    ⟨"ssdV3", sdTrace R D, ScanDist.constraints.toArray, ScanDist.interactions⟩,
    ⟨"sprV3", Gen.Proc.trace R, Proc.constraints.toArray, Proc.interactions⟩,
    ⟨"smmV3", Gen.Mem.trace R, Mem.constraints.toArray, Mem.interactions⟩,
    ⟨"scpV3", Gen.Cmp.trace cmps, Cmp.constraints.toArray, Cmp.interactions B_SCMP⟩ ]
  let P : InstPub := ⟨I.ids, I.p, I.allowed, I.raw.filter (fun q => !(setBits q.bm).isEmpty), I.seed, I.ash⟩
  let pubSends : List (Nat × List (List Nat)) :=
    [(B_SPUBB, keyRecs 0 I.seed ++ ashRecs 0 I.ash ++ fwdRecs P fwd),
     (B_SPAR, [parCodec 0 P] ++ (if P.raw.isEmpty then [] else [parScan 0 P]) ++ rawRecs 0 P ++
        shardRecs 0 P ++ linkRecs 0 P),
     (B_SDL, dlRecs 0 I.ids)]
  let ext : List (Nat × Bool × List Nat) :=
    (pubSends.flatMap fun (b, l) => l.map fun m => (b, true, m)) ++
    (dlRecs 1 I.ids).map (fun m => (B_SDL, false, m)) ++
    [(B_S0F, true, [0, b2n present, vidV]), (B_SPLEN, false, [0, C.post.length])] ++
    (if present then (List.range C.pre.length).map fun p => (ZkFormal.NearV3.B_VBYTES, false, [vidV, p, C.pre[p]!]) else []) ++
    (List.range C.post.length).map (fun p => (B_SPOST, false, [0, p, C.post[p]!])) ++
    (List.range 64).map (fun j => (ZkFormal.Near.B_BYTES, false, [Codec.K_SCH, j, C.shaIn[j]!])) ++
    [(ZkFormal.Near.B_DIGEST, true, [Codec.K_SCH, 64] ++ C.digest)] ++
    -- the shuffle buses are lane v3-chacha's: take the process table's own messages as matched
    []
  return ⟨tabs, ext, C.post⟩

def shuffleBuses : List Nat := [B_SSIN, B_SSOUT, B_SSMEM, B_SGEN, B_SSHUF, B_SCHACHA]

/-! ## `isL` mutants (`smmV3`): flip `isL` on a whole segment -/

def cellN (T : Tab) (r c : Nat) : Nat := (T.tr.cell 0 r c).toNat

/-- The last row of the segment whose `INIT` row is `f` (the first `lst` row from `f`). -/
def segEnd (T : Tab) (f : Nat) : Nat :=
  (((List.range (T.h - f)).find? fun d => cellN T (f + d) Mem.lst == 1).map (f + ·)).getD f

/-- The first `INIT` row with `isL = l` whose segment has no GRANT row (else the first with `isL = l`):
without GRANTs nothing but the `INIT` row's `c` / message can see the flag. -/
def initRowOf (T : Tab) (l : Nat) : Option Nat :=
  let fs := (List.range T.h).filter fun r => cellN T r Mem.fst == 1 && cellN T r Mem.isL == l
  match fs.find? (fun f => (List.range (segEnd T f + 1 - f)).all fun d => cellN T (f + d) Mem.isGr == 0) with
  | some f => some f
  | none => fs.head?

/-- Flip `isL` on every row of the segment of `f` (so the carried-value constraints still hold);
with `pin`, also set the `INIT` row's `c` to the new `isL` (so `fst·(c − isL) = 0` holds). -/
def flipIsL (T : Tab) (f : Nat) (pin : Bool) : Tab :=
  let e := segEnd T f
  { T with tr := ⟨T.tr.log, fun t r c =>
      if f ≤ r ∧ r ≤ e ∧ c = Mem.isL then 1 - T.tr.cell t r c
      else if pin ∧ r = f ∧ c = Mem.cc then 1 - T.tr.cell t r Mem.isL
      else T.tr.cell t r c⟩ }

open ZkFormal.Chacha.Table.E in
/-- The memory constraints before the fix (`fst·c = 0` on `INIT` rows). -/
def oldMemCs : Array Expr := Mem.constraints.toArray.map fun e =>
  if e == Expr.mul (c Mem.fst) (sub (c Mem.cc) (c Mem.isL)) then Expr.mul (c Mem.fst) (c Mem.cc) else e

/-- The rows `f − 1 … e + 1` around a segment (cyclically). -/
def segRowsAround (T : Tab) (f : Nat) : List Nat :=
  (List.range (segEnd T f + 3 - f)).map fun d => (f + d + T.h - 1) % T.h

/-- The `isL` probes on the memory table `TM`: a link and a budget segment, each flipped unpinned
(caught by `fst·(c − isL)`) and pinned (`c` := new `isL`: caught by the `SOP` INIT message);
`others` = the expected external traffic and the other tables' messages. Also prints the old
table's (`fst·c = 0`) local verdict on the unpinned flip, to show the gap the probe covers. -/
def isLProbes (TM : Tab) (others : List (Nat × Bool × List Nat)) : IO (Nat × Nat × List String) := do
  let mut caught := 0
  let mut tot := 0
  let mut missed : List String := []
  for (lbl, l) in [("link", 1), ("budget", 0)] do
    let some f := initRowOf TM l
      | IO.println s!"isL mutant: no {lbl} INIT row"; missed := s!"{lbl}: no INIT row" :: missed; continue
    let e := segEnd TM f
    let grants := ((List.range (e + 1 - f)).filter fun d => cellN TM (f + d) Mem.isGr == 1).length
    let rows := segRowsAround TM f
    let O := flipIsL TM f false
    -- the old table: `fst·c = 0`, and the old generator's `c = 0` on every INIT row
    let oTr : Trace Fp := ⟨O.tr.log, fun t r c => if c = Mem.cc ∧ O.tr.cell t r Mem.fst = 1 then 0 else O.tr.cell t r c⟩
    let O : Tab := { O with cs := oldMemCs, tr := oTr }
    IO.println s!"isL {lbl} segment rows {f}..{e} ({grants} GRANT rows): old table (fst·c = 0) local violations {(checkRows O rows).length}"
    for pin in [false, true] do
      tot := tot + 1
      let T := flipIsL TM f pin
      let v := checkRows T rows
      let ms := msgs T
      let imb := busImbalance (others ++ ms.1)
      IO.println s!"  isL mutant {lbl} pin={pin}: local violations {v.length}, mult bits {ms.2}, imbalance {imb}"
      if !v.isEmpty || ms.2 != 0 || !imb.isEmpty then caught := caught + 1
      else missed := s!"{lbl} pin={pin}" :: missed
  return (caught, tot, missed.reverse)

def mutate (T : Tab) (r c : Nat) : Tab :=
  { T with tr := ⟨T.tr.log, fun t r' c' => if r' == r && c' == c then T.tr.cell t r' c' + 1 else T.tr.cell t r' c'⟩ }

def main (args : List String) : IO UInt32 := do
  let limit := (args.head?.bind String.toNat?).getD 600
  let t0 ← IO.monoMsNow
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "../oracle/fixtures/v3/vectors/scheduler.json"))
  let cases := (getArr j "cases").toList.take limit
  let mut okV := 0
  let mut badV := 0
  let mut viol : Array Nat := Array.replicate 5 0
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
  -- duplicate-id layouts (shard id 1 := shard id 0): non-identity source map, spec semantics
  let mut dupOk := 0
  let mut dupBad := 0
  let mut dupNonId := 0
  for c in cases do
    let some ids := decodeShardLayoutV2 (unhex (getStr c "shard_layout_borsh")) | continue
    if ids.length < 2 then continue
    let ids' := dupIds true ids
    if (List.range (ids'.length * ids'.length)).any (fun l => srcOf ids' l != some l) then dupNonId := dupNonId + 1
    match fullOf c true with
    | .error e => dupBad := dupBad + 1; if dupBad ≤ 5 then IO.println s!"dup: {e}"
    | .ok F =>
      let mut good := true
      let mut all := F.ext
      for T in F.tabs do
        if !(violations T).isEmpty then good := false
        let (ms, bb) := msgs T
        if bb != 0 then good := false
        all := all ++ ms.filter fun m => !shuffleBuses.contains m.1
      if !(busImbalance all).isEmpty then
        good := false
        if dupBad ≤ 5 then IO.println s!"dup imbalance {busImbalance all}"
      if good then dupOk := dupOk + 1 else dupBad := dupBad + 1
  IO.println s!"duplicate-id layouts: {dupOk} ok, {dupBad} bad ({dupNonId} with a non-identity source map)"
  IO.println s!"violations per table (schV3, ssdV3, sprV3, smmV3, scpV3): {viol.toList}"
  -- mutants of codec rows and of the merged table's scan / distribute rows
  let some c := sample | return (if badV == 0 then 0 else 1)
  let F ← IO.ofExcept (fullOf c)
  let base := F.tabs.map fun T => (msgs T).1
  -- rows by kind (first record allowance-field end, first shard row, first header, first allowed cell)
  let dRows := (F.tabs[1]!).tr
  let findRow (T : Tab) (col : Nat) : Nat :=
    ((List.range T.h).find? fun r => (T.tr.cell 0 r col).toNat == 1).getD 0
  let rend := findRow F.tabs[0]! Codec.rend
  let d0 := findRow F.tabs[1]! Dist.kSh
  let hdr := findRow F.tabs[1]! Dist.kGH
  let cell := ((List.range (F.tabs[1]!).h).find? fun r =>
    (dRows.cell 0 r Dist.kC).toNat == 1 && (dRows.cell 0 r Dist.al).toNat == 1).getD (hdr + 1)
  let hasScan := (dRows.cell 0 0 Dist.kP).toNat == 1
  let probes : List (Nat × Nat × Nat) :=
    [ (0, 0, Codec.reg 1), (0, 1, Codec.bpost), (0, 5, Codec.bpost), (0, 6, Codec.bpre), (0, rend - 4, Codec.bpost),
      (0, rend - 6, Codec.ap), (0, rend - 3, Codec.cb), (0, rend, Codec.a2), (0, rend, Codec.afin), (0, rend, Codec.gb),
      (0, rend, Codec.big), (0, rend - 5, Codec.cx), (0, 7, Codec.kidx), (0, 3, Codec.reg 5),
      (1, d0, Dist.q2), (1, d0, Dist.L2), (1, d0, Dist.kp), (1, d0 + 1, Dist.r), (1, d0 + 1, Dist.da), (1, d0, Dist.cx),
      (1, hdr, Dist.N2), (1, hdr, Dist.b), (1, cell, Dist.gb), (1, cell, Dist.sL), (1, cell, Dist.llo),
      (1, cell, Dist.al), (1, cell, Dist.q1), (1, cell, Dist.N1),
      -- cut B: record / memory windows, section boundary
      (1, d0, Dist.shd), (1, d0, Dist.lnk), (1, d0, Dist.llo), (1, d0, Dist.adr), (1, d0, Dist.bv),
      (1, d0, Dist.by1), (1, d0, Dist.side), (1, cell, Dist.alc), (1, cell, Dist.side), (1, d0, Dist.kSh),
      (1, d0, Dist.r1), (1, d0 + 1, Dist.lhi) ] ++
    (if hasScan then [ (1, 0, Scan.chi), (1, 0, Scan.s), (1, 0, Scan.q 1), (1, 1, Scan.clo), (1, 1, Scan.q 4),
      (1, 20, Scan.key), (1, 20, Scan.bvz), (1, 20, Scan.cid), (1, 20, Dist.r1), (1, d0 - 1, Scan.re),
      (1, d0 - 1, Scan.m) ] else [])
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
  let others := F.ext ++ ((List.range F.tabs.length).flatMap fun k =>
    if k == 3 then [] else base[k]!.filter fun m => !shuffleBuses.contains m.1)
  let (lc, lt, lm) ← isLProbes F.tabs[3]! others
  IO.println s!"isL mutants caught {lc}/{lt}, missed {lm}"
  IO.println s!"mutants caught {caught + lc}/{probes.length + lt}, missed {missed.reverse}"
  let t2 ← IO.monoMsNow
  IO.println s!"total time {(t2 - t0) / 1000}s"
  return (if badV == 0 && dupBad == 0 && missed.isEmpty && lm.isEmpty then 0 else 1)
