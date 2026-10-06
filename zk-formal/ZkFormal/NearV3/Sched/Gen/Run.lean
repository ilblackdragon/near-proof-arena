import ZkFormal.NearV3.Sched.Model
import ZkFormal.NearV3.Sched.Ids
import ZkFormal.NearV3.Sched.Gen.Common
import ZkFormal.Chacha.RngSpec
import ZkFormal.NearV3.Sched.Tables.Proc

/-!
# ZkFormal.NearV3.Sched.Gen.Run — the run data of one scheduler instance (lane `v3-sched`)

From a vector (shard ids, params, allowed matrix, raw requests, seed, canonical previous state)
`run` computes everything the honest traces of `sscV3` / `sprV3` / `smmV3` / `scpV3` (and the
lane v3-chacha shuffle tables) need, for one instance `τ`:

* converted requests `cid = 0, 1, …` (`convRaw` order) with set bits, increases, initial key
  `a2[link]`;
* rounds (`processEv`) with start time `T` (`T0`, then `T + Lr`), RNG positions `kst → kend`
  (32-bit words, chained from 0), bucket entries `(ts, ein)` (initial pushes keep `ts = cid`,
  process times are renamed `t ↦ T0 + (t − R)`), shuffled entries and every in/out value of
  the three memory GRANTs and the re-push;
* memory segments per address `addrOf τ kind idx` (INIT, then ops in time order, final);
* the comparator messages `(x, y, [y ≤ x])` sent by the memory and process tables.

Every quantity is recomputed independently (memory replay, shuffle replay via `genAt`) and
checked against `processEv` / `coreEv`; a disagreement is an error.
-/

namespace ZkFormal.NearV3.Sched.Gen

open NearSpecV3 NearSpecV3.Scheduler ZkFormal.Chacha

instance : Inhabited Step := ⟨⟨0, 0, 0, 0, false, false, 0⟩⟩

/-- One vector: claim-only inputs and the canonical previous state. -/
structure Input where
  ids : List Nat
  p : Params
  allowed : Array Bool
  raw : List RawReq
  seed : List UInt8
  ash : List UInt8
  prev : NearSpec.Bandwidth.State

/-- A converted request (one with a set bit). -/
structure CReq where
  cid : Nat
  s : Nat
  r : Nat
  link : Nat
  bm : List UInt8
  bits : List Nat
  incs : List Nat
  key : Nat
  deriving Repr, Inhabited

/-- One processing step = one entry row of `sprV3`. -/
structure Entry where
  x : Nat
  ts : Nat
  ein : Nat
  eout : Nat
  inc : Nat
  rem : Nat
  s : Nat
  r : Nat
  link : Nat
  sbIn : Nat
  sbOut : Nat
  rbIn : Nat
  rbOut : Nat
  alIn : Nat
  alOut : Nat
  cS : Bool
  cR : Bool
  cL : Bool
  ok : Bool
  push : Bool
  zn : Nat
  deriving Repr, Inhabited

structure RoundD where
  K : Nat
  z : Nat
  T : Nat
  Lr : Nat
  kst : Nat
  kend : Nat
  /-- previous key / ordinal (`KSENT`, 0 for the first round). -/
  Kq : Nat
  zq : Nat
  entries : List Entry
  deriving Repr, Inhabited

/-- A memory op row (READ `op = 1` / GRANT `op = 2`). -/
structure MOp where
  t : Nat
  op : Nat
  vin : Nat
  v : Nat
  wp : Nat
  w : Nat
  inc : Nat
  ok : Bool
  c : Bool
  sf : Bool
  deriving Repr, Inhabited

/-- A memory segment. -/
structure Seg where
  addr : Nat
  isL : Bool
  al : Bool
  /-- INIT: `vin`, `v`, `w` (= `inc`). -/
  vin0 : Nat
  v0 : Nat
  w0 : Nat
  ops : List MOp
  deriving Repr, Inhabited

def Seg.vfin (g : Seg) : Nat := match g.ops.getLast? with | some o => o.v | none => g.v0
def Seg.wfin (g : Seg) : Nat := match g.ops.getLast? with | some o => o.w | none => g.w0

structure Run where
  tau : Nat
  n : Nat
  base : Nat
  D : Nat
  seed : List UInt8
  key : List Nat
  a2 : Array Nat
  conv : List CReq
  /-- `used[cid][j]`: increase `j` of request `cid` is processed. -/
  used : Array (Array Bool)
  rounds : List RoundD
  segs : List Seg
  /-- Comparator messages sent by the memory and process tables, `(x, y, b)`. -/
  cmps : List (Nat × Nat × Nat)
  /-- RNG words drawn in total (= `kend` of the last round). -/
  kfin : Nat
  /-- Final process state (`processEv`). -/
  fin : PState

/-- RNG stream position of a `Rng` state (words drawn). -/
def rngPos (r : Rng) : Nat := r.ctr * 16 - r.buf.length

/-- 16-bit key limb `k` of a 32-byte seed: `seed[2k] + 256·seed[2k+1]`. -/
def keyLimb (seed : List UInt8) (k : Nat) : Nat :=
  (seed.getD (2 * k) 0).toNat + 256 * (seed.getD (2 * k + 1) 0).toNat

/-- Replay a shuffle on the stream of `key` from `k0`: `(shuffled, kend)`. -/
def replayShuffle (key : List Nat) (k0 : Nat) (vals : List Nat) : Except String (List Nat × Nat) := do
  let L := vals.length
  let mut l := vals
  let mut k := k0
  for i in List.range (L - 1) do
    let q := L - 1 - i
    match genAt 64 (q + 1) key k with
    | none => throw "genAt fuel"
    | some (j, k') => l := swapAt l q j; k := k'
  return (l, k)

def check (b : Bool) (msg : String) : Except String Unit := if b then pure () else throw msg

/-- Push records `(ts, key, z, e)` as a sorted list (for multiset comparison). -/
def sortPush (l : List (Nat × Nat × Nat × Nat)) : List (Nat × Nat × Nat × Nat) :=
  (l.toArray.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && (a.2.2.2 < b.2.2.2))).toList

def run (I : Input) (tau : Nat := 0) : Except String Run := do
  let n := I.ids.length
  let p := I.p
  let N := n * n
  let lp := linkPass n p I.allowed (a0Canon n I.prev)
  let al (l : Nat) : Bool := I.allowed[l]!
  -- converted requests
  let mut conv : Array CReq := #[]
  for q in I.raw do
    let bits := setBits q.bm
    if bits.isEmpty then continue
    check (q.bm.length == 5) "bitmap length ≠ 5"
    check (q.s < n && q.r < n) "shard index"
    let link := q.s * n + q.r
    conv := conv.push ⟨conv.size, q.s, q.r, link, q.bm, bits, incsOf p q.bm, lp.a2[link]!⟩
  let reqs := convRaw p n I.raw
  check (reqs == conv.toList.map fun c => ⟨c.link, c.incs⟩) "convRaw differs"
  let R := conv.size
  check (R < 65536) "too many requests"
  let st0 : PState := ⟨lp.sb, lp.rb, lp.a2, lp.g2, Rng.ofSeed I.seed⟩
  let fuel := 1 + (reqs.map (·.incs.length)).sum
  let (stF, mrounds) ← processEv n I.allowed reqs st0 fuel
  -- the end-to-end model
  let ev ← coreEv I.ids p I.allowed I.raw I.seed I.ash I.prev
  check (ev.rounds.length == mrounds.length) "coreEv rounds differ"
  for (a, b) in ev.rounds.zip mrounds do
    check (a.key == b.key && a.z == b.z && a.shuffled == b.shuffled &&
      a.steps.map (fun s => (s.t, s.v, s.ok, s.aOut)) == b.steps.map (fun s => (s.t, s.v, s.ok, s.aOut)))
      "coreEv round differs"
  let key := leWords I.seed
  check (key.length == 8) "seed length"
  -- replay
  let mut sb := lp.sb
  let mut rb := lp.rb
  let mut aa := lp.a2
  let mut gg := lp.g2
  let mut opsL : Array (Array MOp) := Array.replicate N #[]
  let mut opsS : Array (Array MOp) := Array.replicate n #[]
  let mut opsR : Array (Array MOp) := Array.replicate n #[]
  for c in conv do
    let v := aa[c.link]!
    let w := gg[c.link]!
    opsL := opsL.modify c.link (·.push ⟨c.cid + 1, OP_READ, v, v, w, w, 0, false, false, false⟩)
  let tsOf (t : Nat) : Nat := if t < R then t else T0 + (t - R)
  let mut pushes : Array (Nat × Nat × Nat × Nat) :=
    conv.map fun c => (c.cid, c.key, if c.key = 0 then 1 else 0, c.cid * 64)
  let mut bucketsAll : Array (Nat × Nat × Nat × Nat) := #[]
  let mut T := T0
  let mut kpos := 0
  let mut Kq := Proc.KSENT
  let mut zq := 0
  let mut used : Array (Array Bool) := conv.map fun c => Array.replicate c.incs.length false
  let mut rounds : Array RoundD := #[]
  let mut gidx := 0
  for rd in mrounds do
    let L := rd.bucket.length
    check (L ≥ 1 && L < 16384) "bucket size"
    let vals := rd.bucket.map (·.v)
    let (sh, kend) ← replayShuffle key kpos vals
    check (sh == rd.shuffled) "shuffle replay differs"
    check (rd.steps.length == L) "steps ≠ bucket"
    for b in rd.bucket do
      check (b.key == rd.key && b.z == rd.z) "bucket push key/z"
      bucketsAll := bucketsAll.push (tsOf b.ts, b.key, b.z, b.v)
    let mut ents : Array Entry := #[]
    for x in List.range L do
      let st := rd.steps[x]!
      check (st.t == R + gidx) "model time"
      let t := T + x
      let e := sh[x]!
      let cid := e / 64
      let j := e % 64
      check (cid < R) "entry cid"
      let c := conv[cid]!
      check (j < c.incs.length) "entry j"
      used := used.modify cid (·.set! j true)
      let inc := c.incs[j]!
      let rem := c.incs.length - j - 1
      let (s, r, l) := (c.s, c.r, c.link)
      let sbIn := sb[s]!
      let rbIn := rb[r]!
      let alIn := aa[l]!
      let wIn := gg[l]!
      let cS := decide (inc ≤ sbIn)
      let cR := decide (inc ≤ rbIn)
      let cL := al l
      let ok := cS && cR && cL
      let sbOut := if ok then sbIn - inc else sbIn
      let rbOut := if ok then rbIn - inc else rbIn
      let alOut := if ok then alIn - inc else alIn
      let wOut := if ok then wIn + inc else wIn
      sb := sb.set! s sbOut
      rb := rb.set! r rbOut
      aa := aa.set! l alOut
      gg := gg.set! l wOut
      let sfL := decide (inc ≤ alIn)
      opsS := opsS.modify s (·.push ⟨t, OP_GRANT, sbIn, sbOut, 0, 0, inc, ok, cS, cS⟩)
      opsR := opsR.modify r (·.push ⟨t, OP_GRANT, rbIn, rbOut, 0, 0, inc, ok, cR, cR⟩)
      opsL := opsL.modify l (·.push ⟨t, OP_GRANT, alIn, alOut, wIn, wOut, inc, ok, cL, sfL⟩)
      check (st.v == e && st.link == l && st.inc == inc && st.last == (rem == 0) && st.ok == ok &&
        st.aOut == alOut) "step differs from processEv"
      let push := ok && rem != 0
      let zn := if alOut = 0 then rd.z + 1 else 0
      if push then pushes := pushes.push (t, alOut, zn, e + 1)
      let bx := rd.bucket[x]!
      ents := ents.push ⟨x, tsOf bx.ts, bx.v, e, inc, rem, s, r, l, sbIn, sbOut, rbIn, rbOut,
        alIn, alOut, cS, cR, cL, ok, push, zn⟩
      gidx := gidx + 1
    rounds := rounds.push ⟨rd.key, rd.z, T, L, kpos, kend, Kq, zq, ents.toList⟩
    T := T + L
    kpos := kend
    Kq := rd.key
    zq := rd.z
  -- every push is popped exactly once
  check (sortPush pushes.toList == sortPush bucketsAll.toList) "push log ≠ buckets"
  -- final state
  check (sb == stF.sb && rb == stF.rb && aa == stF.al && gg == stF.g) "final state differs"
  check (kpos == rngPos stF.rng) "final RNG position differs"
  -- memory segments
  let mut segs : Array Seg := #[]
  for l in List.range N do
    let b := al l
    segs := segs.push ⟨addrOf tau 0 l, true, b, b2n b, lp.a2[l]!, lp.g2[l]!, opsL[l]!.toList⟩
  for s in List.range n do
    segs := segs.push ⟨addrOf tau 1 s, false, false, 0, lp.sb[s]!, 0, opsS[s]!.toList⟩
  for r in List.range n do
    segs := segs.push ⟨addrOf tau 2 r, false, false, 0, lp.rb[r]!, 0, opsR[r]!.toList⟩
  -- comparator messages
  let cmpOf (x y : Nat) : Nat × Nat × Nat := (x, y, if y ≤ x then 1 else 0)
  let mut cmps : Array (Nat × Nat × Nat) := #[]
  for g in segs do
    let mut tp := 0
    for o in g.ops do
      check (tp < o.t) "memory times not increasing"
      cmps := cmps.push (cmpOf o.t (tp + 1))
      if o.op == OP_GRANT then cmps := cmps.push (cmpOf o.vin o.inc)
      tp := o.t
  for rd in rounds do
    if rd.K != 0 then
      check (rd.K < rd.Kq) "round keys not decreasing"
      cmps := cmps.push (cmpOf rd.Kq (rd.K + 1))
    let es := rd.entries.toArray
    for i in List.range es.size do
      let e := es[i]!
      let cx := if i + 1 = es.size then rd.T else es[i + 1]!.ts
      check (e.ts < cx) "bucket ts order"
      cmps := cmps.push (cmpOf cx (e.ts + 1))
  check (cmps.all fun (x, y, _) => x < 2 ^ 29 && y < 2 ^ 29) "comparison operand ≥ 2^29"
  let D := p.maxSingleGrant - p.base
  check (p.base < 2 ^ 24 && D < 2 ^ 24) "params ≥ 2^24"
  return { tau, n, base := p.base, D, seed := I.seed, key, a2 := lp.a2, conv := conv.toList,
           used, rounds := rounds.toList, segs := segs.toList, cmps := cmps.toList,
           kfin := kpos, fin := stF }

end ZkFormal.NearV3.Sched.Gen
