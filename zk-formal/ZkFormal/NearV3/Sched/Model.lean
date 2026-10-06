import NearSpecV3.PrepD0
import ZkFormal.NearV3.Sched.Spec.CanonDup

/-!
# ZkFormal.NearV3.Sched.Model — the scheduler core as the AIR computes it (executable)

Lane `v3-sched`. `NearSpecV3.Scheduler.runCore pub prev` reorganised into the phases the AIR
tables implement (STATUS-V3-SCHED §2–§3). Everything here is executable; the event model is
checked against `runCore` on the 600 nearcore vectors (`test/SchedModelTest.lean`) and its
phases are proved equal to the spec in `Sched/Spec/*`.

* **raw requests** `RawReq = (s, r, bitmap)` with shard *indices* (unknown senders/receivers are
  dropped natively); `incsOf` = differences of `requestValues` over the set bits.
* **link pass** (closed form): `a1 = min(a0 + fair, MA)`, `a2 = allowed ? a1 − base : a1`,
  `g = allowed·base`, budgets `MSB − base·#allowed`.
* **process** as rounds over a push log `Push = (ts, key, z, v = rid·64 + j)`: the round key is
  the largest pending key; its bucket is every pending push with that key in `ts` order; the
  model *checks* that re-pushes go to a smaller key (or 0 → 0 with `z + 1`).
* **distribute** on the grid of (sorted sender, sorted receiver) with the model *checking* that
  no `break` happens; sort key `avg·64 + idx`.
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler NearSpec

instance : Inhabited Req := ⟨⟨0, []⟩⟩

/-- `runCore` with the converted request list given explicitly (`runCore` converts the raw
requests with `convertRaw`; `Spec/Conv.convertRequests_eq_convRaw` relates it to `convRaw`). -/
def coreOf (ids : List Nat) (p : Params) (allowed : Array Bool) (reqs : List Req)
    (seed allShardsHash : Bytes) (prevState : Option Bytes) : Option Output := do
  let prev ← match prevState with
    | none => some NearSpec.Bandwidth.State.initial
    | some b => NearSpec.Bandwidth.State.decode b
  let n := ids.length
  let links := List.range (n * n)
  let allow0 := prev.links.foldl (fun (a : Array Nat) la =>
      match indexOf ids la.sender, indexOf ids la.receiver with
      | some s, some r => a.set! (s * n + r) la.allowance
      | _, _ => a) (Array.replicate (n * n) 0)
  let st : St := ⟨Array.replicate n p.maxShardBandwidth, Array.replicate n p.maxShardBandwidth,
    allow0, Array.replicate (n * n) 0, Rng.ofSeed seed⟩
  let fair := p.maxShardBandwidth / n
  let st := { st with allowance := st.allowance.map fun a => Nat.min (Nat.min (a + fair) u64Max) p.maxAllowance }
  let st := links.foldl (fun st l => (tryGrant n allowed st l p.base).2) st
  let st ← processRequests n allowed st reqs
  let st := distribute n allowed st
  let sid (i : Nat) : Nat := ids.getD i 0
  let newLinks : List NearSpec.Bandwidth.LinkAllowance :=
    links.map fun l => ⟨sid (l / n), sid (l % n), st.allowance[l]!⟩
  let newState : NearSpec.Bandwidth.State := ⟨newLinks, sha256 (prev.sanityHash ++ allShardsHash)⟩
  some ⟨newState.encode, links.map fun l => ((sid (l / n), sid (l % n)), st.granted[l]!), p⟩

theorem runCore_eq (pub : SchedPub) (prev : Option Bytes) :
    runCore pub prev = coreOf pub.ids pub.params pub.allowed
      (convertRaw pub.values pub.params.base pub.ids pub.raw) pub.seed pub.allShardsHash prev := rfl

/-! ## Requests: raw form and set bits -/

/-- A request with resolved shard indices `(s, r)` and its 5-byte bitmap. -/
structure RawReq where
  s : Nat
  r : Nat
  bm : List UInt8
  deriving DecidableEq, Repr

/-- Positions `< 40` of the set bits, ascending. -/
def setBits (bm : List UInt8) : List Nat := (List.range 40).filter (getBit bm)

/-- Increases from the value table over the set bits (`prev` = value of the last set bit). -/
def incsFrom (vals : List Nat) : Nat → List Nat → List Nat
  | _, [] => []
  | prev, c :: cs => (vals.getD c 0 - prev) :: incsFrom vals (vals.getD c 0) cs

def incsOf (p : Params) (bm : List UInt8) : List Nat := incsFrom (requestValues p) p.base (setBits bm)

/-- The converted list as the AIR builds it (requests with no set bit are dropped). -/
def convRaw (p : Params) (n : Nat) (raw : List RawReq) : List Req :=
  raw.filterMap fun q => match incsOf p q.bm with
    | [] => none
    | incs => some ⟨q.s * n + q.r, incs⟩

/-! ## Link pass (closed form) -/

structure LinkPass where
  a2 : Array Nat
  g2 : Array Nat
  sb : Array Nat
  rb : Array Nat
  cntS : Array Nat
  cntR : Array Nat

def linkPass (n : Nat) (p : Params) (allowed : Array Bool) (a0 : Array Nat) : LinkPass :=
  let N := n * n
  let fair := p.maxShardBandwidth / n
  let a1 := fun l => Nat.min (a0[l]! + fair) p.maxAllowance
  let al := fun l => allowed[l]!
  let cntS := (List.range n).map fun s => ((List.range n).filter fun r => al (s * n + r)).length
  let cntR := (List.range n).map fun r => ((List.range n).filter fun s => al (s * n + r)).length
  { a2 := (List.range N).toArray.map fun l => if al l then a1 l - p.base else a1 l
    g2 := (List.range N).toArray.map fun l => if al l then p.base else 0
    sb := cntS.toArray.map fun c => p.maxShardBandwidth - p.base * c
    rb := cntR.toArray.map fun c => p.maxShardBandwidth - p.base * c
    cntS := cntS.toArray, cntR := cntR.toArray }

/-! ## Process: rounds over a push log -/

/-- A push: time stamp, key (allowance at push time), 0-round ordinal `z`, entry `rid·64 + j`. -/
structure Push where
  ts : Nat
  key : Nat
  z : Nat
  v : Nat
  deriving DecidableEq, Repr, Inhabited

/-- One processed step (what a `sprV3` row records). -/
structure Step where
  t : Nat
  v : Nat
  link : Nat
  inc : Nat
  last : Bool
  ok : Bool
  aOut : Nat
  deriving Repr

/-- One round: key, ordinal, bucket (pushes in `ts` order), shuffled entries, steps. -/
structure Round where
  key : Nat
  z : Nat
  bucket : List Push
  shuffled : List Nat
  kstart : Nat
  steps : List Step
  deriving Repr

structure PState where
  sb : Array Nat
  rb : Array Nat
  al : Array Nat
  g : Array Nat
  rng : Rng

def insertTs (p : Push) : List Push → List Push
  | [] => [p]
  | q :: qs => if p.ts < q.ts then p :: q :: qs else q :: insertTs p qs

def sortTs (l : List Push) : List Push := l.foldl (fun acc p => insertTs p acc) []

/-- Run the rounds model. Returns the final state and the rounds, or an error string when a
structural fact of STATUS §2 fails (the test reports it). -/
def processEv (n : Nat) (allowed : Array Bool) (reqs : List Req) (st0 : PState) (fuel : Nat) :
    Except String (PState × List Round) := do
  let R := reqs.length
  let reqA : Array Req := reqs.toArray
  let init : List Push := (List.range R).filterMap fun i =>
    let q : Req := reqA[i]!
    if q.incs.isEmpty then none else
    let k := st0.al[q.link]!
    some ⟨i, k, if k = 0 then 1 else 0, i * 64⟩
  let mut pend := init
  let mut st := st0
  let mut t := R
  let mut rounds : List Round := []
  let mut lastKey : Option (Nat × Nat) := none
  for _ in List.range fuel do
    if pend.isEmpty then break
    let K := pend.foldl (fun m p => Nat.max m p.key) 0
    let bucket := sortTs (pend.filter (·.key == K))
    let z := (bucket.headD default).z
    if !(bucket.all (·.z == z)) then throw "bucket with mixed z"
    if K = 0 && z = 0 then throw "0-round with z = 0"
    if K > 0 && z != 0 then throw "positive round with z ≠ 0"
    match lastKey with
    | some (K', z') =>
      if !(K < K' || (K == 0 && K' == 0 && z == z' + 1)) then throw s!"round order: {K'},{z'} then {K},{z}"
    | none => pure ()
    lastKey := some (K, z)
    pend := pend.filter (·.key != K)
    let vs := bucket.map (·.v)
    let ks := t  -- informational
    match shuffle vs st.rng with
    | none => throw "shuffle fuel"
    | some (sh, rng) =>
      st := { st with rng := rng }
      let mut steps : List Step := []
      for v in sh do
        let rid := v / 64
        let j := v % 64
        let q : Req := reqA[rid]!
        let inc := q.incs.getD j 0
        let last := j + 1 == q.incs.length
        let s := q.link / n
        let r := q.link % n
        let ok := allowed[q.link]! && decide (inc ≤ st.sb[s]!) && decide (inc ≤ st.rb[r]!)
        if ok then
          st := { st with sb := st.sb.set! s (st.sb[s]! - inc), rb := st.rb.set! r (st.rb[r]! - inc),
                          al := st.al.set! q.link (st.al[q.link]! - inc),
                          g := st.g.set! q.link (st.g[q.link]! + inc) }
        let aOut := st.al[q.link]!
        if ok && !last then
          if !(aOut < K || (K == 0 && aOut == 0)) then throw "re-push to a key ≥ the popped key"
          let z' := if aOut = 0 then (if K = 0 then z + 1 else 1) else 0
          pend := pend ++ [⟨t, aOut, z', v + 1⟩]
        steps := steps ++ [⟨t, v, q.link, inc, last, ok, aOut⟩]
        t := t + 1
      rounds := rounds ++ [⟨K, z, bucket, sh, ks, steps⟩]
  if !pend.isEmpty then throw "out of fuel"
  return (st, rounds)

/-! ## Distribute on the sorted grid -/

def avgOf (links left : Nat) : Nat := if links = 0 then 0 else left / links

/-- Indices sorted by the strictly increasing key `avg·64 + idx`. -/
def sortedBy (key : Nat → Nat) (n : Nat) : List Nat :=
  sortByKey key (List.range n)

/-- The grid: for sender position `i`, receiver position `j`: `gb` or none (disallowed).
Errors if a `break` would happen (`links = 0` on an allowed link). -/
def distributeEv (n : Nat) (allowed : Array Bool) (sb rb cntS cntR : Array Nat) :
    Except String (Array Nat × List Nat × List Nat) := do
  let sord := sortedBy (fun s => avgOf cntS[s]! sb[s]!) n
  let rord := sortedBy (fun r => avgOf cntR[r]! rb[r]!) n
  let mut ri : Array (Nat × Nat) := (List.range n).toArray.map fun r => (cntR[r]!, rb[r]!)
  let mut g : Array Nat := Array.replicate (n * n) 0
  for s in sord do
    let mut se := (cntS[s]!, sb[s]!)
    for r in rord do
      let l := s * n + r
      if allowed[l]! then
        let re := ri[r]!
        if se.1 = 0 || re.1 = 0 then throw "distribute break"
        let gb := Nat.min (se.2 / se.1) (re.2 / re.1)
        g := g.set! l gb
        se := (se.1 - 1, se.2 - gb)
        ri := ri.set! r (re.1 - 1, re.2 - gb)
  return (g, sord, rord)

/-! ## The event model end to end -/

structure Ev where
  state : Bytes
  granted : List Nat
  rounds : List Round
  sord : List Nat
  rord : List Nat

/-- `allow0` of a canonical previous state (record `l` holds link `l`). -/
def a0Canon (n : Nat) (prev : NearSpec.Bandwidth.State) : Array Nat :=
  if prev.links.length = n * n then (prev.links.map (·.allowance)).toArray else Array.replicate (n * n) 0

/-- `allow0` of a canonical previous state, read the spec's way (first-index `indexOf`, the
last record wins; `Spec/CanonDup.allow0_src`): record `srcOf ids l` for link `l`. -/
def a0Src (ids : List Nat) (prev : NearSpec.Bandwidth.State) : Array Nat :=
  srcArr ids fun k => (a0Canon ids.length prev)[k]!


def coreEv (ids : List Nat) (p : Params) (allowed : Array Bool) (raw : List RawReq)
    (seed ash : Bytes) (prev : NearSpec.Bandwidth.State) : Except String Ev := do
  let n := ids.length
  let lp := linkPass n p allowed (a0Src ids prev)
  let reqs := convRaw p n raw
  let st0 : PState := ⟨lp.sb, lp.rb, lp.a2, lp.g2, Rng.ofSeed seed⟩
  let (st, rounds) ← processEv n allowed reqs st0 (1 + (reqs.map (·.incs.length)).sum)
  let (gd, sord, rord) ← distributeEv n allowed st.sb st.rb lp.cntS lp.cntR
  let sid (i : Nat) : Nat := ids.getD i 0
  let links := List.range (n * n)
  let newLinks : List NearSpec.Bandwidth.LinkAllowance :=
    links.map fun l => ⟨sid (l / n), sid (l % n), st.al[l]!⟩
  let newState : NearSpec.Bandwidth.State := ⟨newLinks, sha256 (prev.sanityHash ++ ash)⟩
  return ⟨newState.encode, links.map fun l => st.g[l]! + gd[l]!, rounds, sord, rord⟩

end ZkFormal.NearV3.Sched
