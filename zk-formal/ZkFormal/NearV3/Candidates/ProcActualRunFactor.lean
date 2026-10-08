import ZkFormal.NearV3.Candidates.ProcActualPrefix
namespace ZkFormal.NearV3.Candidates.ProcActualRunFactor
open NearSpec NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

/-- The unchanged replay, memory and comparison suffix of ActualRun.run. -/
def runRest (I : Input) (tau : Nat) (conv : Array CReq) (stF : PState)
    (mrounds : List Round) : Except String Run := do
  let n := I.ids.length
  let p := I.p
  let N := n*n
  let lp := linkPass n p I.allowed (ProcActualInput.allowances I.ids I.prev)
  let al (l : Nat) : Bool := I.allowed[l]!
  let R := conv.size
  let key := NearSpecV3.leWords I.seed
  -- replay
  let mut sb := lp.sb
  let mut rb := lp.rb
  let mut aa := lp.a2
  let mut gg := lp.g2
  let mut opsL : Array (Array Gen.MOp) := Array.replicate N #[]
  let mut opsS : Array (Array Gen.MOp) := Array.replicate n #[]
  let mut opsR : Array (Array Gen.MOp) := Array.replicate n #[]
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
  let mut rounds : Array Gen.RoundD := #[]
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
  let mut segs : Array Gen.Seg := #[]
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

/-- Checked decomposition of the full corrected executable. -/
theorem run_eq_prefix (I : Input) (tau : Nat) :
    ActualRun.run I tau = (do
      let (conv,st,rs,_) ← ProcActualPrefix.runPrefix I
      runRest I tau conv st rs) := by
  simp only [ActualRun.run,ProcActualPrefix.runPrefix,runRest,bind_assoc,pure_bind]
theorem run_of_prefix (I : Input) (tau : Nat) (conv : Array CReq) (st : PState)
    (rs : List Round) (ev : Ev)
    (h : ProcActualPrefix.runPrefix I=.ok (conv,st,rs,ev)) :
    ActualRun.run I tau=runRest I tau conv st rs := by
  rw [run_eq_prefix,h]
  rfl

/-- On actual prepared native inputs, full generation reduces to the replay suffix.
No success premise for the prefix or corrected core is supplied. -/
theorem prepared_reduction {cb : Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hp : NearSpecV3.prepD0 cb hint=.ok p) (sp : SchedPub) (hsp : sp∈p.sched)
    (ctx : NearSpecV3.ApplyCtx) (hpub : NearSpecV3.schedPub ctx=some sp)
    (oldBytes : Option Bytes) (out : Output) (hcore : runCore sp oldBytes=some out) (tau : Nat) :
    ∃prev conv st rs ev,ProcActualCore.decodePrevious oldBytes=some prev ∧
      ProcActualPrefix.runPrefix (ProcPreparedSequence.input sp prev)=.ok (conv,st,rs,ev) ∧
      ActualRun.run (ProcPreparedSequence.input sp prev) tau=
        runRest (ProcPreparedSequence.input sp prev) tau conv st rs ∧
      ev.state=out.state ∧ ev.granted=out.granted.map Prod.snd := by
  obtain ⟨prev,conv,st,rs,ev,hprev,hpfx,hstate,hgrants⟩ :=
    ProcActualPrefix.prepared_prefix hp sp hsp ctx hpub oldBytes out hcore
  exact ⟨prev,conv,st,rs,ev,hprev,hpfx,run_of_prefix _ tau conv st rs ev hpfx,hstate,hgrants⟩

end ZkFormal.NearV3.Candidates.ProcActualRunFactor
