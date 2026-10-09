import ZkFormal.NearV3.Candidates.ProcActualStateReplay
namespace ZkFormal.NearV3.Candidates.ProcActualReplayEntry
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

abbrev Acc := Array Nat × Array Nat × Array Nat × Array Nat ×
  Array (Array Gen.MOp) × Array (Array Gen.MOp) × Array (Array Gen.MOp) ×
  Array (Nat×Nat×Nat×Nat) × Array (Array Bool) × Nat × Array Entry

def state (acc : Acc) (rng : NearSpecV3.Rng) : PState :=
  ⟨acc.1,acc.2.1,acc.2.2.1,acc.2.2.2.1,rng⟩

/-- Entry body extracted from the corrected generator, including all side effects. -/
def step (I : Input) (conv : Array CReq) (rd : Round) (sh : List Nat) (T x : Nat)
    (acc : Acc) : Except String (ForInStep Acc) := do
  let (sb0,rb0,aa0,gg0,opsL0,opsS0,opsR0,pushes0,used0,gidx0,ents0) := acc
  let mut sb := sb0
  let mut rb := rb0
  let mut aa := aa0
  let mut gg := gg0
  let mut opsL := opsL0
  let mut opsS := opsS0
  let mut opsR := opsR0
  let mut pushes := pushes0
  let mut used := used0
  let mut gidx := gidx0
  let mut ents := ents0
  let R := conv.size
  let al (l : Nat) := I.allowed[l]!
  let tsOf (t : Nat) := if t<R then t else T0+(t-R)
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
  return .yield (sb,rb,aa,gg,opsL,opsS,opsR,pushes,used,gidx,ents)

/-- Given the established event and pointer invariants, the real entry body
succeeds even with arbitrary memory-log, used-bit and push accumulators. -/
theorem step_success (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat)
    (T x : Nat) (acc : Acc) (rng : NearSpecV3.Rng)
    (hv : ProcRequestPointers.Valid (ProcActualConversionExact.view cv) sh[x]!)
    (he : rd.steps[x]! =ProcModelEvent.replayEvent I.allowed cv[sh[x]!/64]! sh[x]!
      (cv.size+acc.2.2.2.2.2.2.2.2.2.1) (state acc rng)) :
    ∃out,step I cv rd sh T x acc=.ok (.yield out) := by
  rcases acc with ⟨sb,rb,aa,gg,opsL,opsS,opsR,pushes,used,gidx,ents⟩
  obtain ⟨hi,hj⟩ := ProcActualIndexGuards.view_bounds cv sh[x]! hv
  have hlast : ∀a : Nat,decide (a=0)=(a==0) := by
    intro a
    exact Bool.eq_iff_iff.mpr (by simp)
  dsimp only [ProcModelEvent.replayEvent,state] at he
  unfold step
  simp only [he,hi,hj,check,decide_true,BEq.rfl,
    Bool.true_and,Bool.and_true,hlast,ite_true,bind,Except.bind,pure,Except.pure]
  split <;> exact ⟨_,rfl⟩

end ZkFormal.NearV3.Candidates.ProcActualReplayEntry
