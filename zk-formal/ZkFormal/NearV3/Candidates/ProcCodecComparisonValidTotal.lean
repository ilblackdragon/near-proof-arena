import ZkFormal.NearV3.Candidates.ProcCodecComparisonValidLoops
namespace ZkFormal.NearV3.Candidates.ProcCodecComparisonValidTotal
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Complete
open ZkFormal.NearV3.Assembly.CodecDigest

private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem core (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (hmax:I.p.maxShardBandwidth≤4500000)
    (hgrant:∀k,k<R.n*R.n→(R.segs.getD k default).wfin+gb[k]!≤4500000)
    (h:coreLayout I R present vid gb fwd=.ok out) : ∀q∈out.cmps,CmpOk q := by
  unfold coreLayout at h
  dsimp only at h
  simp only [pure,Except.pure] at h
  rw [push_loop] at h
  simp only [bind,Except.bind] at h
  obtain ⟨mid,hloop,h⟩:=bind_ok h
  rw [push_loop] at h
  simp only [bind,Except.bind] at h
  rw [push_loop] at h
  simp only [bind,Except.bind] at h
  cases h
  apply ExceptLoop.invariant _ _ ProcCodecComparisonValidLoops.Good ?_ _ mid ?_ hloop
  · intro k hk s hs u hu
    exact ProcCodecComparisonValidLoops.block I R present vid gb fwd k s u hmax
      (hgrant k (List.mem_range.mp hk)) hs hu
  · intro q hq
    cases hq

theorem generated (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (hmax:I.p.maxShardBandwidth≤4500000)
    (hgrant:∀k,k<R.n*R.n→(R.segs.getD k default).wfin+gb[k]!≤4500000)
    (h:ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out) :
    ∀q∈out.cmps,CmpOk q := by
  rw [←coreLayout_eq] at h
  cases hc:coreLayout I R present vid gb fwd with
  | error e=>simp [hc,Except.map] at h
  | ok o=>
    simp only [hc,Except.map,Except.ok.injEq] at h
    subst out
    exact core I R present vid gb fwd o hmax hgrant hc
end ZkFormal.NearV3.Candidates.ProcCodecComparisonValidTotal
