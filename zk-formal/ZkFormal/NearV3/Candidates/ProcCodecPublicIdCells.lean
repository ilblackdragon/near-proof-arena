import ZkFormal.NearV3.Candidates.ProcPriorCodecStartIndexData
import ZkFormal.NearV3.Candidates.ProcPriorCodecStartZeroRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecSenderCells
namespace ZkFormal.NearV3.Candidates.ProcCodecPublicIdCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash

/-- The actual record selector sends once, at receiver zero and sender byte
zero; no uniqueness of IDs is required. -/
theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f g : Nat) (s out : State)
    (hk : k<R.n*R.n) (hf : f<3) (hg : g<8)
    (h : step I R present gb fwd (instanceCells I R present vidV) k f g s=.ok (.yield out)) :
    ∃a,out.1=s.1.push a ∧ a[srcC]! =k/R.n ∧
      a[rs]! =(if f=0 ∧ g=0 then 1 else 0) ∧
      a[nzb]! =(if f=0 ∧ g=0 ∧ k%R.n=0 then 1 else 0) := by
  obtain ⟨a,ha,hsrc,_,_,hrs,_,_,_⟩ :=
    ProcPriorCodecStartIndexData.actual I R present gb fwd vidV k f g s out hf hg h
  obtain ⟨b,hb,hstart,hother⟩ :=
    ProcPriorCodecStartZeroRows.actual I R present gb fwd vidV k f g s out hk hf hg h
  have he : b=a := Array.push_inj_right.mp (hb.symm.trans ha)
  subst b
  refine ⟨a,ha,hsrc,hrs,?_⟩
  by_cases hs : f=0 ∧ g=0
  · rw [(hstart hs).1]
    simp only [hs.1,hs.2,true_and]
  · rw [hother hs]
    have hn : ¬(f=0 ∧ g=0 ∧ k%R.n=0) := fun hh=>hs ⟨hh.1,hh.2.1⟩
    rw [ite_eq_right hn]

theorem position (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<8) :
    out.rows[5+24*k+8*f+g]![srcC]! =k/R.n ∧
      out.rows[5+24*k+8*f+g]![rs]! =(if f=0 ∧ g=0 then 1 else 0) ∧
      out.rows[5+24*k+8*f+g]![nzb]! =(if f=0 ∧ g=0 ∧ k%R.n=0 then 1 else 0) := by
  apply ProcCodecGeneratedRecordPosition.property I R present vidV gb fwd out h k f g hk hf hg
    (fun a=>a[srcC]! =k/R.n ∧ a[rs]! =(if f=0 ∧ g=0 then 1 else 0) ∧
      a[nzb]! =(if f=0 ∧ g=0 ∧ k%R.n=0 then 1 else 0))
  intro before after hs
  exact actual I R present gb fwd vidV k f g before after hk hf hg hs
end ZkFormal.NearV3.Candidates.ProcCodecPublicIdCells
