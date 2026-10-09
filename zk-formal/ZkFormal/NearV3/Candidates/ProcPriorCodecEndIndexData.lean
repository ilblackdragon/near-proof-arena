import ZkFormal.NearV3.Candidates.ProcPriorCodecStartIndexData
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordIndexRows
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecEndIndexData
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f g : Nat) (s out : State)
    (hk:k<R.n*R.n) (hf:f<3) (hg:g<8)
    (h:step I R present gb fwd (instanceCells I R present vidV) k f g s=.ok (.yield out)) :
    ∃a,out.1=s.1.push a ∧ a[srcC]! =k/R.n ∧ a[useC]! =k%R.n ∧
      a[hasC]! =(if k%R.n+1=R.n then 1 else 0) ∧
      a[rend]! =(if f=2 ∧ g=7 then 1 else 0) ∧
      a[ekl]! =(if k+1=R.n*R.n then 1 else 0) ∧ a[fA]! =(if f=2 then 1 else 0) := by
  obtain ⟨a,ha,hsrc,huse,hhas,_⟩:=ProcPriorCodecStartIndexData.actual I R present gb fwd vidV k f g s out hf hg h
  obtain ⟨b,hb,_,_,_,_,_,hfA,_,_,he7,_,_,_,hekl,_⟩:=ProcPriorCodecRecordZeroRows.actual I R present gb fwd vidV k f g s out hf hg h
  have heq:b=a := Array.push_inj_right.mp (hb.symm.trans ha)
  subst b
  obtain ⟨b,hb,_,_,_,hrend,_⟩:=ProcPriorCodecRecordIndexRows.actual I R present gb fwd vidV k f g s out hk hf hg h
  have heq:b=a := Array.push_inj_right.mp (hb.symm.trans ha)
  subst b
  refine ⟨a,ha,hsrc,huse,hhas,?_,hekl,hfA⟩
  rw [hrend,hfA,he7]
  by_cases hf2:f=2 <;> by_cases hg7:g=7 <;> simp [hf2,hg7]
end ZkFormal.NearV3.Candidates.ProcPriorCodecEndIndexData
