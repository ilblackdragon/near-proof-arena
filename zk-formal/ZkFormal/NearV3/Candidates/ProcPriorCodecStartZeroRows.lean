import ZkFormal.NearV3.Candidates.ProcPriorCodecStartZeroCells
import ZkFormal.NearV3.Candidates.ProcPriorCodecPlainStep
import ZkFormal.NearV3.Candidates.ProcPriorCodecAllowanceData
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecStartZeroRows
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecExtra ProcPriorCodecNativeHash ProcPriorCodecStartZeroCells

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vid k f gg : Nat) (s out : State)
    (hk : k<R.n*R.n) (hf : f<3) (hg : gg<8)
    (h : step I R present gb fwd (instanceCells I R present vid) k f gg s=.ok (.yield out)) :
    ∃a,out.1=s.1.push a ∧ (f=0 ∧ gg=0 → a[nzb]! =(if k%R.n=0 then 1 else 0) ∧
      a[ig2]! =finv (k%R.n) ∧ a[ib]! =finv (fsub (k%R.n) (R.n-1))) ∧
      (¬(f=0 ∧ gg=0) → a[nzb]! =0) := by
  by_cases hf2:f=2
  · subst f
    obtain ⟨a,ha,_,hz,_⟩:=ProcPriorCodecAllowanceData.cells I R present gb fwd
      (instanceCells I R present vid) k gg s out hg hk h
    exact ⟨a,ha,by simp,fun _=>hz⟩
  · have hfplain:f<2 := by omega
    rw [ProcPriorCodecPlainStep.step_eq I R present gb fwd (instanceCells I R present vid) k f gg s hfplain] at h
    simp only [Except.ok.injEq,ForInStep.yield.injEq] at h
    subst out
    refine ⟨_,rfl,?_,?_⟩
    · intro hs
      obtain ⟨rfl,rfl⟩:=hs
      simpa only [ProcPriorCodecPlainStep.row,ProcPriorCodecStepRows.record,Nat.mul_zero,Nat.add_zero,
        show (0:Nat)<2 from by decide,show (0:Nat)=0 from rfl,and_self,ite_true] using
        (ProcPriorCodecStartZeroCells.start I R present vid k (5+24*k)
          (idByte I.ids k 0) (if ¬present then 0 else idByte I.ids k 0) (b2n I.allowed[k]!) gb[k]!)
    · intro hs
      dsimp only [ProcPriorCodecPlainStep.row,ProcPriorCodecStepRows.record]
      rw [if_neg hs]
      exact ProcPriorCodecStartZeroCells.other I R present vid k f gg _ _ _ _ _
end ZkFormal.NearV3.Candidates.ProcPriorCodecStartZeroRows
