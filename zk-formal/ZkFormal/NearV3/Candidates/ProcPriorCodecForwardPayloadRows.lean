import ZkFormal.NearV3.Candidates.ProcPriorCodecForwardPayloadCells
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordStep
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecForwardPayloadRows
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecExtra ProcPriorCodecNativeHash ProcPriorCodecForwardPayloadCells

def demand (fwd : List (Nat×Nat)) (k : Nat) : Nat :=
  ((fwd.find? (·.1==k)).map (fun x=>x.2)).getD 0

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000 in
theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vid k f gg : Nat) (s out : State)
    (hk : k<R.n*R.n) (hf : f<3) (hg : gg<8)
    (h : step I R present gb fwd (instanceCells I R present vid) k f gg s=.ok (.yield out)) :
    ∃a,out.1=s.1.push a ∧ (a[fwg]! =0 ∨ (f=2 ∧ gg=7 ∧ R.tau=0 ∧
      a[cx]! =a[gfin]! +a[Codec.gb]! ∧ a[cy]! =demand fwd k ∧ a[cbit]! =1 ∧
      a[fb 0]! =demand fwd k%256 ∧ a[fb 1]! =demand fwd k/256%256 ∧
      a[fb 2]! =demand fwd k/65536%256)) := by
  have hff : f=0 ∨ f=1 ∨ f=2 := by omega
  have hgg : gg=0 ∨ gg=1 ∨ gg=2 ∨ gg=3 ∨ gg=4 ∨ gg=5 ∨ gg=6 ∨ gg=7 := by omega
  rcases hff with rfl|rfl|rfl
  all_goals rcases hgg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [step,check,bind,Except.bind,pure,Except.pure,getElem!_pos,hk] at h
  iterate 4
    all_goals repeat first | split at h | cases h
  all_goals try subst out
  all_goals try (simp only [Except.ok.injEq,ForInStep.yield.injEq] at h; subst out)
  all_goals refine ⟨_,rfl,?_⟩
  all_goals repeat rw [ProcPriorCodecForwardPayloadCells.row I R present vid _ _ _ _ _ _ _ _ (by simp [columns])]
  all_goals simp [SchedSetAll.lookup,initial,baseExtra,startExtra,allowanceExtra,priorExtra,
    wrapExtra,compareExtra,carryExtra,endExtra,forwardExtra,
    ap,apost,big,lowf,wt,nzb,ib,ig2,e2,cb,rend,bF,a1,a2,g2,al,base,afin,gfin,u0g,
    fwg,cx,cy,cbit,cg,pm0,pm1,fb,apR,bigR,a0g,rs,Codec.gb,srcC,hasC,useC,fA,klo,khi,
    List.foldl_append,demand]
  all_goals omega
end ZkFormal.NearV3.Candidates.ProcPriorCodecForwardPayloadRows
