import ZkFormal.NearV3.Candidates.ProcPriorCodecLinkGateCells
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordStep
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecNativeLinkGates
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecExtra ProcPriorCodecNativeHash ProcPriorCodecLinkGateCells

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000 in
theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vid k f gg : Nat) (s out : State)
    (hk : k<R.n*R.n) (hf : f<3) (hg : gg<8)
    (h : step I R present gb fwd (instanceCells I R present vid) k f gg s=.ok (.yield out)) :
    ∃a,out.1=s.1.push a ∧ a[a0g]! =a[fA]!*a[e2]!*a[hasC]! ∧ a[u0g]! =a[rend]!*a[useC]! := by
  have hff : f=0 ∨ f=1 ∨ f=2 := by omega
  have hgg : gg=0 ∨ gg=1 ∨ gg=2 ∨ gg=3 ∨ gg=4 ∨ gg=5 ∨ gg=6 ∨ gg=7 := by omega
  rcases hff with rfl|rfl|rfl
  all_goals rcases hgg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [step,check,bind,Except.bind,pure,Except.pure,getElem!_pos,hk] at h
  iterate 4
    all_goals repeat first | split at h | cases h
  all_goals try subst out
  all_goals try (simp only [Except.ok.injEq,ForInStep.yield.injEq] at h; subst out)
  all_goals refine ⟨_,rfl,?_,?_⟩
  all_goals repeat rw [ProcPriorCodecLinkGateCells.row I R present vid _ _ _ _ _ _ _ _ (by simp [columns])]
  all_goals simp [SchedSetAll.lookup,initial,List.foldl_append,columns,baseExtra,startExtra,allowanceExtra,priorExtra,
    wrapExtra,compareExtra,carryExtra,endExtra,forwardExtra,
    ap,apost,big,lowf,wt,nzb,ib,ig2,e2,cb,rend,bF,a1,a2,g2,al,base,afin,gfin,u0g,
    fwg,cx,cy,cbit,cg,pm0,pm1,fb,apR,bigR,a0g,rs,Codec.gb,srcC,hasC,useC,fA,zt]
  all_goals omega
end ZkFormal.NearV3.Candidates.ProcPriorCodecNativeLinkGates
