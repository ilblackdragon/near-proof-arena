import ZkFormal.NearV3.Candidates.ProcPriorCodecControlCells
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordStep
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecTerminalGates
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecExtra ProcPriorCodecNativeHash ProcPriorCodecControlCells

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000 in
theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vid k : Nat) (s out : State)
    (hk : k<R.n*R.n)
    (h : step I R present gb fwd (instanceCells I R present vid) k 2 7 s=.ok (.yield out)) :
    ∃a,out.1=s.1.push a ∧ a[fA]! =1 ∧ a[rend]! =1 ∧ a[e2]! =0 := by
  all_goals simp [step,check,bind,Except.bind,pure,Except.pure,getElem!_pos,hk] at h
  iterate 4
    all_goals repeat first | split at h | cases h
  all_goals try subst out
  all_goals try (simp only [Except.ok.injEq,ForInStep.yield.injEq] at h; subst out)
  all_goals refine ⟨_,rfl,?_,?_,?_⟩
  all_goals repeat rw [ProcPriorCodecControlCells.row I R present vid _ _ _ _ _ _ _ _ (by simp [columns])]
  all_goals simp [SchedSetAll.lookup,initial,List.foldl_append,columns,baseExtra,startExtra,allowanceExtra,priorExtra,
    wrapExtra,compareExtra,carryExtra,endExtra,forwardExtra,
    ap,apost,big,lowf,wt,nzb,ib,ig2,e2,cb,rend,bF,a1,a2,g2,al,base,afin,gfin,u0g,
    fwg,cx,cy,cbit,cg,pm0,pm1,fb,apR,bigR,a0g,rs,Codec.gb,srcC,hasC,useC,fA,zt]
  all_goals omega
end ZkFormal.NearV3.Candidates.ProcPriorCodecTerminalGates
