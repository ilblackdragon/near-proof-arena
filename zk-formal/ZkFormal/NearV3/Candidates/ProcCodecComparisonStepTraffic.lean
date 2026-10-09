import ZkFormal.NearV3.Candidates.ProcCodecComparisonAppend
import ZkFormal.NearV3.Candidates.ProcCodecComparisonTraffic
namespace ZkFormal.NearV3.Candidates.ProcCodecComparisonStepTraffic
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec ProcPriorCodecRecordStep
open ZkFormal.NearV3.Sched.Complete ProcCodecComparisonAppend
set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
theorem step_traffic (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vid k f g : Nat) (st : State) (out : ForInStep State)
    (h:step I R present gb fwd (ProcPriorCodecNativeHash.instanceCells I R present vid) k f g st=.ok out) :
    ∃s a,out=.yield s ∧ s.1=st.1.push a ∧ ProcCodecConcatTraffic.natMessages a B_SCMP true=(requests I R present gb fwd k f g).map cmpMsg := by
  have az (n j : Nat) : (Array.replicate n (0:Nat))[j]! = 0 := by
    by_cases hj:j<n
    · simp [getElem!_pos, hj]
    · simp [getElem!_neg, hj]
  by_cases h0:f=0 ∧ g=0
  all_goals by_cases h2:f=2
  all_goals by_cases hg2:g=2
  all_goals by_cases hg7:g=7
  all_goals by_cases hge:g≥2
  all_goals try omega
  all_goals simp (maxSteps := 1000000) only [step,az,Nat.zero_div,Nat.zero_mod,ne_eq,not_true_eq_false,h0,h2,hg2,hg7,hge,and_true,and_false,true_and,false_and,
    ite_true,ite_false,ite_self,Nat.reduceEqDiff,Nat.reduceLeDiff,Nat.reduceLT,bind,Except.bind,pure,Except.pure] at h
  all_goals repeat first | cases h | split at h
  all_goals try { unfold check at h; simp only [bind,Except.bind,pure,Except.pure] at h }
  all_goals repeat first | cases h | split at h
  all_goals first | refine ⟨_,_,rfl,rfl,?_⟩ | refine ⟨_,_,(Except.ok.inj h).symm,rfl,?_⟩
  all_goals rw [ProcCodecComparisonTraffic.nat_messages]
  all_goals rw [ProcCodecComparisonCells.row I R present vid k _ _ _ _ _ _ cg (by simp),
    ProcCodecComparisonCells.row I R present vid k _ _ _ _ _ _ cx (by simp),
    ProcCodecComparisonCells.row I R present vid k _ _ _ _ _ _ cy (by simp),
    ProcCodecComparisonCells.row I R present vid k _ _ _ _ _ _ cbit (by simp)]
  all_goals simp_all [requests,SchedSetAll.lookup,List.foldl_append,
    ProcPriorCodecExtra.baseExtra,ProcPriorCodecExtra.startExtra,ProcPriorCodecExtra.priorExtra,
    ProcPriorCodecExtra.allowanceExtra,ProcPriorCodecExtra.wrapExtra,ProcPriorCodecExtra.compareExtra,
    ProcPriorCodecExtra.carryExtra,ProcPriorCodecExtra.endExtra,ProcPriorCodecExtra.forwardExtra,
    cg,cx,cy,cbit,rs,al,Codec.gb,srcC,hasC,useC,nzb,ig2,ib,apR,bigR,lowf,wt,ap,big,apost,e2,a0g,cb,
    rend,bF,a1,a2,g2,afin,gfin,u0g,fwg,pm0,pm1,fb,cmpMsg]


  all_goals simp only [show ZkFormal.Algebra.Fp.ofNat 0 = (0:ZkFormal.Algebra.Fp) from rfl,
    show ZkFormal.Algebra.Fp.ofNat 1 = (1:ZkFormal.Algebra.Fp) from rfl,
    show (0:ZkFormal.Algebra.Fp) ≠ 1 from by decide +kernel,List.not_mem_nil,not_false_eq_true,if_false,if_true,List.replicate_zero,List.replicate_succ]
end ZkFormal.NearV3.Candidates.ProcCodecComparisonStepTraffic
