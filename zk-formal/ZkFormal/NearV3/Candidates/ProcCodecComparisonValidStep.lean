import ZkFormal.NearV3.Candidates.ProcCodecComparisonCost
import ZkFormal.NearV3.Candidates.CmpHeight
namespace ZkFormal.NearV3.Candidates.ProcCodecComparisonValidStep
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcPriorCodecRecordStep
open ZkFormal.NearV3.Sched.Complete

def Good (s : State) :=∀q∈s.2.1,CmpOk q

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
theorem step (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k f g : Nat) (st : State) (out : ForInStep State)
    (hmax:I.p.maxShardBandwidth≤4500000)
    (hgrant:(R.segs.getD k default).wfin+gb[k]!≤4500000)
    (hg:Good st)
    (h:ProcPriorCodecRecordStep.step I R present gb fwd inst k f g st=.ok out) :
    ∃s,out=.yield s ∧ Good s := by
  have checked (x y : Nat) (msg : String) (u : Unit)
      (hh:check (decide (x≤y)) msg=.ok u) : x≤y := by
    by_cases hxy:x≤y
    · exact hxy
    · simp [check,hxy] at hh
  have hf:I.p.maxShardBandwidth/R.n≤4500000:=Nat.le_trans (Nat.div_le_self _ _) hmax
  have hlow: (if present then (ProcActualInput.allowances I.ids I.prev)[k]! else 0)%16777216<16777216:=
    Nat.mod_lt _ (by decide)
  have az (n j : Nat) : (Array.replicate n (0:Nat))[j]! = 0 := by
    by_cases hj:j<n
    · simp [getElem!_pos,hj]
    · simp [getElem!_neg,hj]
  by_cases h0:f=0 ∧ g=0
  all_goals by_cases h2:f=2
  all_goals by_cases hg2:g=2
  all_goals by_cases hg7:g=7
  all_goals by_cases hge:g≥2
  all_goals try omega
  all_goals simp (maxSteps := 1000000) only [ProcPriorCodecRecordStep.step,az,Nat.zero_div,Nat.zero_mod,
    ne_eq,not_true_eq_false,h0,h2,hg2,hg7,hge,and_true,and_false,true_and,false_and,
    ite_true,ite_false,ite_self,Nat.reduceEqDiff,Nat.reduceLeDiff,Nat.reduceLT,bind,Except.bind,pure,Except.pure] at h
  all_goals repeat first | cases h | split at h
  all_goals try { unfold check at h; simp only [bind,Except.bind,pure,Except.pure] at h }
  all_goals repeat first | cases h | split at h
  all_goals first | refine ⟨_,rfl,?_⟩ | refine ⟨_,(Except.ok.inj h).symm,?_⟩
  all_goals try have hfw : ((fwd.find? (·.1==k)).map (·.2)).getD 0≤
      (R.segs.getD k default).wfin+gb[k]! := checked _ _ _ _ (by assumption)
  all_goals intro q hq
  all_goals simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  all_goals first
    | exact hg q hq
    | (rcases hq with hq|rfl
       · exact hg q hq
       · simp only [CmpOk,Prod.fst,Prod.snd]
         repeat' split <;> simp_all [check,Codec.MA] <;> omega)
end ZkFormal.NearV3.Candidates.ProcCodecComparisonValidStep
