import ZkFormal.NearV3.Candidates.ProcCodecComparisonValidStep
namespace ZkFormal.NearV3.Candidates.ProcCodecComparisonAppend
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcPriorCodecRecordStep

def requests (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (k f g : Nat) : List (Nat×Nat×Nat) :=
  if f=2 ∧ g=2 then
    let x := (if present then (ProcActualInput.allowances I.ids I.prev)[k]! else 0)%16777216 + I.p.maxShardBandwidth/R.n
    [(x,Codec.MA,if Codec.MA≤x then 1 else 0)]
  else if f=2 ∧ g=7 ∧ R.tau=0 then
    [((R.segs.getD k default).wfin+gb[k]!,((fwd.find? (·.1 == k)).map (·.2)).getD 0,1)]
  else []

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
theorem step_requests (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k f g : Nat) (st : State) (out : ForInStep State)
    (h:step I R present gb fwd inst k f g st=.ok out) :
    ∃s,out=.yield s ∧ s.2.1=st.2.1++requests I R present gb fwd k f g := by
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
  all_goals first | refine ⟨_,rfl,?_⟩ | refine ⟨_,(Except.ok.inj h).symm,?_⟩
  all_goals simp_all [requests]

end ZkFormal.NearV3.Candidates.ProcCodecComparisonAppend
