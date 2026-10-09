import ZkFormal.NearV3.Candidates.ProcConverted
import ZkFormal.NearV3.Candidates.ProcReplayShape
import ZkFormal.NearV3.Sched.Spec.Steps
namespace ZkFormal.NearV3.Candidates.ProcConvertedFacts
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def Facts (I : Input) (c : CReq) : Prop :=
  c.s<I.ids.length ∧ c.r<I.ids.length ∧ c.incs=incsOf I.p c.bm

def All (I : Input) (cv : Array CReq) : Prop := ∀c∈cv.toList,Facts I c

theorem step_facts (I : Input) (q : RawReq) (cv : Array CReq) (hs : All I cv)
    (out : ForInStep (Array CReq)) (h : ProcConverted.step I q cv=.ok out) :
    ExceptLoop.StepInv (All I) out := by
  unfold ProcConverted.step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | simp only [ExceptLoop.StepInv,All,Array.toList_push,List.mem_append,List.mem_singleton]
      intro c hc
      rcases hc with hc|rfl
      · exact hs c hc
      · have hcheck : check (q.s<I.ids.length && q.r<I.ids.length) "shard index"=.ok () := by assumption
        have hh := ProcReplayShape.check_true _ _ hcheck
        simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
        exact ⟨hh.1,hh.2,rfl⟩

theorem loop_facts (I : Input) (out : Array CReq)
    (h : forIn I.raw #[] (ProcConverted.step I)=.ok out) : All I out :=
  ExceptLoop.invariant I.raw (ProcConverted.step I) (All I)
    (fun q _ cv hs out h=>step_facts I q cv hs out h) #[] out (by simp [All]) h

set_option maxHeartbeats 400000 in
theorem run_facts (I : Input) (tau : Nat) (R : Run) (h : Gen.run I tau=.ok R) :
    ∀c∈R.conv,Facts I c := by
  unfold Gen.run at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals apply loop_facts I; assumption

theorem entry_facts (I : Input) (cv : Array CReq) (hc : All I cv)
    (cid j : Nat) (hi : cid<cv.size) (hj : j<cv[cid]!.incs.length) :
    cv[cid]!.s<I.ids.length ∧ (I.p.maxSingleGrant-I.p.base)/40≤cv[cid]!.incs[j]! := by
  have hm : cv[cid]!∈cv.toList := by
    rw [getElem!_pos cv cid hi]
    exact Array.getElem_mem_toList hi
  have hf := hc _ hm
  refine ⟨hf.1,?_⟩
  apply incsOf_ge I.p cv[cid]!.bm
  rw [←hf.2.2,getElem!_pos cv[cid]!.incs j hj]
  exact List.getElem_mem hj
end ZkFormal.NearV3.Candidates.ProcConvertedFacts
