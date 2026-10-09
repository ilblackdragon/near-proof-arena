import ZkFormal.NearV3.Candidates.ProcModelEvent
import ZkFormal.NearV3.Candidates.ProcActualIndexGuards
import ZkFormal.NearV3.Candidates.ProcActualRun
import ZkFormal.NearV3.Candidates.ProcActualConverted
import ZkFormal.NearV3.Candidates.ProcActualReplayShape
import ZkFormal.NearV3.Sched.Spec.Steps
namespace ZkFormal.NearV3.Candidates.ProcActualCoordinates
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def Facts (I : Input) (c : CReq) : Prop :=
  c.s<I.ids.length ∧ c.r<I.ids.length ∧ c.link=c.s*I.ids.length+c.r

def All (I : Input) (cv : Array CReq) : Prop := ∀c∈cv.toList,Facts I c

theorem step_facts (I : Input) (q : RawReq) (cv : Array CReq) (hs : All I cv)
    (out : ForInStep (Array CReq)) (h : ProcActualConverted.step I q cv=.ok out) :
    ExceptLoop.StepInv (All I) out := by
  unfold ProcActualConverted.step at h
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
        have hh := ProcActualReplayShape.check_true _ _ hcheck
        simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
        exact ⟨hh.1,hh.2,rfl⟩

theorem loop_facts (I : Input) (out : Array CReq)
    (h : forIn I.raw #[] (ProcActualConverted.step I)=.ok out) : All I out :=
  ExceptLoop.invariant I.raw (ProcActualConverted.step I) (All I)
    (fun q _ cv hs out h=>step_facts I q cv hs out h) #[] out (by simp [All]) h

/-- Converted coordinates supply model/replay event equality at a valid pointer.
The allowance-array size is explicit until the combined replay invariant is wired. -/
theorem selected_event (I : Input) (cv : Array CReq)
    (hcv : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv)
    (v t : Nat) (st : PState)
    (hv : ProcRequestPointers.Valid (ProcActualConversionExact.view cv) v)
    (ha : st.al.size=I.ids.length*I.ids.length) :
    ProcModelEvent.event I.ids.length I.allowed (ProcActualConversionExact.view cv) v t st=
      ProcModelEvent.replayEvent I.allowed cv[v/64]! v t st := by
  obtain ⟨hi,hj⟩ := ProcActualIndexGuards.view_bounds cv v hv
  have hm : cv[v/64]!∈cv.toList := by
    rw [getElem!_pos cv _ hi]
    exact Array.getElem_mem_toList hi
  have hf := loop_facts I cv hcv _ hm
  have hq : (ProcActualConversionExact.view cv).toArray[v/64]! =
      NearSpecV3.Scheduler.Req.mk cv[v/64]!.link cv[v/64]!.incs := by
    simp [ProcActualConversionExact.view,List.getElem!_toArray,getElem!_def,hi]
  apply ProcModelEvent.event_eq_replay _ _ _ _ _ _ _ hq hf.2.1 hf.2.2 hj
  rw [ha,hf.2.2]
  have hmul := Nat.mul_le_mul_right I.ids.length (Nat.succ_le_of_lt hf.1)
  rw [Nat.succ_mul] at hmul
  have hr : cv[v/64]!.r<I.ids.length := hf.2.1
  omega

end ZkFormal.NearV3.Candidates.ProcActualCoordinates
