import ZkFormal.NearV3.Candidates.ProcMaxBucket
namespace ZkFormal.NearV3.Candidates.ProcModelTime
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

def Inv (s : ProcModelStep.Acc) : Prop :=
  ProcPendingTime.Inv s.1 s.2.2.1 ∧ ∀rd∈s.2.2.2.1,ProcPendingTime.Inv rd.bucket rd.kstart

set_option maxHeartbeats 800000 in
theorem step_inv (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (i : Nat) (s : ProcModelStep.Acc) (hs : Inv s)
    (out : ForInStep ProcModelStep.Acc) (h : ProcModelStep.step n allowed reqs i s=.ok out) :
    ExceptLoop.StepInv Inv out := by
  unfold ProcModelStep.step at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | rename_i sh rng hsh unused entryOut hentry
      have hf (f : Push→Bool) : ProcPendingTime.Inv (s.1.filter f) s.2.2.1 :=
        ⟨hs.1.1.filter _,fun p hp=>hs.1.2 p (List.mem_filter.mp hp).1⟩
      have he := ProcPendingTime.entries_inv n allowed reqs _ _ _ _ entryOut (hf _) hentry
      refine ⟨he,?_⟩
      intro rd hr
      simp only [List.mem_append,List.mem_singleton] at hr
      rcases hr with hr|rfl
      · exact hs.2 rd hr
      · change ProcPendingTime.Inv (sortTs _) _
        rw [ProcMaxBucket.sort_id _ (hs.1.1.filter _)]
        exact hf _

set_option maxHeartbeats 400000 in
theorem process_time (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h : processEv n allowed reqs st0 fuel=.ok (st,rs)) :
    ∀rd∈rs,rd.bucket.Pairwise (fun p q=>p.ts<q.ts) ∧ ∀p∈rd.bucket,p.ts<rd.kstart := by
  rw [ProcModelStep.process_eq] at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals
    have hh : Inv ?out := by
      refine ExceptLoop.invariant (α := Nat) (ε := String) ?xs ?f Inv ?step ?b _ ?init ?loop
      case loop => assumption
      case init => exact ⟨ProcPendingTime.initial reqs st0,by simp [ProcModelStep.initial]⟩
      case step => exact fun i _ s hs out h=>step_inv n allowed reqs i s hs out h
    exact hh.2
end ZkFormal.NearV3.Candidates.ProcModelTime
