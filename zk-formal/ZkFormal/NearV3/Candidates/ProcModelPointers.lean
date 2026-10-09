import ZkFormal.NearV3.Candidates.ProcEntryPointers
import ZkFormal.NearV3.Sched.Spec.Loop
namespace ZkFormal.NearV3.Candidates.ProcModelPointers
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcRequestPointers
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

def Inv (reqs : List Req) (s : ProcModelStep.Acc) : Prop :=
  (∀p∈s.1,Valid reqs p.v) ∧ (∀rd∈s.2.2.2.1,∀e∈rd.steps,Valid reqs e.v)

set_option maxHeartbeats 800000 in
theorem step_inv (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (hsmall : Small reqs) (i : Nat) (s : ProcModelStep.Acc) (hs : Inv reqs s)
    (out : ForInStep ProcModelStep.Acc) (h : ProcModelStep.step n allowed reqs i s=.ok out) :
    ExceptLoop.StepInv (Inv reqs) out := by
  unfold ProcModelStep.step at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | rename_i sh rng hsh unused entryOut hentry
      have hv : ∀v∈sh,Valid reqs v := by
        intro v hv
        have hm := (shuffle_perm hsh).mem_iff.mp hv
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
        have hp' := (ProcPushPerm.sort_perm _).mem_iff.mp hp
        exact hs.1 p (List.mem_filter.mp hp').1
      have he := ProcEntryPointers.entries_inv n allowed reqs _ _ sh hsmall hv _ entryOut
        (And.intro (fun p hp=>hs.1 p (List.mem_filter.mp hp).1) (by simp)) hentry
      refine ⟨he.1,?_⟩
      intro rd hr e hm
      simp only [List.mem_append,List.mem_singleton] at hr
      rcases hr with hr|rfl
      · exact hs.2 rd hr e hm
      · exact he.2 e hm

set_option maxHeartbeats 400000 in
/-- Every request ID and increase index inspected by a successful model run is
in bounds, derived from initial requests and exact re-push/shuffle semantics. -/
theorem process_pointers (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (hsmall : Small reqs) (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h : processEv n allowed reqs st0 fuel=.ok (st,rs)) :
    ∀rd∈rs,∀e∈rd.steps,Valid reqs e.v := by
  rw [ProcModelStep.process_eq] at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals
    have hh : Inv reqs ?out := by
      refine ExceptLoop.invariant (α := Nat) (ε := String) ?xs ?f (Inv reqs) ?step ?b _ ?init ?loop
      case loop => assumption
      case init => exact ⟨initial_valid reqs st0,by simp [ProcModelStep.initial]⟩
      case step => exact fun i _ s hs out h=>step_inv n allowed reqs hsmall i s hs out h
    exact hh.2
end ZkFormal.NearV3.Candidates.ProcModelPointers
