import ZkFormal.NearV3.Candidates.ProcModelEntryShape
import ZkFormal.NearV3.Sched.Spec.Loop
namespace ZkFormal.NearV3.Candidates.ProcModelRoundShape
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

inductive Trace (start : Nat) : List Round → Nat → Prop
  | nil : Trace start [] start
  | snoc {rs : List Round} {t : Nat} (h : Trace start rs t) (rd : Round)
      (ht : rd.kstart=t) (hc : rd.steps.length=rd.bucket.length)
      (hs : ProcModelEntryShape.Stamped t rd.steps) :
      Trace start (rs++[rd]) (t+rd.bucket.length)

def Inv (start : Nat) (s : ProcModelStep.Acc) : Prop := Trace start s.2.2.2.1 s.2.2.1

set_option maxHeartbeats 800000 in
theorem step_inv (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (start i : Nat) (s : ProcModelStep.Acc) (hs : Inv start s)
    (out : ForInStep ProcModelStep.Acc) (h : ProcModelStep.step n allowed reqs i s=.ok out) :
    ExceptLoop.StepInv (Inv start) out := by
  unfold ProcModelStep.step at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | rename_i sh rng hsh unused entryOut hentry
      have hl := (shuffle_perm hsh).length_eq
      simp only [List.length_map] at hl
      have hc := ProcModelEntryShape.entries_counts n allowed reqs _ _ _ _ _ hentry
      have ht := ProcModelEntryShape.entries_inv n allowed reqs _ _ s.2.2.1 _ _ _
        ⟨rfl,by simp [ProcModelEntryShape.Stamped]⟩ hentry
      change Trace start _ entryOut.2.2.1
      rw [hc.1,hl]
      exact Trace.snoc hs _ rfl (by simpa only [List.length_nil,Nat.zero_add,hl] using hc.2) ht.2

set_option maxHeartbeats 400000 in
theorem process_trace (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h : processEv n allowed reqs st0 fuel=.ok (st,rs)) : ∃last,Trace reqs.length rs last := by
  rw [ProcModelStep.process_eq] at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals
    have hh : Inv reqs.length ?out := by
      refine ExceptLoop.invariant (α := Nat) (ε := String) ?xs ?f (Inv reqs.length) ?step ?b _ ?init ?loop
      case loop => assumption
      case init => exact Trace.nil
      case step => exact fun i _ s hs out h=>step_inv n allowed reqs reqs.length i s hs out h
    exact ⟨_,hh⟩
end ZkFormal.NearV3.Candidates.ProcModelRoundShape
