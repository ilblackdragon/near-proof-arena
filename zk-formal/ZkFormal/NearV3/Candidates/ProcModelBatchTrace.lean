import ZkFormal.NearV3.Candidates.ProcActualEntryTransition
namespace ZkFormal.NearV3.Candidates.ProcModelBatchTrace
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

/-- Retain each round's actual shuffle and entry-loop witnesses. -/
def Batch (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (st : PState) (t : Nat) (rd : Round) (st' : PState) (t' : Nat) : Prop :=
  ∃rng pending out,
    NearSpecV3.shuffle (rd.bucket.map (·.v)) st.rng=some (rd.shuffled,rng) ∧
    forIn rd.shuffled (pending,{st with rng:=rng},t,[])
      (ProcModelStep.entryStep n allowed reqs rd.key rd.z)=.ok out ∧
    rd.steps=out.2.2.2 ∧ st'=out.2.1 ∧ t'=out.2.2.1 ∧ rd.kstart=t

inductive Trace (n : Nat) (allowed : Array Bool) (reqs : List Req) (initial : PState)
    (start : Nat) : List Round → PState → Nat → Prop
  | nil : Trace n allowed reqs initial start [] initial start
  | snoc {rs : List Round} {st : PState} {t : Nat}
      (h : Trace n allowed reqs initial start rs st t)
      (rd : Round) (st' : PState) (t' : Nat)
      (hb : Batch n allowed reqs st t rd st' t') :
      Trace n allowed reqs initial start (rs++[rd]) st' t'

def Inv (n : Nat) (allowed : Array Bool) (reqs : List Req) (initial : PState)
    (start : Nat) (s : ProcModelStep.Acc) : Prop :=
  Trace n allowed reqs initial start s.2.2.2.1 s.2.1 s.2.2.1

set_option maxHeartbeats 800000 in
theorem step_trace (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (initial : PState) (start i : Nat) (s : ProcModelStep.Acc)
    (hs : Inv n allowed reqs initial start s) (out : ForInStep ProcModelStep.Acc)
    (h : ProcModelStep.step n allowed reqs i s=.ok out) :
    ExceptLoop.StepInv (Inv n allowed reqs initial start) out := by
  unfold ProcModelStep.step at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | rename_i sh rng hsh unused entryOut hentry
      exact Trace.snoc hs _ _ _ ⟨rng,_,entryOut,hsh,hentry,rfl,rfl,rfl,rfl⟩

set_option maxHeartbeats 400000 in
/-- Successful process execution retains the complete ordered chain of batches. -/
theorem process_trace (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h : processEv n allowed reqs st0 fuel=.ok (st,rs)) :
    ∃last,Trace n allowed reqs st0 reqs.length rs st last := by
  rw [ProcModelStep.process_eq] at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals
    have ht : Inv n allowed reqs st0 reqs.length ?out := by
      refine ExceptLoop.invariant (α := Nat) (ε := String) ?xs ?f
        (Inv n allowed reqs st0 reqs.length) ?step ?b _ ?init ?loop
      case loop => assumption
      case init => exact Trace.nil
      case step => exact fun i _ s hs out h=>step_trace n allowed reqs st0 reqs.length i s hs out h
    exact ⟨_,ht⟩
end ZkFormal.NearV3.Candidates.ProcModelBatchTrace
