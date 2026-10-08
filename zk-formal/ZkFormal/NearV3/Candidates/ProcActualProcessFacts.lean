import ZkFormal.NearV3.Candidates.ProcActualInput
import ZkFormal.NearV3.Candidates.ProcNativeState
namespace ZkFormal.NearV3.Candidates.ProcActualProcessFacts
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

def Shape (n : Nat) (st : PState) : Prop :=
  st.sb.size=n ∧ st.rb.size=n ∧ st.g.size=n*n

theorem model_shape (n : Nat) (allowed : Array Bool) (l inc : Nat) (st : PState)
    (h : Shape n st) : Shape n (ProcGrantAgreement.modelGrant n allowed l inc st) := by
  unfold ProcGrantAgreement.modelGrant
  split
  · simpa [Shape] using h
  · exact h

theorem entry_shape (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z v : Nat) (s : ProcModelStep.EntryAcc) (hs : Shape n s.2.1)
    (out : ForInStep ProcModelStep.EntryAcc)
    (h : ProcModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ExceptLoop.StepInv (fun s => Shape n s.2.1) out := by
  have hg := ProcGrantAgreement.entry_grant n allowed reqs K z v s out h
  cases out <;> simp only [ExceptLoop.StepInv] at hg ⊢ <;>
    rw [hg] <;> exact model_shape n allowed _ _ _ hs

theorem entries_shape (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z : Nat) (vs : List Nat) (s out : ProcModelStep.EntryAcc)
    (hs : Shape n s.2.1)
    (h : forIn vs s (ProcModelStep.entryStep n allowed reqs K z)=.ok out) : Shape n out.2.1 :=
  ExceptLoop.invariant vs (ProcModelStep.entryStep n allowed reqs K z) (fun s=>Shape n s.2.1)
    (fun v _ s hs out h=>entry_shape n allowed reqs K z v s hs out h) s out hs h

set_option maxHeartbeats 800000 in
theorem step_shape (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (i : Nat) (s : ProcModelStep.Acc) (hs : Shape n s.2.1)
    (out : ForInStep ProcModelStep.Acc) (h : ProcModelStep.step n allowed reqs i s=.ok out) :
    ExceptLoop.StepInv (fun s=>Shape n s.2.1) out := by
  unfold ProcModelStep.step at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | rename_i sh rng hsh unused entryOut hentry
      exact entries_shape n allowed reqs _ _ _ _ _ (by exact hs) hentry

set_option maxHeartbeats 400000 in
theorem process_shape (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (st0 st : PState) (fuel : Nat) (rs : List Round) (hs : Shape n st0)
    (h : processEv n allowed reqs st0 fuel=.ok (st,rs)) : Shape n st := by
  rw [ProcModelStep.process_eq] at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals
    refine ExceptLoop.invariant (α := Nat) (ε := String) ?xs ?f
      (fun s : ProcModelStep.Acc=>Shape n s.2.1) ?step ?b _ ?init ?loop
    case loop => assumption
    case init => exact hs
    case step => exact fun i _ s hs out h=>step_shape n allowed reqs i s hs out h

theorem initial_shape (I : ZkFormal.NearV3.Sched.Gen.Input) :
    Shape I.ids.length (ProcActualInput.initial I) := by
  simp [Shape,ProcActualInput.initial,linkPass]

/-- Successful corrected processing derives the final budget invariant and all
array sizes required by native distribution agreement. -/
theorem prepared_facts (sp : SchedPub) (hs : SchedPubOk sp)
    (ha : sp.allowed.size=sp.ids.length*sp.ids.length) (prev : NearSpec.Bandwidth.State)
    (st : PState) (rs : List Round)
    (h : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs)) :
    ProcNativeGrant.Inv sp.ids.length sp.params.maxShardBandwidth st ∧ Shape sp.ids.length st := by
  have hM : sp.params.maxShardBandwidth≤u64Max := by rw [pv86_maxShard hs.params]; decide
  refine ⟨ProcNativeState.process_inv sp.ids.length sp.params.maxShardBandwidth hM sp.allowed
    _ _ st _ rs (ProcActualInput.initial_inv _ hs.n1 hs.params ha) h,?_⟩
  exact process_shape sp.ids.length sp.allowed _ _ st _ rs (initial_shape _) h

end ZkFormal.NearV3.Candidates.ProcActualProcessFacts
