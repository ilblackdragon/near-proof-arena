import ZkFormal.NearV3.Candidates.ProcActualModelKeyCap
import ZkFormal.NearV3.Candidates.ProcActualMemoryFinal
namespace ZkFormal.NearV3.Candidates.ProcActualAllowanceBound
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl
def Bound (M : Nat) (st : PState) : Prop := ∀i : Nat,st.al[i]!≤M

theorem model_bound (n M : Nat) (allowed : Array Bool) (l inc : Nat) (st : PState)
    (h : Bound M st) : Bound M (ProcGrantAgreement.modelGrant n allowed l inc st) := by
  unfold ProcGrantAgreement.modelGrant
  split
  · intro i
    by_cases hl : l<st.al.size
    · by_cases hi : i<st.al.size
      · by_cases he : i=l
        · subst i
          simpa [Array.set!_eq_setIfInBounds,Array.setIfInBounds,hl,hi] using
            (Nat.le_trans (Nat.sub_le st.al[l]! inc) (h l))
        · simpa [Array.set!_eq_setIfInBounds,Array.setIfInBounds,hl,hi,he,Ne.symm he] using h i
      · simp [Array.set!_eq_setIfInBounds,Array.setIfInBounds,hl,getElem!_def,hi]
    · simpa [Array.set!_eq_setIfInBounds,Array.setIfInBounds,hl] using h i
  · exact h

theorem entry_bound (n M : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z v : Nat) (s : ProcModelStep.EntryAcc) (hs : Bound M s.2.1)
    (out : ForInStep ProcModelStep.EntryAcc)
    (h : ProcModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ExceptLoop.StepInv (fun s => Bound M s.2.1) out := by
  have hg := ProcGrantAgreement.entry_grant n allowed reqs K z v s out h
  cases out <;> simp only [ExceptLoop.StepInv] at hg ⊢ <;>
    rw [hg] <;> exact model_bound n M allowed _ _ _ hs

theorem entries_bound (n M : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z : Nat) (vs : List Nat) (s out : ProcModelStep.EntryAcc)
    (hs : Bound M s.2.1)
    (h : forIn vs s (ProcModelStep.entryStep n allowed reqs K z)=.ok out) : Bound M out.2.1 :=
  ExceptLoop.invariant vs (ProcModelStep.entryStep n allowed reqs K z) (fun s=>Bound M s.2.1)
    (fun v _ s hs out h=>entry_bound n M allowed reqs K z v s hs out h) s out hs h

set_option maxHeartbeats 800000 in
theorem step_bound (n M : Nat) (allowed : Array Bool) (reqs : List Req)
    (i : Nat) (s : ProcModelStep.Acc) (hs : Bound M s.2.1)
    (out : ForInStep ProcModelStep.Acc) (h : ProcModelStep.step n allowed reqs i s=.ok out) :
    ExceptLoop.StepInv (fun s=>Bound M s.2.1) out := by
  unfold ProcModelStep.step at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | rename_i sh rng hsh unused entryOut hentry
      exact entries_bound n M allowed reqs _ _ _ _ _ (by exact hs) hentry

set_option maxHeartbeats 400000 in
theorem process_bound (n M : Nat) (allowed : Array Bool) (reqs : List Req)
    (st0 st : PState) (fuel : Nat) (rs : List Round) (hs : Bound M st0)
    (h : processEv n allowed reqs st0 fuel=.ok (st,rs)) : Bound M st := by
  rw [ProcModelStep.process_eq] at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals
    refine ExceptLoop.invariant (α := Nat) (ε := String) ?xs ?f
      (fun s : ProcModelStep.Acc=>Bound M s.2.1) ?step ?b _ ?init ?loop
    case loop => assumption
    case init => exact hs
    case step => exact fun i _ s hs out h=>step_bound n M allowed reqs i s hs out h

theorem actual_process (I : Input) (st : PState) (rs : List Round)
    (h : ProcActualInput.process I=.ok (st,rs)) : Bound I.p.maxAllowance st :=
  process_bound I.ids.length I.p.maxAllowance I.allowed _ _ st _ rs
    (ProcActualModelKeyCap.initial_allowance I) h

theorem run_allowance (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tau : Nat) (cv : Array CReq) (rs : List Round)
    (st : PState) (ev : Ev) (R : Run)
    (hprefix : ProcActualPrefix.runPrefix (ProcPreparedSequence.input sp prev)=.ok (cv,st,rs,ev))
    (hr : ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok R)
    (i : Nat) (hi : i<sp.ids.length*sp.ids.length) :
    (R.segs.getD i default).vfin<16777216 := by
  have hp := (ProcActualAfterMemoryReduction.prefix_facts _ cv st rs ev hprefix).2
  have hb := actual_process (ProcPreparedSequence.input sp prev) st rs hp i
  rw [(ProcActualMemoryFinal.run_link_final sp hs prev tau cv rs st ev R i hi hprefix hr).1]
  change st.al[i]!≤sp.params.maxAllowance at hb
  have hm : sp.params.maxAllowance=4500000 := by rw [lp_calc hs.params]
  omega
/-- Any successful actual run on valid scheduler parameters has24-bit final
link allowances; prefix success and internal process witnesses are derived. -/
theorem successful_run (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tau : Nat) (R : Run)
    (hr : ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok R)
    (i : Nat) (hi : i<sp.ids.length*sp.ids.length) :
    (R.segs.getD i default).vfin<16777216 := by
  have hx := hr
  rw [ProcActualRunFactor.run_eq_prefix] at hx
  cases hp : ProcActualPrefix.runPrefix (ProcPreparedSequence.input sp prev) with
  | error e => simp only [hp,bind,Except.bind] at hx; cases hx
  | ok v =>
    rcases v with ⟨cv,st,rs,ev⟩
    exact run_allowance sp hs prev tau cv rs st ev R hp hr i hi
end ZkFormal.NearV3.Candidates.ProcActualAllowanceBound
