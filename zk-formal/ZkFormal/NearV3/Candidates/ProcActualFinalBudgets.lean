import ZkFormal.NearV3.Candidates.ProcActualModelKeyCap
import ZkFormal.NearV3.Candidates.ProcActualMemoryFinal
import ZkFormal.NearV3.Candidates.ProcActualReplayAllowance
namespace ZkFormal.NearV3.Candidates.ProcActualFinalBudgets
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl
def Bound (M : Nat) (st : PState) : Prop := (∀i : Nat,st.sb[i]!≤M) ∧ (∀i : Nat,st.rb[i]!≤M)

theorem model_bound (n M : Nat) (allowed : Array Bool) (l inc : Nat) (st : PState)
    (h : Bound M st) : Bound M (ProcGrantAgreement.modelGrant n allowed l inc st) := by
  unfold ProcGrantAgreement.modelGrant
  split
  · exact ⟨ProcActualReplayAllowance.set_bound _ _ h.1 _ _ (Nat.le_trans (Nat.sub_le _ _) (h.1 _)),
      ProcActualReplayAllowance.set_bound _ _ h.2 _ _ (Nat.le_trans (Nat.sub_le _ _) (h.2 _))⟩
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

theorem initial (I:Input) : Bound I.p.maxShardBandwidth (ProcActualInput.initial I) := by
  have hb : ∀(xs:List Nat)(i:Nat),
      ((xs.toArray.map fun c=>I.p.maxShardBandwidth-I.p.base*c)[i]!)≤I.p.maxShardBandwidth := by
    intro xs i
    simp only [getElem!_def,Array.getElem?_map]
    split
    · next h=>
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨c,_,rfl⟩:=h
      exact Nat.sub_le _ _
    · exact Nat.zero_le _
  exact ⟨hb _,hb _⟩

theorem actual_process (I:Input)(st:PState)(rs:List Round)
    (h:ProcActualInput.process I=.ok (st,rs)) : Bound I.p.maxShardBandwidth st :=
  process_bound I.ids.length I.p.maxShardBandwidth I.allowed _ _ st _ rs (initial I) h

set_option maxHeartbeats 1200000 in
theorem run (I:Input)(tau:Nat)(R:Run)(h:ActualRun.run I tau=.ok R) : Bound I.p.maxShardBandwidth R.fin := by
  unfold ActualRun.run at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals apply actual_process I; assumption

theorem prepared (sp:SchedPub)(hs:SchedPubOk sp)(prev:NearSpec.Bandwidth.State)(tau:Nat)(R:Run)
    (h:ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok R) :
    (∀i:Nat,R.fin.sb[i]!<2^23) ∧ (∀i:Nat,R.fin.rb[i]!<2^23) := by
  have hb:=run _ tau R h
  change Bound sp.params.maxShardBandwidth R.fin at hb
  rw [pv86_maxShard hs.params] at hb
  exact ⟨fun i=>by have:=hb.1 i;omega,fun i=>by have:=hb.2 i;omega⟩
end ZkFormal.NearV3.Candidates.ProcActualFinalBudgets
