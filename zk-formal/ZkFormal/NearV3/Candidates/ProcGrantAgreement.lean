import ZkFormal.NearV3.Candidates.ProcModelEntryShape
namespace ZkFormal.NearV3.Candidates.ProcGrantAgreement
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

theorem set_read (a : Array Nat) (i : Nat) : a.set! i a[i]! = a := by
  by_cases hi : i<a.size
  · simp [Array.set!_eq_setIfInBounds,Array.setIfInBounds,hi, getElem!_pos a i hi]
  · simp [Array.set!_eq_setIfInBounds,Array.setIfInBounds,hi]

theorem coordinates (n s r l : Nat) (hr : r<n) (hl : l=s*n+r) : l/n=s ∧ l%n=r := by
  have hn : 0<n := by omega
  subst l
  constructor
  · rw [Nat.add_comm,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt hr]
    simp
  · simp [Nat.add_mod,Nat.mod_eq_of_lt hr]

def modelGrant (n : Nat) (allowed : Array Bool) (l inc : Nat) (st : PState) : PState :=
  if allowed[l]! && decide (inc≤st.sb[l/n]!) && decide (inc≤st.rb[l%n]!) then
    { st with
      sb := st.sb.set! (l/n) (st.sb[l/n]! - inc)
      rb := st.rb.set! (l%n) (st.rb[l%n]! - inc)
      al := st.al.set! l (st.al[l]! - inc)
      g := st.g.set! l (st.g[l]! + inc) }
  else st

def replayGrant (allowed : Array Bool) (s r l inc : Nat) (st : PState) : PState :=
  let ok := decide (inc≤st.sb[s]!) && decide (inc≤st.rb[r]!) && allowed[l]!
  { st with
    sb := st.sb.set! s (if ok then st.sb[s]! - inc else st.sb[s]!)
    rb := st.rb.set! r (if ok then st.rb[r]! - inc else st.rb[r]!)
    al := st.al.set! l (if ok then st.al[l]! - inc else st.al[l]!)
    g := st.g.set! l (if ok then st.g[l]! + inc else st.g[l]!) }

/-- Generator unconditional writes and native conditional updates agree exactly,
including denied grants, using actual resolved source/receiver coordinates. -/
theorem grant_eq (n : Nat) (allowed : Array Bool) (s r l inc : Nat) (st : PState)
    (hr : r<n) (hl : l=s*n+r) : modelGrant n allowed l inc st=replayGrant allowed s r l inc st := by
  obtain ⟨hd,hm⟩ := coordinates n s r l hr hl
  cases hS : decide (inc≤st.sb[s]!) <;> cases hR : decide (inc≤st.rb[r]!) <;> cases hL : allowed[l]! <;>
    simp only [modelGrant,replayGrant,hd,hm,hS,hR,hL,Bool.false_and,Bool.and_false,
      Bool.true_and,Bool.and_true,Bool.false_eq_true,ite_false,ite_true,set_read]

theorem entry_grant (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z v : Nat) (s : ProcModelStep.EntryAcc) (out : ForInStep ProcModelStep.EntryAcc)
    (h : ProcModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ExceptLoop.StepInv (fun out=>out.2.1=modelGrant n allowed reqs.toArray[v/64]!.link
      (reqs.toArray[v/64]!.incs.getD (v%64) 0) s.2.1) out := by
  unfold ProcModelStep.entryStep at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals simp_all only [ExceptLoop.StepInv,modelGrant,Bool.false_eq_true,ite_true,ite_false]
end ZkFormal.NearV3.Candidates.ProcGrantAgreement
