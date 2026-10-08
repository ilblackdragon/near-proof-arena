import ZkFormal.NearV3.Candidates.ProcActualRun
import ZkFormal.NearV3.Candidates.ProcActualZeroPending
namespace ZkFormal.NearV3.Candidates.ProcActualZeroTransition
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualZeroPending

private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

theorem entry_pending (n : Nat) (allowed : Array Bool) (reqs : List NearSpecV3.Scheduler.Req)
    (K z v : Nat) (s : ProcActualModelStep.EntryAcc)
    (hs : Pending (nextZero (some (K,z))) s.1)
    (out : ForInStep ProcActualModelStep.EntryAcc) (h : ProcActualModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ExceptLoop.StepInv (fun s=>Pending (nextZero (some (K,z))) s.1) out := by
  unfold ProcActualModelStep.entryStep at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | simp only [ExceptLoop.StepInv,Pending,List.mem_append,List.mem_singleton]
      intro p hp hk
      rcases hp with hp|rfl
      · exact hs p hp hk
      · dsimp only at hk ⊢
        rw [if_pos hk]
        rfl

theorem entries_pending (n : Nat) (allowed : Array Bool) (reqs : List NearSpecV3.Scheduler.Req)
    (K z : Nat) (vs : List Nat) (s out : ProcActualModelStep.EntryAcc)
    (hs : Pending (nextZero (some (K,z))) s.1)
    (h : forIn vs s (ProcActualModelStep.entryStep n allowed reqs K z)=.ok out) :
    Pending (nextZero (some (K,z))) out.1 :=
  ExceptLoop.invariant vs (ProcActualModelStep.entryStep n allowed reqs K z)
    (fun s=>Pending (nextZero (some (K,z))) s.1)
    (fun v _ s hs out h=>entry_pending n allowed reqs K z v s hs out h) s out hs h

def Ordered (last : Option (Nat×Nat)) (K z : Nat) : Prop :=
  match last with | none=>True | some (K',z')=>K<K' ∨ (K=0 ∧ K'=0 ∧ z=z'+1)

theorem next_positive (last : Option (Nat×Nat)) (K z : Nat)
    (h : Ordered last K z) (hk : K≠0) : nextZero last=1 := by
  cases last with
  | none => rfl
  | some a =>
    rcases a with ⟨K',z'⟩
    have hkp : K'≠0 := by unfold Ordered at h; omega
    simp [nextZero,hkp]

theorem filtered_pending (ps : List Push) (last : Option (Nat×Nat)) (K z : Nat)
    (hp : Pending (nextZero last) ps)
    (hk : K=ps.foldl (fun m p=>Nat.max m p.key) 0)
    (ho : Ordered last K z) :
    Pending (nextZero (some (K,z))) (ps.filter (fun p=>p.key != K)) := by
  by_cases hz : K=0
  · have hf := zero_filter ps (hk.symm.trans hz)
    simpa [hz,hf,Pending]
  · intro p hm hzero
    have hm' := (List.mem_filter.mp hm).1
    have hh := hp p hm' hzero
    rw [next_positive last K z ho hz] at hh
    simpa [nextZero,hz] using hh
end ZkFormal.NearV3.Candidates.ProcActualZeroTransition
