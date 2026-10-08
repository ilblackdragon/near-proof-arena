import ZkFormal.NearV3.Candidates.ProcShuffleReplay
import ZkFormal.NearV3.Candidates.ProcModelStep
namespace ZkFormal.NearV3.Candidates.ProcModelRng
open NearSpecV3 ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

theorem entry_rng (n : Nat) (allowed : Array Bool) (reqs : List Scheduler.Req)
    (K z v : Nat) (s : ProcModelStep.EntryAcc) (out : ForInStep ProcModelStep.EntryAcc)
    (h : ProcModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ExceptLoop.StepInv (fun out=>out.2.1.rng=s.2.1.rng) out := by
  unfold ProcModelStep.entryStep at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals rfl

theorem entries_rng (n : Nat) (allowed : Array Bool) (reqs : List Scheduler.Req)
    (K z : Nat) (vs : List Nat) (s out : ProcModelStep.EntryAcc)
    (h : forIn vs s (ProcModelStep.entryStep n allowed reqs K z)=.ok out) : out.2.1.rng=s.2.1.rng := by
  apply ExceptLoop.invariant vs (ProcModelStep.entryStep n allowed reqs K z)
    (fun out=>out.2.1.rng=s.2.1.rng) ?_ s out rfl h
  intro v hv st hs next hn
  have hh := entry_rng n allowed reqs K z v st next hn
  cases next <;> exact hh.trans hs

inductive Trace (key : List Nat) (start : Nat) : List Round → Nat → Prop
  | nil : Trace key start [] start
  | snoc {rs : List Round} {k : Nat} (h : Trace key start rs k) (rd : Round) (last : Nat)
      (hs : replayShuffle key k (rd.bucket.map (·.v))=.ok (rd.shuffled,last)) :
      Trace key start (rs++[rd]) last

def Inv (key : List Nat) (start : Nat) (s : ProcModelStep.Acc) : Prop :=
  ∃k,s.2.1.rng=rngAt key k ∧ Trace key start s.2.2.2.1 k

set_option maxHeartbeats 800000 in
theorem step_inv (n : Nat) (allowed : Array Bool) (reqs : List Scheduler.Req)
    (key : List Nat) (start i : Nat) (s : ProcModelStep.Acc) (hs : Inv key start s)
    (out : ForInStep ProcModelStep.Acc) (h : ProcModelStep.step n allowed reqs i s=.ok out) :
    ExceptLoop.StepInv (Inv key start) out := by
  let K := s.1.foldl (fun m p=>Nat.max m p.key) 0
  let bucket := sortTs (s.1.filter (fun p=>p.key==K))
  unfold ProcModelStep.step at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | rename_i sh rng hsh unused entryOut hentry
      rcases hs with ⟨k,hk,ht⟩
      change shuffle (bucket.map (·.v)) s.2.1.rng=some (sh,rng) at hsh
      rw [hk] at hsh
      obtain ⟨last,hr,he⟩ := ProcShuffleReplay.replay_of_shuffle key k _ _ _ hsh
      refine ⟨last,?_,Trace.snoc ht _ last hr⟩
      exact (entries_rng n allowed reqs _ _ _ _ _ hentry).trans he

set_option maxHeartbeats 400000 in
theorem process_trace (n : Nat) (allowed : Array Bool) (reqs : List Scheduler.Req)
    (key : List Nat) (start : Nat) (st0 st : PState) (fuel : Nat) (rs : List Round)
    (hr : st0.rng=rngAt key start)
    (h : processEv n allowed reqs st0 fuel=.ok (st,rs)) :
    ∃last,st.rng=rngAt key last ∧ Trace key start rs last := by
  rw [ProcModelStep.process_eq] at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals
    have hh : Inv key start ?out := by
      refine ExceptLoop.invariant (α := Nat) (ε := String) ?xs ?f (Inv key start) ?step ?b _ ?init ?loop
      case loop => assumption
      case init => exact ⟨start,hr,Trace.nil⟩
      case step => exact fun i _ s hs out h=>step_inv n allowed reqs key start i s hs out h
    exact hh
end ZkFormal.NearV3.Candidates.ProcModelRng
