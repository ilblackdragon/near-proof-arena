import ZkFormal.NearV3.Candidates.ProcRequestPointers
namespace ZkFormal.NearV3.Candidates.ProcEntryPointers
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcRequestPointers

def Inv (reqs : List Req) (s : ProcModelStep.EntryAcc) : Prop :=
  (∀p∈s.1,Valid reqs p.v) ∧ (∀e∈s.2.2.2,Valid reqs e.v)

theorem entry_inv (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z v : Nat) (hs : Small reqs) (hv : Valid reqs v)
    (s : ProcModelStep.EntryAcc) (hS : Inv reqs s)
    (out : ForInStep ProcModelStep.EntryAcc)
    (h : ProcModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ExceptLoop.StepInv (Inv reqs) out := by
  unfold ProcModelStep.entryStep at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals
    simp only [ExceptLoop.StepInv,Inv,List.mem_append,List.mem_singleton]
    constructor
    · intro p hp
      first
      | exact hS.1 p hp
      | rcases hp with hp|rfl
        · exact hS.1 p hp
        · apply next_valid reqs v hs hv
          simp_all only [Bool.true_and,Bool.false_and,Bool.false_eq_true,Bool.not_eq_true']
    · intro e he
      rcases he with he|rfl
      · exact hS.2 e he
      · exact hv

theorem entries_inv (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z : Nat) (vs : List Nat) (hs : Small reqs)
    (hv : ∀v∈vs,Valid reqs v) (s out : ProcModelStep.EntryAcc)
    (hS : Inv reqs s)
    (h : forIn vs s (ProcModelStep.entryStep n allowed reqs K z)=.ok out) : Inv reqs out :=
  ExceptLoop.invariant vs (ProcModelStep.entryStep n allowed reqs K z) (Inv reqs)
    (fun v hm s hS out h=>entry_inv n allowed reqs K z v hs (hv v hm) s hS out h) s out hS h
end ZkFormal.NearV3.Candidates.ProcEntryPointers
