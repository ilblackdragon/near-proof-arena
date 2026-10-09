import ZkFormal.NearV3.Candidates.ProcNativeBucketReplay
namespace ZkFormal.NearV3.Candidates.ProcPendingTime
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

def Inv (ps : List Push) (t : Nat) : Prop :=
  ps.Pairwise (fun p q=>p.ts<q.ts) ∧ ∀p∈ps,p.ts<t

theorem append (ps : List Push) (t : Nat) (h : Inv ps t) (p : Push) (hp : p.ts=t) :
    Inv (ps++[p]) (t+1) := by
  refine ⟨List.pairwise_append.mpr ⟨h.1,by simp,?_⟩,?_⟩
  · intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    rw [hp]
    exact h.2 a ha
  · intro a ha
    simp only [List.mem_append,List.mem_singleton] at ha
    rcases ha with ha|rfl
    · have := h.2 a ha; omega
    · omega

theorem initial (reqs : List Req) (st : PState) :
    Inv (ProcModelStep.initial reqs st).1 reqs.length := by
  constructor
  · apply List.pairwise_filterMap.mpr
    apply List.pairwise_lt_range.imp
    intro i j hij p hp q hq
    dsimp only at hp hq
    split at hp
    · contradiction
    · cases hp
      split at hq
      · contradiction
      · cases hq; exact hij
  · intro p hp
    obtain ⟨i,hi,hp⟩ := List.mem_filterMap.mp hp
    dsimp only at hp
    split at hp
    · contradiction
    · cases hp; exact List.mem_range.mp hi

theorem entry_inv (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z v : Nat) (s : ProcModelStep.EntryAcc) (hs : Inv s.1 s.2.2.1)
    (out : ForInStep ProcModelStep.EntryAcc)
    (h : ProcModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ExceptLoop.StepInv (fun s=>Inv s.1 s.2.2.1) out := by
  unfold ProcModelStep.entryStep at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact append _ _ hs _ rfl
    | exact ⟨hs.1,fun p hp=>Nat.lt_trans (hs.2 p hp) (Nat.lt_succ_self _)⟩

theorem entries_inv (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z : Nat) (vs : List Nat) (s out : ProcModelStep.EntryAcc)
    (hs : Inv s.1 s.2.2.1)
    (h : forIn vs s (ProcModelStep.entryStep n allowed reqs K z)=.ok out) : Inv out.1 out.2.2.1 :=
  ExceptLoop.invariant vs (ProcModelStep.entryStep n allowed reqs K z) (fun s=>Inv s.1 s.2.2.1)
    (fun v _ s hs out h=>entry_inv n allowed reqs K z v s hs out h) s out hs h
end ZkFormal.NearV3.Candidates.ProcPendingTime
