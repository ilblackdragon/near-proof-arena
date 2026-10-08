import ZkFormal.NearV3.Candidates.ProcModelRng
namespace ZkFormal.NearV3.Candidates.ProcModelEntryShape
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

def Stamped (start : Nat) (es : List Step) : Prop :=
  ∀i (hi : i<es.length),(es[i]).t=start+i

def Inv (start : Nat) (s : ProcModelStep.EntryAcc) : Prop :=
  s.2.2.1=start+s.2.2.2.length ∧ Stamped start s.2.2.2

theorem stamped_append (start : Nat) (es : List Step) (h : Stamped start es)
    (e : Step) (ht : e.t=start+es.length) : Stamped start (es++[e]) := by
  intro i hi
  by_cases hil : i<es.length
  · rw [List.getElem_append_left hil]
    exact h i hil
  · have he : i=es.length := by simp only [List.length_append,List.length_cons,List.length_nil] at hi; omega
    subst i
    simpa using ht

theorem entry_shape (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z v : Nat) (s : ProcModelStep.EntryAcc) (out : ForInStep ProcModelStep.EntryAcc)
    (h : ProcModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ∃next,out=.yield next ∧ next.2.2.1=s.2.2.1+1 ∧ next.2.2.2.length=s.2.2.2.length+1 := by
  unfold ProcModelStep.entryStep at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals exact ⟨_,rfl,rfl,by simp⟩

theorem entry_inv (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z v start : Nat) (s : ProcModelStep.EntryAcc) (hs : Inv start s)
    (out : ForInStep ProcModelStep.EntryAcc)
    (h : ProcModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ExceptLoop.StepInv (Inv start) out := by
  unfold ProcModelStep.entryStep at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals exact ⟨by simpa [Inv,hs.1,Nat.add_assoc],stamped_append start _ hs.2 _ hs.1⟩

theorem entries_inv (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z start : Nat) (vs : List Nat) (s out : ProcModelStep.EntryAcc) (hs : Inv start s)
    (h : forIn vs s (ProcModelStep.entryStep n allowed reqs K z)=.ok out) : Inv start out :=
  ExceptLoop.invariant vs (ProcModelStep.entryStep n allowed reqs K z) (Inv start)
    (fun v _ s hs out h=>entry_inv n allowed reqs K z v start s hs out h) s out hs h

theorem entries_counts (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z : Nat) (vs : List Nat) (s out : ProcModelStep.EntryAcc)
    (h : forIn vs s (ProcModelStep.entryStep n allowed reqs K z)=.ok out) :
    out.2.2.1=s.2.2.1+vs.length ∧ out.2.2.2.length=s.2.2.2.length+vs.length := by
  induction vs generalizing s with
  | nil => simp only [List.forIn_nil] at h; cases h; simp
  | cons v vs ih =>
    rw [List.forIn_cons] at h
    cases he : ProcModelStep.entryStep n allowed reqs K z v s with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok next =>
      rcases entry_shape n allowed reqs K z v s next he with ⟨next,rfl,ht,hl⟩
      simp only [he,bind,Except.bind] at h
      have hh := ih next h
      simp only [List.length_cons]
      omega
end ZkFormal.NearV3.Candidates.ProcModelEntryShape
