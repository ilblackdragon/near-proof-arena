import ZkFormal.NearV3.Candidates.ProcActualGrantMemory
import ZkFormal.NearV3.Candidates.ProcActualReplayAllowance
namespace ZkFormal.NearV3.Candidates.ProcActualGrantOperands
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualReplayEntry

def Values (B : Nat) (o : Gen.MOp) : Prop := o.op=OP_GRANT → o.vin<B ∧ o.inc<B

def Logs (B : Nat) (logs : Array (Array Gen.MOp)) : Prop :=
  ∀ops∈logs.toList,∀o∈ops.toList,Values B o

theorem modify_values (B : Nat) (logs : Array (Array Gen.MOp)) (i : Nat) (o : Gen.MOp)
    (h : Logs B logs) (ho : Values B o) : Logs B (logs.modify i (·.push o)) := by
  intro ops hm
  obtain ⟨j,hj,he⟩ := List.getElem_of_mem hm
  have hj' : j<logs.size := by simpa using hj
  have h0 := h _ (Array.getElem_mem_toList hj')
  subst ops
  simp only [Array.getElem_toList,Array.getElem_modify]
  split
  · intro a ha
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at ha
    rcases ha with ha|rfl
    · exact h0 a ha
    · exact ho
  · exact h0

def Inv (B : Nat) (s : Acc) : Prop :=
  (∀i,s.1[i]!<B) ∧ (∀i,s.2.1[i]!<B) ∧ (∀i,s.2.2.1[i]!<B) ∧
  Logs B s.2.2.2.2.1 ∧ Logs B s.2.2.2.2.2.1 ∧ Logs B s.2.2.2.2.2.2.1

theorem set_sub (B : Nat) (a : Array Nat) (ha : ∀i,a[i]!<B)
    (i inc : Nat) (ok : Bool) :
    ∀j,(a.set! i (if ok then a[i]!-inc else a[i]!))[j]!<B := by
  intro j
  by_cases hij : i=j
  · subst j
    by_cases hi : i<a.size
    · rw [Array.getElem!_set!_self a i _ hi]
      have := ha i
      split <;> omega
    · rw [Array.set!_eq_setIfInBounds,Array.setIfInBounds_eq_of_size_le (by omega)]
      exact ha i
  · rw [Array.getElem!_set!_ne a i j _ hij]
    exact ha j

set_option maxHeartbeats 800000 in
theorem step_values (B : Nat) (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat)
    (T x : Nat) (s out : Acc) (hs : Inv B s)
    (hc : ∀i j,cv[i]!.incs[j]!<B)
    (h : step I cv rd sh T x s=.ok (.yield out)) : Inv B out := by
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,used,gi,es⟩
  rcases hs with ⟨hs,hr,ha,hl,hos,hor⟩
  unfold step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals
    refine ⟨set_sub B sb hs _ _ _,set_sub B rb hr _ _ _,set_sub B aa ha _ _ _,
      modify_values B ol _ _ hl ?_,modify_values B os _ _ hos ?_,
      modify_values B orr _ _ hor ?_⟩
    all_goals exact fun _=>⟨by apply_assumption, hc _ _⟩
end ZkFormal.NearV3.Candidates.ProcActualGrantOperands
