import ZkFormal.NearV3.Candidates.ProcReplayDecisions
namespace ZkFormal.NearV3.Candidates.ProcReplayAllowance
open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcReplayChain ProcReplayShape

def Bounded (M : Nat) (a : Array Nat) : Prop := ∀i : Nat,a[i]!≤M

theorem link_bound (n : Nat) (p : NearSpecV3.Scheduler.Params) (allowed : Array Bool) (a0 : Array Nat) :
    Bounded p.maxAllowance (linkPass n p allowed a0).a2 := by
  intro i
  simp only [linkPass,getElem!_def,Array.getElem?_map]
  split
  · next h =>
    simp only [Option.map_eq_some_iff] at h
    rcases h with ⟨l,hl,rfl⟩
    have hb (a b M : Nat) (v : Bool) : (if v then Nat.min a M-b else Nat.min a M)≤M := by
      split
      · exact Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_right _ _)
      · exact Nat.min_le_right _ _
    exact hb _ _ _ _
  · exact Nat.zero_le _

theorem set_bound (M : Nat) (a : Array Nat) (h : Bounded M a) (i v : Nat) (hv : v≤M) :
    Bounded M (a.set! i v) := by
  intro j
  by_cases hij : i=j
  · subst j
    by_cases hi : i<a.size
    · rw [Array.getElem!_set!_self a i v hi]
      exact hv
    · rw [Array.set!_eq_setIfInBounds,Array.setIfInBounds_eq_of_size_le (by omega)]
      exact h i
  · rw [Array.getElem!_set!_ne a i j v hij]
    exact h j

theorem decrease_bound (M : Nat) (a : Array Nat) (h : Bounded M a) (i inc : Nat) (ok : Bool) :
    (if ok then a[i]!-inc else a[i]!)≤M := by
  have hh := h i
  split <;> omega

def EntryInv (M : Nat) (s : EntryAcc) : Prop :=
  Bounded M s.2.2.1 ∧ ∀e∈s.2.2.2.2.2.2.2.2.2.2.toList,e.alOut≤M

def Inv (M : Nat) (s : ReplayAcc) : Prop :=
  Bounded M s.2.2.1 ∧
  ∀rd∈s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.toList,∀e∈rd.entries,e.alOut≤M

set_option maxHeartbeats 1000000 in
/-- Every actual emitted allowance is bounded by the configured maximum:
initial clamping and subsequent native subtraction suffice, without AIR premises. -/
theorem run_allowances (I : Input) (tau : Nat) (R : Run) (h : Gen.run I tau=.ok R) :
    ∀rd∈R.rounds,∀e∈rd.entries,e.alOut≤I.p.maxAllowance := by
  unfold Gen.run at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals
    have hall : Inv I.p.maxAllowance ?out := by
      refine ExceptLoop.invariant (α := Round) (ε := String) ?xs ?f (Inv I.p.maxAllowance) ?step ?b _ ?init ?loop
      case loop => assumption
      case init => exact ⟨link_bound _ _ _ _,by simp⟩
      case step =>
        intro rd hrd s hs out ho
        repeat first | cases ho | split at ho
        all_goals
          rename_i entryOut hentry
          have hi : EntryInv I.p.maxAllowance entryOut := by
            refine ExceptLoop.invariant (α := Nat) (ε := String) ?exs ?ef (EntryInv I.p.maxAllowance) ?estep ?eb _ ?einit ?eloop
            case eloop => exact hentry
            case einit => exact ⟨hs.1,by simp⟩
            case estep =>
              intro i hil st hst eo heo
              repeat first | cases heo | split at heo
              all_goals repeat first | cases heo | split at heo
              all_goals
                refine ⟨?_,?_⟩
                · apply set_bound _ _ hst.1
                  exact decrease_bound _ _ hst.1 _ _ _
                · simp only [Array.toList_push,List.mem_append,List.mem_singleton]
                  intro e he
                  rcases he with he|rfl
                  · exact hst.2 e he
                  · exact decrease_bound _ _ hst.1 _ _ _
          refine ⟨hi.1,?_⟩
          simp only [Array.toList_push,List.mem_append,List.mem_singleton]
          intro r hr
          rcases hr with hr|rfl
          · exact hs.2 r hr
          · exact hi.2
    exact hall.2
end ZkFormal.NearV3.Candidates.ProcReplayAllowance
