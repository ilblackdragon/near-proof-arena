import ZkFormal.NearV3.Candidates.ProcActualRun
import ZkFormal.NearV3.Candidates.ProcActualZeroTransition
namespace ZkFormal.NearV3.Candidates.ProcActualZeroTrace
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualZeroPending ProcActualZeroTransition ProcActualModelValid

inductive Trace : Option (Nat×Nat) → List (Nat×Nat) → Prop
  | nil : Trace none []
  | snoc {last : Option (Nat×Nat)} {rs : List (Nat×Nat)} (h : Trace last rs)
      (K z : Nat) (hv : Valid K z) (ho : Ordered last K z)
      (hz : K=0 → z=nextZero last) : Trace (some (K,z)) (rs++[(K,z)])

def Inv (s : ProcActualModelStep.Acc) : Prop :=
  Pending (nextZero s.2.2.2.2) s.1 ∧ Trace s.2.2.2.2 (s.2.2.2.1.map (fun rd=>(rd.key,rd.z)))

private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

set_option maxHeartbeats 1000000 in
theorem step_inv (n : Nat) (allowed : Array Bool) (reqs : List NearSpecV3.Scheduler.Req)
    (i : Nat) (s : ProcActualModelStep.Acc) (hs : Inv s) (out : ForInStep ProcActualModelStep.Acc)
    (h : ProcActualModelStep.step n allowed reqs i s=.ok out) : ExceptLoop.StepInv Inv out := by
  let K := s.1.foldl (fun m p=>Nat.max m p.key) 0
  let z := ((sortTs (s.1.filter (fun p=>p.key==K))).headD default).z
  unfold ProcActualModelStep.step at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | have hv : Valid K z := by apply scalar_valid <;> assumption
      have ho : Ordered s.2.2.2.2 K z := by
        simp_all only [Ordered,ne_eq,Bool.not_eq_true,Bool.not_eq_false,Bool.not_eq_false',Bool.or_eq_true,Bool.and_eq_true,
          decide_eq_true_eq,beq_iff_eq,and_assoc,K,z]
      have hz : K=0 → z=nextZero s.2.2.2.2 := by
        intro hk
        have hp : 0<z := by simpa [Valid,hk] using hv
        change 0<((sortTs (s.1.filter (fun p=>p.key==K))).headD default).z at hp
        change ((sortTs (s.1.filter (fun p=>p.key==K))).headD default).z=nextZero s.2.2.2.2
        rw [hk] at hp ⊢
        exact zero_head _ _ hs.1 hp
      have hf := filtered_pending s.1 s.2.2.2.2 K z hs.1 rfl ho
      refine ⟨?_,?_⟩
      · exact entries_pending n allowed reqs K z _ _ _ hf (by assumption)
      · simp only [List.map_append,List.map_cons,List.map_nil]
        exact Trace.snoc hs.2 K z hv ho hz

set_option maxHeartbeats 400000 in
theorem process_trace (n : Nat) (allowed : Array Bool) (reqs : List NearSpecV3.Scheduler.Req)
    (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h : processEv n allowed reqs st0 fuel=.ok (st,rs)) :
    ∃last,Trace last (rs.map (fun rd=>(rd.key,rd.z))) := by
  rw [ProcActualModelStep.process_eq] at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals
    have hh : Inv ?out := by
      refine ExceptLoop.invariant (α := Nat) (ε := String) ?xs ?f Inv ?step ?b _ ?init ?loop
      case loop => assumption
      case init => exact ⟨initial _ _,Trace.nil⟩
      case step => exact fun i _ s hs out h=>step_inv n allowed reqs i s hs out h
    exact ⟨_,hh.2⟩

theorem run_trace (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau=.ok R) :
    ∃last,Trace last (R.rounds.map (fun rd=>(rd.K,rd.z))) := by
  rcases ProcActualModelRounds.run_model I tau R h with ⟨st,rs,hm,hkeys⟩
  rw [hkeys]
  exact process_trace _ _ _ _ _ _ _ hm
end ZkFormal.NearV3.Candidates.ProcActualZeroTrace
