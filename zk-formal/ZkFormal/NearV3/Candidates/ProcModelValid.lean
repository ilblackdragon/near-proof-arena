import ZkFormal.NearV3.Candidates.ProcModelStep
import ZkFormal.NearV3.Candidates.ProcRoundBounds
namespace ZkFormal.NearV3.Candidates.ProcModelValid
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def Valid (K z : Nat) : Prop := if K=0 then 0<z else z=0

abbrev ModelAcc := List Push × PState × Nat × List Round × Option (Nat×Nat)
def Inv (s : ModelAcc) : Prop := ∀rd∈s.2.2.2.1,Valid rd.key rd.z

theorem scalar_valid (K z : Nat)
    (hz : (decide (K=0) && decide (z=0)) ≠ true)
    (hp : (decide (K>0) && (z != 0)) ≠ true) : Valid K z := by
  simp only [ne_eq,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at hz hp
  unfold Valid
  split <;> omega

private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

set_option maxHeartbeats 1000000 in
/-- The event model checks the positive/zero ordinal distinction on every
emitted round; early completion preserves the already checked prefix. -/
theorem process_valid (n : Nat) (allowed : Array Bool) (reqs : List NearSpecV3.Scheduler.Req)
    (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h : processEv n allowed reqs st0 fuel=.ok (st,rs)) : ∀rd∈rs,Valid rd.key rd.z := by
  rw [ProcModelStep.process_eq] at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals
    change Inv _
    refine ExceptLoop.invariant (α := Nat) (ε := String) ?xs ?f Inv ?step ?b _ ?init ?loop
    case loop => assumption
    case init => simp [Inv,ProcModelStep.initial]
    case step =>
      intro i hi s hs out ho
      unfold ProcModelStep.step at ho
      simp only [bind,Except.bind,pure,Except.pure,throw_eq] at ho
      split at ho
      all_goals repeat first | cases ho | split at ho
      all_goals repeat first | cases ho | split at ho
      all_goals repeat first | cases ho | split at ho
      all_goals first
        | exact hs
        | simp only [ExceptLoop.StepInv,Inv,List.mem_append,List.mem_singleton]
          intro rd hr
          rcases hr with hr|rfl
          · exact hs rd hr
          · apply scalar_valid <;> assumption

theorem run_valid (I : Input) (tau : Nat) (R : Run) (h : Gen.run I tau=.ok R) :
    ∀rd∈R.rounds,Valid rd.K rd.z := by
  rcases ProcModelRounds.run_model I tau R h with ⟨st,rs,hm,hkeys⟩
  have hv := process_valid _ _ _ _ _ _ _ hm
  intro rd hrd
  have hk : (rd.K,rd.z)∈rs.map (fun r=>(r.key,r.z)) := by
    rw [←hkeys]
    exact List.mem_map_of_mem hrd
  rcases List.mem_map.mp hk with ⟨r,hr,he⟩
  have hh := hv r hr
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  change r.key=rd.K at he1
  change r.z=rd.z at he2
  simpa only [he1,he2] using hh
end ZkFormal.NearV3.Candidates.ProcModelValid
