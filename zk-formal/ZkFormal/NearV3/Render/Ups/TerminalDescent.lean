import ZkFormal.NearV3.Render.Ups.DescentAllocation

namespace ZkFormal.NearV3.Render.UpsGen
open UpsRows

def kindDescents (kinds : List UKind) : Nat := (kinds.filter descendKind).length

theorem descentCount_kinds (parts : List TreePart) : descentCount parts=kindDescents (parts.map TreePart.kind) := by
  induction parts with
  | nil => rfl
  | cons p ps ih =>
    cases hp : descendKind p.kind <;> simp [descentCount,kindDescents,hp] at ih ⊢ <;> omega

theorem termPlan_no_descents (cs : UCase) (matched : Nat) :
    (termPlan cs matched).filter descendKind=[] := by
  cases cs <;> simp [termPlan,UCase.split,descendKind] <;> split <;> simp [descendKind]

theorem termPlan_drop_no_descents (cs : UCase) (matched k : Nat) :
    ((termPlan cs matched).drop k).filter descendKind=[] := by
  have h := termPlan_no_descents cs matched
  rw [List.filter_eq_nil_iff] at h ⊢
  intro p hp
  exact h p (List.mem_of_mem_drop hp)

/-- Every terminal part uses the same source-level counter D. -/
theorem planned_terminal_counter (run : TreeRun) (hp : run.Planned) (k : Nat)
    (hk : k≤(termPlan run.terminal run.matched).length) :
    remainingDescents run.parts k=descentCount run.parts := by
  obtain ⟨upper,he,_⟩ := hp
  unfold remainingDescents
  rw [descentCount_kinds,descentCount_kinds,List.map_drop,he]
  rw [List.drop_append_of_le_length hk]
  simp only [kindDescents,List.filter_append,termPlan_drop_no_descents,termPlan_no_descents,List.nil_append]
end ZkFormal.NearV3.Render.UpsGen
