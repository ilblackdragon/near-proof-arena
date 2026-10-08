import ZkFormal.NearV3.Candidates.HorizontalProfile
namespace ZkFormal.NearV3.Candidates.HorizontalAuxCheck
open ZkFormal.Air HorizontalTables HorizontalProfile
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem fused_aux_degree : (fuse selected).auxDegree 2=8 := by
  rw [auxDegree_eq,fuse_profiles]
  decide +kernel

theorem selected_constraints : selected.all (fun T=>T.allConstraints.all
    (fun e=>decide (e.degree≤8)))=true := by decide +kernel

theorem fused_degree : (fuse selected).degree 2=8 := by
  have hc : ∀ e∈(fuse selected).allConstraints, e.degree≤8 :=
    fused_constraint_bound selected 8 (by
      intro T hT e he
      exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp selected_constraints T hT) e he))
  have fold : ∀ xs : List Nat, (∀ x∈xs,x≤8)→xs.foldr max 2≤8 := by
    intro xs
    induction xs with
    | nil => intro _; decide
    | cons x xs ih => intro h; exact Nat.max_le.mpr ⟨h x (by simp), ih (by intro y hy; exact h y (by simp [hy]))⟩
  unfold Table.degree
  rw [fused_aux_degree]
  exact Nat.max_eq_left (fold _ (by intro x hx; obtain ⟨e,he,rfl⟩:=List.mem_map.mp hx; exact hc e he))

theorem fused_shape : ZkFormal.Size.shapeOf 2 (fuse selected)=⟨3372,106,7,106,22⟩ := by
  unfold ZkFormal.Size.shapeOf Table.quotCount
  rw [fused_degree,auxCount_eq,numSide_eq,numSide_eq,fuse_profiles]
  decide +kernel
end ZkFormal.NearV3.Candidates.HorizontalAuxCheck
