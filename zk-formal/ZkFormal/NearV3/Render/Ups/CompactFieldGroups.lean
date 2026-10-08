import ZkFormal.NearV3.Render.Ups.CompactWalk
import ZkFormal.NearV3.Render.Ups.GFieldsComplete
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Near.Render.EvI ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3 UpsGen

theorem compact_cFieldFrame {insts : List UpsInst} (hpos : 0<insts.length) (hi : ∀I∈insts,InstOk I)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cFieldFrame := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cFields := List.mem_of_mem_take he
    simp [compactConstraints, hm])
  · intro i hi' t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]
      exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cFieldFrame.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi' k p hk hp q _ _ C D P hC _
    exact fields_frame_q (hf _ (inst_mem hi') k hk) hp hC

theorem compact_cFieldLengths {insts : List UpsInst} (hpos : 0<insts.length) (hi : ∀I∈insts,InstOk I)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cFieldLengths := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cFields := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [compactConstraints, hm])
  · intro i hi' t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]
      exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cFieldLengths.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi' k p hk hp q _ _ C D P hC _
    exact fields_lengths_q (hf _ (inst_mem hi') k hk) hp hC

theorem compact_cFieldAdvance {insts : List UpsInst} (hpos : 0<insts.length) (hi : ∀I∈insts,InstOk I)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cFieldAdvance := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cFields := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [compactConstraints, hm])
  · intro i hi' t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]
      exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cFieldAdvance.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi' k p hk hp q hq hr C D P hC hD
    by_cases hp1 : p + 1 < (part (inst insts i) k).q.length
    · apply fields_advance_qmid (hf _ (inst_mem hi') k hk) hp1 hC
      intro x hx
      rw [hD x hx, compact_nextRow hpos hi hq hr (rk' := .q k (p + 1))
        (by simp only [compactNext,nextRK]; rw [if_pos hp1]) x, compactRowCell_q]
    · have he : p + 1 = (part (inst insts i) k).q.length := by omega
      exact fields_advance_qlast he (((hi _ (inst_mem hi')).memEnd k hk p hp).1 he).2 hC

theorem compact_cFieldSucc {insts : List UpsInst} (hpos : 0<insts.length) (hi : ∀I∈insts,InstOk I)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cFieldSucc := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cFields := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [compactConstraints, hm])
  · intro i hi' t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]
      exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cFieldSucc.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi' k p hk hp q hq hr C D P hC hD
    by_cases hp1 : p + 1 < (part (inst insts i) k).q.length
    · apply fields_succ_qmid (hf _ (inst_mem hi') k hk) hp1 hC
      intro x hx
      rw [hD x hx, compact_nextRow hpos hi hq hr (rk' := .q k (p + 1))
        (by simp only [compactNext,nextRK]; rw [if_pos hp1]) x, compactRowCell_q]
    · have he : p + 1 = (part (inst insts i) k).q.length := by omega
      exact fields_succ_qlast (((hi _ (inst_mem hi')).memEnd k hk p hp).1 he).1 hC

theorem compact_cWindowCounts {insts : List UpsInst} (hpos : 0<insts.length) (hi : ∀I∈insts,InstOk I)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    (hw : ∀ I ∈ insts, ∀ k, k < nQ I → WindowOk I (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cWindowCounts := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cFields := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [compactConstraints,hm])
  · intro i hi' t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cWindowCounts.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi' k p hk hp q _ _ C D P hC _
    exact window_counts_q (hf _ (inst_mem hi') k hk) (hw _ (inst_mem hi') k hk) hC

theorem compact_cWindowRoles {insts : List UpsInst} (hpos : 0<insts.length) (hi : ∀I∈insts,InstOk I)
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cWindowRoles := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cFields := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [compactConstraints,hm])
  · intro i hi' t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]
      exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cWindowRoles.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi' k p hk hp q _ _ C D P hC _
    exact window_roles_q hC

theorem compact_cWindowChild {insts : List UpsInst} (hpos : 0<insts.length) (hi : ∀I∈insts,InstOk I)
    (hw : ∀ I ∈ insts, ∀ k, k < nQ I → WindowOk I (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cWindowChild := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cFields := List.mem_of_mem_drop he
    simp [compactConstraints,hm])
  · intro i hi' t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cWindowChild.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi' k p hk hp q _ _ C D P hC _
    exact window_child_q (hw _ (inst_mem hi') k hk) hp hC

end ZkFormal.NearV3.Render.UpsRelay
