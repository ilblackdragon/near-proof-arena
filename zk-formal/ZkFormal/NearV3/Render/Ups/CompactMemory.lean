import ZkFormal.NearV3.Render.Ups.CompactBytes
import ZkFormal.NearV3.Render.Ups.GMem
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Near.Render.EvI ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3 UpsGen

theorem compact_cMemCurrent {insts : List UpsInst} (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    (hm : ∀ I ∈ insts, ∀ k, k < nQ I → MemOk I (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cMemCurrent := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have he' : e ∈ UpsV3.cMem := by
      rcases List.mem_append.mp he with he | he
      · exact List.mem_of_mem_take he
      · exact List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [compactConstraints, he'])
  · intro i hi t ht q _ _ C D P hC _ e he
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (by decide : cMemCurrent.all (vz zW (fun _ => false) false false false) = true) e he)
  · intro i hi k p hk hp q _ _ C D P hC _
    have f := hf _ (inst_mem hi) k hk
    have m := hm _ (inst_mem hi) k hk
    have hn := ((hinst _ (inst_mem hi)).bits k hk).2.2.1
    generalize inst insts i = I at *
    generalize part I k = Q at *
    have hb := m.bytes p hp
    have hc := fieldAt_bounds Q.shape p (by rw [← f.bytes]; exact hp)
    have hl := nodeFields_length (by rw [← f.shape]; exact hc.2)
    generalize fieldAt Q.shape p = fa at hC hb hc hl
    obtain ⟨st, ix, fl, wi⟩ := fa
    by_cases hs : st = 8
    · subst st
      have he : fl = 8 := hl.2.2.2.2.2.2.2.2 rfl
      subst fl
      obtain ⟨h0,h1,h2,h3⟩ := m.carries ix hc.1
      exact mem_current hC hc.1 hn h0 h1 h2 h3 (hb rfl)
    · exact mem_non hs hC

theorem compact_cMemCarry {insts : List UpsInst} (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    (hm : ∀ I ∈ insts, ∀ k, k < nQ I → MemOk I (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cMemCarry := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have he' : e ∈ UpsV3.cMem := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [compactConstraints, he'])
  · intro i hi t ht q _ _ C D P hC _ e he
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (by decide : cMemCarry.all (vz zW (fun _ => false) false false false) = true) e he)
  · intro i hi k p hk hp q hq hr C D P hC hD
    by_cases hp1 : p + 1 < (part (inst insts i) k).q.length
    · apply mem_carry_mid (hf _ (inst_mem hi) k hk) (hm _ (inst_mem hi) k hk) hp1 hC
      intro x hx
      rw [hD x hx, compact_nextRow hpos hinst hq hr (rk' := .q k (p + 1))
        (by simp only [compactNext,nextRK]; rw [if_pos hp1]) x, compactRowCell_q]
    · have he : p + 1 = (part (inst insts i) k).q.length := by omega
      exact mem_carry_off hC (.inr (((hinst _ (inst_mem hi)).memEnd k hk p hp).1 he).2)

theorem compact_cMemLengths {insts : List UpsInst} (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cMemLengths := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have he' : e ∈ UpsV3.cMem := List.mem_of_mem_drop he
    simp [compactConstraints, he'])
  · intro i hi t ht q _ _ C D P hC _ e he
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (by decide : cMemLengths.all (vz zW (fun _ => false) false false false) = true) e he)
  · intro i hi k p hk hp q hq hr C D P hC hD
    by_cases hp1 : p + 1 < (part (inst insts i) k).q.length
    · apply mem_lengths_mid (hf _ (inst_mem hi) k hk) hp1 hC
      intro x hx
      rw [hD x hx, compact_nextRow hpos hinst hq hr (rk' := .q k (p + 1))
        (by simp only [compactNext,nextRK]; rw [if_pos hp1]) x, compactRowCell_q]
    · have he : p + 1 = (part (inst insts i) k).q.length := by omega
      have hm := ((hinst _ (inst_mem hi)).memEnd k hk p hp).1 he
      have f := hf _ (inst_mem hi) k hk
      generalize inst insts i = I at *
      generalize part I k = Q at *
      have hc := fieldAt_bounds Q.shape p (by rw [← f.bytes]; exact hp)
      have hl := nodeFields_length (by rw [← f.shape]; exact hc.2)
      have hlen : (fieldAt Q.shape p).2.2.1 = 8 := hl.2.2.2.2.2.2.2.2 hm.1
      have hix : (fieldAt Q.shape p).2.1 = 7 := by omega
      rw [hm.1, hlen, hix] at hC
      exact mem_lengths_last he hC

theorem compact_cMem {insts : List UpsInst} (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    (hm : ∀ I ∈ insts, ∀ k, k < nQ I → MemOk I (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H UpsV3.cMem := by
  have hcur := compact_cMemCurrent hpos hinst hf hm hH
  have hcar := compact_cMemCarry hpos hinst hf hm hH
  have hlen := compact_cMemLengths hpos hinst hf hH
  intro q hq C D P hC hD e he
  change e ∈ ((UpsV3.cMem.take 4 ++ cMemCarry) ++
    (UpsV3.cMem.drop 6).take 5) ++ cMemLengths at he
  rcases List.mem_append.1 he with he | he
  · rcases List.mem_append.1 he with he | he
    · rcases List.mem_append.1 he with he | he
      · exact hcur q hq C D P hC hD e (List.mem_append_left _ he)
      · exact hcar q hq C D P hC hD e he
    · exact hcur q hq C D P hC hD e (List.mem_append_right _ he)
  · exact hlen q hq C D P hC hD e he

end ZkFormal.NearV3.Render.UpsRelay
