import ZkFormal.NearV3.Render.Ups.CompactFieldGroups
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Near.Render.EvI ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3 UpsGen
theorem compact_cWindowFlow {insts : List UpsInst} (hpos : 0<insts.length) (hi : ∀I∈insts,InstOk I)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cWindowFlow := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cFields := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [compactConstraints,hm])
  · intro i hi' t ht q hq hr C D P hC hD
    apply window_flow_off
    · simp only [sCH]; rw [hC _ (by decide)]; rfl
    · simp only [sCH]; rw [hD _ (by decide)]
      by_cases h3 : t < 3
      · rw [compact_nextRow hpos hi hq hr (rk' := .w (t+1)) (by simp only [compactNext]; rw [ite_eq_left (by omega)]),compactRowCell_w]; rfl
      · rw [compact_nextRow hpos hi hq hr (rk' := .q 0 0)
          (by simp only [compactNext]; rw [ite_eq_right (by omega)]),compactRowCell_q]
        rw [(hf _ (inst_mem hi') 0 (hi _ (inst_mem hi')).nQ1).first]
        rfl
  · intro i hi' k p hk hp q hq hr C D P hC hD
    by_cases hp1 : p+1 < (part (inst insts i) k).q.length
    · apply window_flow_qmid (hf _ (inst_mem hi') k hk) hC
      intro x hx
      rw [hD x hx,compact_nextRow hpos hi hq hr (rk' := .q k (p+1)) (by simp [compactNext,nextRK,hp1]),compactRowCell_q]
    · apply window_flow_off
      · have hl : p+1 = (part (inst insts i) k).q.length := by omega
        have hs := (((hi _ (inst_mem hi')).memEnd k hk p hp).1 hl).1
        simp only [sCH]; rw [hC _ (by decide)]; cellsimp; simp [ind,hs]
      · simp only [sCH]; rw [hD _ (by decide)]
        by_cases hk1 : k+1 < nQ (inst insts i)
        · rw [compact_nextRow hpos hi hq hr (rk' := .q (k+1) 0) (by simp [compactNext,nextRK,hp1,hk1]),compactRowCell_q]
          rw [(hf _ (inst_mem hi') (k+1) hk1).first]
          rfl
        · have hn : compactNext (inst insts i) (.q k p) = none := by simp [compactNext,nextRK,hp1,hk1]
          rcases compact_nextLastAll hi hr hn with h | h
          · exact h 113
          · rw [h,compactRowCell_w]; rfl

theorem compact_groupOk_append {insts : List UpsInst} {H : Nat} {a b : List Expr}
    (ha : CompactGroupOk insts H a) (hb : CompactGroupOk insts H b) :
    CompactGroupOk insts H (a++b) := by
  intro q hq C D P hC hD e he
  rcases List.mem_append.mp he with he|he
  · exact ha q hq C D P hC hD e he
  · exact hb q hq C D P hC hD e he

theorem compact_cFields {insts : List UpsInst} (hpos : 0<insts.length)
    (hi : ∀I∈insts,InstOk I)
    (hf : ∀I∈insts,∀k,k<nQ I → FieldsOk (part I k))
    (hw : ∀I∈insts,∀k,k<nQ I → WindowOk I (part I k))
    {H : Nat} (hH : compactR insts+1≤H) : CompactGroupOk insts H UpsV3.cFields := by
  change CompactGroupOk insts H
    (((((((cFieldFrame++cFieldAdvance)++cFieldLengths)++cFieldSucc)++cWindowFlow)++cWindowCounts)++cWindowRoles)++cWindowChild)
  exact compact_groupOk_append (compact_groupOk_append (compact_groupOk_append
    (compact_groupOk_append (compact_groupOk_append (compact_groupOk_append
      (compact_groupOk_append (compact_cFieldFrame hpos hi hf hH) (compact_cFieldAdvance hpos hi hf hH))
      (compact_cFieldLengths hpos hi hf hH)) (compact_cFieldSucc hpos hi hf hH))
      (compact_cWindowFlow hpos hi hf hH)) (compact_cWindowCounts hpos hi hf hw hH))
      (compact_cWindowRoles hpos hi hH)) (compact_cWindowChild hpos hi hw hH)
end ZkFormal.NearV3.Render.UpsRelay
