import ZkFormal.NearV3.Render.Ups.CompactDispatch
import ZkFormal.NearV3.Render.Ups.GRows
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Near.Render.EvI ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3 UpsGen

theorem compactRowCell_seg {insts : List UpsInst} {q x : Nat} {r : Nat×RK}
    (h : isSeg x=true) : compactRowCell insts q r x=segCell (inst insts r.1) x := by
  simp only [compactRowCell,h,ite_true]

theorem compact_cConst {insts : List UpsInst} (hpos : 0<insts.length)
    (hi : ∀I∈insts,InstOk I) {H : Nat} (hH : compactR insts+1≤H) :
    CompactGroupOk insts H UpsV3.cConst := by
  apply compact_groupOk_by hpos hH (fun e he=>by simp [compactConstraints,he])
  all_goals intro i hi'
  · intro t ht q hq hr C D P hC hD ex hex
    simp only [UpsV3.cConst, List.mem_append, List.mem_map] at hex
    have hn : ∀ x, x < 200 → D x = compactRowCell insts (q + 1) (i, if t < 3 then .w (t + 1) else .q 0 0) x := by
      intro x hx; rw [hD x hx]
      exact compact_nextRow hpos hi hq hr (by simp only [compactNext,nextRK]; split <;> split <;> first | rfl | omega) x
    rcases hex with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · refine const_ev (.inr ?_)
      have hs := segConst_isSeg x hx; have hl := segConst_lt x hx
      rw [hn x hl, hC x hl, compactRowCell_seg hs]; simp only [WC, hs, ite_true]
    · rw [mul3_eq]; refine const_ev (.inl ?_)
      obtain ⟨-, -, hl⟩ := partConst_isPC x hx
      simp only [ev, Dsl.c, Dsl.not, Dsl.sub, Dsl.k, vb, qb, pl, Bool.false_eq_true, ite_false]
      rw [hC 2 (by decide), hC 3 (by decide)]; simp [WC, isSeg, wCell]
  · intro k p hk hp q hq hr C D P hC hD ex hex
    simp only [UpsV3.cConst, List.mem_append, List.mem_map] at hex
    have hpl : C 9 = ind (p + 1 = (part (inst insts i) k).q.length) := by rw [hC 9 (by decide)]; rfl
    have hrp : C 79 = ind (k + 1 = nQ (inst insts i)) := by rw [hC 79 (by decide)]; rfl
    have h0 : C 0 = 1 := by rw [hC 0 (by decide)]; rfl
    have h3 : C 3 = 1 := by rw [hC 3 (by decide)]; rfl
    have h2 : C 2 = 0 := by rw [hC 2 (by decide)]; rfl
    rcases hex with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · have hs := segConst_isSeg x hx; have hl := segConst_lt x hx
      by_cases hlast : p + 1 = (part (inst insts i) k).q.length ∧ k + 1 = nQ (inst insts i)
      · refine const_ev (.inl ?_)
        simp only [ev, Dsl.c, Dsl.sub, Dsl.mul3, Bool.false_eq_true, ite_false, act, qb, pl, rootP]
        rw [h0, h3, hpl, hrp, ind_pos hlast.1, ind_pos hlast.2]; rfl
      · refine const_ev (.inr ?_)
        have hn : compactNext (inst insts i) (.q k p) = some (if p + 1 < (part (inst insts i) k).q.length
            then .q k (p + 1) else .q (k + 1) 0) := by
          simp only [compactNext,nextRK]; split
          · rfl
          · rw [if_pos (by omega)]
        rw [hD x hl, compact_nextRow hpos hi hq hr hn x, hC x hl, compactRowCell_seg hs]; simp only [QC, hs, ite_true]
    · rw [mul3_eq]
      obtain ⟨hpc, hs, hl⟩ := partConst_isPC x hx
      by_cases hp1 : p + 1 < (part (inst insts i) k).q.length
      · refine const_ev (.inr ?_)
        rw [hD x hl, compact_nextRow hpos hi hq hr (rk' := .q k (p + 1)) (by simp only [compactNext,nextRK]; rw [if_pos hp1]) x,
          hC x hl]
        simp only [compactRowCell, qCell, QC, hs, hpc, Bool.false_eq_true, ite_false, ite_true]
      · refine const_ev (.inl ?_)
        simp only [ev, Dsl.c, Dsl.not, Dsl.sub, Dsl.k, vb, qb, pl, Bool.false_eq_true, ite_false]
        rw [h2, h3, hpl, ind_pos (by omega)]; rfl


end ZkFormal.NearV3.Render.UpsRelay
