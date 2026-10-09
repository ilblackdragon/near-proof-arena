import ZkFormal.NearV3.Render.Ups.CompactRowsLocal
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Near.Render.EvI ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3 UpsGen

theorem compactRowCell_w (insts : List UpsInst) (q i t x : Nat) :
    compactRowCell insts q (i,.w t) x=WC (inst insts i) t x := rfl

theorem compactRowCell_q (insts : List UpsInst) (q i k p x : Nat) :
    compactRowCell insts q (i,.q k p) x=QC (inst insts i) (part (inst insts i) k) k p
      (fieldAt (part (inst insts i) k).shape p).1
      (fieldAt (part (inst insts i) k).shape p).2.1
      (fieldAt (part (inst insts i) k).shape p).2.2.1
      (fieldAt (part (inst insts i) k).shape p).2.2.2 (compactU insts q) x := rfl

theorem compact_cRows {insts : List UpsInst} (hpos : 0<insts.length)
    (hi : ∀I∈insts,InstOk I) {H : Nat} (hH : compactR insts+1≤H) :
    CompactGroupOk insts H compactRows := by
  apply compact_groupOk_by hpos hH (fun e he=>by simp [compactConstraints,he])
  all_goals intro i hi'
  · intro t ht q hq hr C D P hC hD ex hex
    have hn : ∀ rk', compactNext (inst insts i) (.w t) = some rk' → ∀ x, x < 200 → D x = compactRowCell insts (q + 1) (i, rk') x :=
      fun rk' h x hx => by rw [hD x hx]; exact compact_nextRow hpos hi hq hr h x
    by_cases ht3 : t=3
    · subst t
      have hf : (if q=0 then (1:Int) else 0)=0 := by rw [if_neg (compact_q_ne0 hpos hr (by decide))]
      rw [hf]
      exact compactRows_w3 hC (fun x hx=>by rw [hn (.q 0 0) rfl x hx]; rfl) ex hex
    refine compactRows_old (by rw [hC vb (by decide)]; rfl) (by rw [hC wt3 (by decide)]; simp [wt3,WC,isSeg,wCell,ind,ht3]) ?_ ex hex
    intro ex hex
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl | rfl
    · exact rows_w0 hC (fun x hx => by rw [hn (.w 1) rfl x hx, compactRowCell_w]) ex hex
    · exact rows_w1 (by rw [if_neg (compact_q_ne0 hpos hr (by decide))]) hC
        (fun x hx => by rw [hn (.w 2) rfl x hx, compactRowCell_w]) ex hex
    · exact rows_w2 (by rw [if_neg (compact_q_ne0 hpos hr (by decide))]) hC
        (fun x hx => by rw [hn (.w 3) rfl x hx, compactRowCell_w]) ex hex
    · exact False.elim (ht3 rfl)
  · intro k p hk hp q hq hr C D P hC hD ex hex
    refine compactRows_old (by rw [hC vb (by decide)]; rfl) (by rw [hC wt3 (by decide)]; rfl) ?_ ex hex
    intro ex hex
    have iok := hi _ (inst_mem hi')
    have hf : (if q = 0 then (1 : Int) else 0) = 0 := by rw [if_neg (compact_q_ne0 hpos hr (by simp))]
    have hfa := iok.memEnd k hk p hp
    by_cases hp1 : p + 1 < (part (inst insts i) k).q.length
    · refine rows_qmid hp1 hfa hf (fun h => ?_) hC (fun x hx => by
        rw [hD x hx, compact_nextRow hpos hi hq hr (rk' := .q k (p + 1)) (by simp only [compactNext,nextRK]; rw [if_pos hp1]) x,
          compactRowCell_q]) ex hex
      have e : k = nQ (inst insts i) - 1 := by omega
      subst e; exact ⟨iok.rootDep, iok.rootSN, rfl⟩
    · by_cases hk1 : k + 1 < nQ (inst insts i)
      · exact rows_qpart (by omega) hk1 hfa hf (iok.rcStep k hk1) (iok.cNStep k hk1) hC (fun x hx => by
          rw [hD x hx, compact_nextRow hpos hi hq hr (rk' := .q (k + 1) 0)
            (by simp only [compactNext,nextRK]; rw [if_neg hp1, if_pos hk1]) x, compactRowCell_q]) ex hex
      · have e : k = nQ (inst insts i) - 1 := by omega
        have hDa : D 0 = D 4 := by
          have hn : compactNext (inst insts i) (.q k p) = none := by simp only [compactNext,nextRK]; rw [if_neg hp1, if_neg hk1]
          rw [hD 0 (by decide), hD 4 (by decide)]
          rcases compact_nextLastAll hi hr hn with h | h <;> rw [h, h] <;> rfl
        subst e
        exact rows_qlast (by omega) (by omega) hfa hf iok.rootRc iok.rootDep iok.rootSN rfl hC hDa ex hex

end ZkFormal.NearV3.Render.UpsRelay
