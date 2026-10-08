import ZkFormal.NearV3.Render.Ups.CompactCurrentGroups
import ZkFormal.NearV3.Render.Ups.GDig
import ZkFormal.NearV3.Render.Ups.GSeg

set_option maxHeartbeats 1000000
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Near.Render.EvI ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3 UpsGen

theorem compact_cSeg {insts : List UpsInst} (hpos : 0<insts.length)
    (hi : ∀I∈insts,InstOk I) {H : Nat} (hH : compactR insts+1≤H) :
    CompactGroupOk insts H UpsV3.cSeg := by
  apply compact_current_group hpos hH (fun e he=>by simp [compactConstraints,he])
  · intro i hi' t ht C D P fst lst trn hC ex hex
    by_cases h0 : t=0
    · subst t; exact seg_w0 (hi _ (inst_mem hi')) hC ex hex
    · refine vzC (zc := fun x => zW x || x == 4) (fun x hx => ?_)
        (List.all_eq_true.1 (show UpsV3.cSeg.all (vz (fun x => zW x || x == 4) (fun _ => false) false false false) = true
          by decide) ex hex)
      simp only [Bool.or_eq_true, beq_iff_eq] at hx
      rcases hx with hx | rfl
      · rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx
      · rw [hC 4 (by decide)]; simp [WC, isSeg, wCell, ind]; omega
  · intro i hi' k p hk hp u C D P fst lst trn hC ex hex
    refine vzC (zc := zQ) (fun x hx => ?_)
      (List.all_eq_true.1 (show UpsV3.cSeg.all (vz zQ (fun _ => false) false false false) = true by decide) ex hex)
    rw [hC x (by simp [zQ] at hx; omega)]; exact zQ_cell _ _ _ _ _ _ _ _ _ _ hx

theorem compact_cDigest {insts : List UpsInst} (hpos : 0<insts.length)
    (hi : ∀I∈insts,InstOk I) {H : Nat} (hH : compactR insts+1≤H) :
    CompactGroupOk insts H UpsV3.cDigest := by
  apply compact_current_group hpos hH (fun e he=>by simp [compactConstraints,he])
  · intro i hi' t ht C D P fst lst trn hC ex hex
    apply cast0
    simp only [UpsV3.cDigest, List.mem_cons, List.not_mem_nil, or_false] at hex
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl | rfl <;>
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ups_ev [hC] <;> cellsimp <;>
      simp [ind, upsIdV] <;> omega
  · intro i hi' k p hk hp u C D P fst lst trn hC ex hex
    apply cast0
    have hLs := (hi _ (inst_mem hi')).Lsmall
    generalize inst insts i = I at *
    generalize part I k = Q at hC
    generalize fieldAt Q.shape p = fa at hC
    obtain ⟨st, ix, fl, wi⟩ := fa
    simp only [UpsV3.cDigest, List.mem_cons, List.not_mem_nil, or_false] at hex
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ups_ev [hC] <;> cellsimp
    · simp only [gDV, winFrV, cpV, wfrV, GdB, WinFrB, ind]
      by_cases h4 : CpB I Q st wi = true <;> by_cases h5 : WfrB I Q st wi = true <;>
        simp only [h4, h5, Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false, Bool.or_false,
          Bool.false_or, Bool.true_and, Bool.false_and, ite_true, ite_false, Bool.false_eq_true,
          Bool.not_eq_true'] <;>
        by_cases h1 : ix = 0 <;> by_cases h2 : st = 5 <;> by_cases h3 : st = 7 <;> simp [h1, h2, h3] <;> omega
    · simp only [gDV, dIV, upsIdV, ind]
      by_cases h1 : GdB I Q st ix wi = true <;> simp only [h1, ite_true, ite_false] <;>
        by_cases h2 : st = 5 <;> simp [h2] <;> omega
    · simp only [gDV, dLV, ind]
      by_cases h1 : GdB I Q st ix wi = true <;> simp only [h1, ite_true, ite_false] <;>
        by_cases h2 : st = 5 <;> simp [h2]
      have := Lb_sum I hLs; omega
    · simp only [gDV, dIV, upsIdV, wnV, ind]
      by_cases h1 : GdB I Q st ix wi = true <;> by_cases h3 : WnB I Q st wi = true <;>
        simp only [h1, h3, ite_true, ite_false] <;> by_cases h2 : st = 5 <;> by_cases h2' : st = 7 <;>
        simp [h2, h2'] <;> omega
    · simp only [gDV, dLV, wnV, ind]
      by_cases h1 : GdB I Q st ix wi = true <;> by_cases h3 : WnB I Q st wi = true <;>
        simp only [h1, h3, ite_true, ite_false] <;> by_cases h2 : st = 5 <;> by_cases h2' : st = 7 <;>
        simp [h2, h2'] <;> omega
    · simp only [gDV, dIV, upsIdV, wnV, ind]
      by_cases h1 : GdB I Q st ix wi = true <;> by_cases h3 : WnB I Q st wi = true <;>
        simp only [h1, h3, ite_true, ite_false] <;> by_cases h2 : st = 5 <;> by_cases h2' : st = 7 <;>
        simp [h2, h2'] <;> omega
    · simp only [gDV, dLV, wnV, ind]
      by_cases h1 : GdB I Q st ix wi = true <;> by_cases h3 : WnB I Q st wi = true <;>
        simp only [h1, h3, ite_true, ite_false] <;> by_cases h2 : st = 5 <;> by_cases h2' : st = 7 <;>
        simp [h2, h2'] <;> omega

end ZkFormal.NearV3.Render.UpsRelay
