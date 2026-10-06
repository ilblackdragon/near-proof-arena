import ZkFormal.NearV3.Render.Ups.Tac

/-!
# ZkFormal.NearV3.Render.Ups.GDig — `cDigest` on the honest table

The digest lookups: `gD` is the fresh-window start (`qb·fs·winFr`) or `W3`; the id and length
of a lookup are the value's (`VH`), the new leaf's (`wn`) or the `MEMD` child's; `W3` looks up
the root part (`upsId nQ`, `rlen`).  The value length `L < 2^24` makes `L0 + 256 L1 + 65536 L2 = L`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

namespace UpsGen

theorem Lb_sum (I : UpsInst) (h : L I < 2 ^ 24) : Lb I 0 + 256 * Lb I 1 + 65536 * Lb I 2 = (L I : Int) := by
  simp only [Lb]; simp; omega

/-- **`cDigest`.** -/
theorem cDigest_ok {insts : List UpsInst} (ok : UpsOk insts) {H : Nat}
    (hH : R insts + 1 ≤ H) : GroupOk insts H UpsV3.cDigest := by
  apply groupOk_by ok hH (fun e he => by simp [UpsV3.constraints, he])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    apply cast0
    simp only [UpsV3.cDigest, List.mem_cons, List.not_mem_nil, or_false] at hex
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl | rfl <;>
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ups_ev [hC] <;> cellsimp <;>
      simp [ind, upsIdV] <;> omega
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _ C D P hC _ ex hex
    apply cast0
    have hLs := (ok.inst _ (inst_mem hi)).Lsmall
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

end UpsGen

end ZkFormal.NearV3.Render
