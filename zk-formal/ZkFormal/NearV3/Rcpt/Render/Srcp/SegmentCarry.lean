import ZkFormal.NearV3.Rcpt.Render.Srcp.SegmentFacts

namespace ZkFormal.NearV3.Render.SrcpGen

/-- Each active row either disables segment carry or keeps its segment constants. -/
theorem segment_carry_cases {bs : List SrcpB} (h : SrcpWf bs) (H r : Nat)
    (hH : R bs ≤ H) (hr : r < R bs) :
    cell bs r SrcpV3.sg = 0 ∨ cell bs r SrcpV3.sl = 1 ∨
      (∀ x ∈ SrcpV3.segConst, cell bs ((r + 1) % H) x = cell bs r x) := by
  by_cases hn : r + 1 < R bs
  · have hm : (r + 1) % H = r + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hm]
    rcases adjAt hn with ⟨hk, hi⟩ | ⟨hk, _⟩
    · have hs := internal_segment _ (before bs ((recs bs).getD r default).1)
        _ _ (mem_recs (descriptor_mem hr)).2 hk
      rcases hs with hSg | hWl | hReg
      · left
        simp only [cell, hr, ite_true, rowFrame]
        change ((frame _ _ _).sg).toNat = 0
        rw [hSg]; rfl
      · right; left
        simp only [cell, hr, ite_true, rowFrame]
        change ((frame _ _ _).sl).toNat = 1
        rw [hWl]; rfl
      · right; right
        intro x hx
        simp only [cell, hr, hn, ite_true, rowFrame]
        rw [segment_gz _ _ x hx]
        conv => rhs; rw [segment_gz _ _ x hx]
        rw [hi]
        exact hReg x hx
    · right; left
      have hlast := none_last _ _ (mem_recs (descriptor_mem hr)).2 hk
      simp only [cell, hr, ite_true, rowFrame]
      rw [hlast]
      change ((frame _ _ (lastKind _)).sl).toNat = 1
      rw [terminal_sl]; rfl
  · right; left
    have he : r = R bs - 1 := by omega
    subst r
    simp only [cell, hr, ite_true, lastAt h, rowFrame]
    change ((frame _ _ (lastKind _)).sl).toNat = 1
    rw [terminal_sl]; rfl

end ZkFormal.NearV3.Render.SrcpGen
