import ZkFormal.NearV3.Rcpt.Render.Srcp.RegisterFacts

namespace ZkFormal.NearV3.Render.SrcpGen

/-- Each active row either disables shifting or carries the complete register window. -/
theorem register_carry_cases {bs : List SrcpB} (h : SrcpWf bs) (H r : Nat)
    (hH : R bs ≤ H) (hr : r < R bs) :
    cell bs r SrcpV3.sg = 0 ∨ cell bs r SrcpV3.wl = 1 ∨
      (∀ x, x < 31 → cell bs ((r + 1) % H) (SrcpV3.reg x) =
        cell bs r (SrcpV3.reg (x + 1))) := by
  by_cases hn : r + 1 < R bs
  · have hm : (r + 1) % H = r + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hm]
    rcases adjAt hn with ⟨hk, hi⟩ | ⟨hk, _⟩
    · have hs := internal_registers _ (before bs ((recs bs).getD r default).1)
        _ _ (mem_recs (descriptor_mem hr)).2 hk
      rcases hs with hSg | hWl | hReg
      · left
        simp only [cell, hr, ite_true, rowFrame]
        change ((frame _ _ _).sg).toNat = 0
        rw [hSg]; rfl
      · right; left
        simp only [cell, hr, ite_true, rowFrame]
        change ((frame _ _ _).wl).toNat = 1
        rw [hWl]; rfl
      · right; right
        intro x hx
        simp only [cell, hr, hn, ite_true, rowFrame]
        rw [Frame.reg_cell _ x (by omega), Frame.reg_cell _ (x + 1) (by omega)]
        simp only
        rw [hi]
        exact hReg x
    · right; left
      have hlast := none_last _ _ (mem_recs (descriptor_mem hr)).2 hk
      simp only [cell, hr, ite_true, rowFrame]
      rw [hlast]
      change ((frame _ _ (lastKind _)).wl).toNat = 1
      rw [terminal_wl]; rfl
  · right; left
    have he : r = R bs - 1 := by omega
    subst r
    simp only [cell, hr, ite_true, lastAt h, rowFrame]
    change ((frame _ _ (lastKind _)).wl).toNat = 1
    rw [terminal_wl]; rfl

end ZkFormal.NearV3.Render.SrcpGen
