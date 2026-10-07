import ZkFormal.NearV3.Rcpt.Render.Srcp.TransitionFacts

namespace ZkFormal.NearV3.Render.SrcpGen

/-- An active row either carries its list constants forward or ends its list. -/
theorem list_carry_cases {bs : List SrcpB} (h : SrcpWf bs) (H r : Nat)
    (hH : R bs ≤ H) (hr : r < R bs) :
    (∀ x ∈ SrcpV3.listConst,
      cell bs ((r + 1) % H) x = cell bs r x) ∨
    (cell bs r SrcpV3.rt = 0 ∧ cell bs r SrcpV3.sl = 1 ∧
      cell bs ((r + 1) % H) SrcpV3.sg = 0) := by
  by_cases hn : r + 1 < R bs
  · have hm : (r + 1) % H = r + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hm]
    rcases adjAt hn with ⟨_, hi⟩ | ⟨hk, hd⟩
    · left
      intro x hx
      simp only [cell, hr, hn, ite_true, rowFrame]
      rw [list_constant _ _ _ _ x hx, list_constant _ _ _ _ x hx]
      rw [hi]
    · right
      have hlast := none_last _ _ (mem_recs (descriptor_mem hr)).2 hk
      simp only [cell, hr, hn, ite_true, rowFrame]
      rw [hlast, hd]
      refine ⟨?_, ?_, ?_⟩
      · change ((frame _ _ (lastKind _)).rt).toNat = 0
        rw [terminal_rt]; rfl
      · change ((frame _ _ (lastKind _)).sl).toNat = 1
        rw [terminal_sl]; rfl
      · rfl
  · right
    have he : r = R bs - 1 := by omega
    have hc := last_cells h
    refine ⟨by simpa [he] using hc.1, by simpa [he] using hc.2.2.1, ?_⟩
    by_cases hh : r + 1 = H
    · rw [hh, Nat.mod_self]
      exact first_sg h
    · have hm : (r + 1) % H = r + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hm]
      simp [padding_cell (show R bs ≤ r + 1 by omega), SrcpV3.sg, SrcpV3.sz]

end ZkFormal.NearV3.Render.SrcpGen
