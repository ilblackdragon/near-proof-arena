import ZkFormal.NearV3.Rcpt.Render.Srcp.SizeFacts

namespace ZkFormal.NearV3.Render.SrcpGen

/-- Natural SIZE prefixes satisfy the table recurrence throughout active rows and padding. -/
theorem size_step {bs : List SrcpB} (h : SrcpWf bs) (r : Nat) :
    cell bs (r + 1) SrcpV3.sz = cell bs r SrcpV3.sz + rowCharge bs (r + 1) := by
  by_cases hr : r < R bs
  · by_cases hn : r + 1 < R bs
    · rw [active_charge bs (r + 1) hn]
      rcases adjAt hn with ⟨hk, hi⟩ | ⟨hk, hd⟩
      · simp only [cell, hr, hn, ite_true, rowFrame]
        rw [hi]
        change (frame _ _ _).sz = (frame _ _ _).sz + chargeKind _ _
        exact internal_size _ _ _ _ hk
      · have hlast := none_last _ _ (mem_recs (descriptor_mem hr)).2 hk
        have hi := (mem_recs (descriptor_mem hn)).1
        rw [hd] at hi
        simp only at hi
        simp only [cell, hr, hn, ite_true, rowFrame]
        rw [hlast, hd]
        change (rootFrame _ _).sz = (frame _ _ (lastKind _)).sz + (bs.getD _ default).L
        exact cross_size _ hi
    · have hp : R bs ≤ r + 1 := by omega
      have he : r = R bs - 1 := by omega
      rw [padding_charge bs (r + 1) hp, padding_cell hp]
      simp only [ite_true, Nat.add_zero]
      rw [he, last_size_cell h]
  · have hp : R bs ≤ r := by omega
    have hn : R bs ≤ r + 1 := by omega
    rw [padding_charge bs (r + 1) hn, padding_cell hp, padding_cell hn]
    simp

end ZkFormal.NearV3.Render.SrcpGen
