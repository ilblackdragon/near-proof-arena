import ZkFormal.NearV3.Rcpt.Candidates.DedupFirstLocal
import ZkFormal.NearV3.Rcpt.Candidates.DedupActiveLocal
import ZkFormal.NearV3.Rcpt.Candidates.DedupLastLocal
import ZkFormal.NearV3.Rcpt.Candidates.DedupPaddingLocal

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air Render.SrcpGen

/-- Every row of the complete logical renderer satisfies every candidate polynomial,
including both physical endpoints and arbitrary padding height. -/
theorem row_local {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    (H r : Nat) (hH : R bs ≤ H) (hr : r < H) (pub : Nat → Int) :
    ∀ ex ∈ DedupTable.constraints,
      ev (cellsI bs rep r) (cellsI bs rep ((r + 1) % H))
        (if r = 0 then 1 else 0) (if r + 1 = H then 1 else 0)
        (if r + 1 = H then 0 else 1) pub ex = 0 := by
  have hR := R_ge_33 h
  by_cases h0 : r = 0
  · subst r
    have hm : 1 % H = 1 := Nat.mod_eq_of_lt (by omega)
    simpa [hm, show 1 ≠ H by omega] using first_local h pub
  · by_cases hl : r + 1 = H
    · have hm : (r + 1) % H = 0 := by rw [hl, Nat.mod_self]
      simp only [h0, hl, ite_false, ite_true, hm, Nat.mod_self]
      by_cases ha : r < R bs
      · have he : r = R bs - 1 := by omega
        rw [he]
        exact last_physical h (cellsI bs rep 0) pub (first_sg h)
      · rw [padding_cellsI bs rep r (by omega)]
        exact padding_physical_last (size bs) (cellsI bs rep 0) pub
    · have hm : (r + 1) % H = r + 1 := Nat.mod_eq_of_lt (by omega)
      simp only [h0, hl, ite_false, hm]
      by_cases ha : r < R bs
      · by_cases hn : r + 1 < R bs
        · exact active_step h r hn pub
        · have he : r = R bs - 1 := by omega
          rw [padding_cellsI bs rep (r + 1) (by omega), he]
          exact last_to_padding h pub
      · rw [padding_cellsI bs rep r (by omega), padding_cellsI bs rep (r + 1) (by omega)]
        exact padding_to_padding (size bs) 0 1 pub

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
