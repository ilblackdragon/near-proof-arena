import ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionConstraintTransfer
import ZkFormal.NearV3.Rcpt.Candidates.DedupRowLocal

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air DedupRender

/-- Left physical rows preserve all logical steps up to the authenticated overlap;
the carried endpoint is gated without losing its preceding transition. -/
theorem left_rows {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    (H r : Nat) (hH : 2 ≤ H) (hR : R bs ≤ 2 * H - 2) (hr : r < H)
    (pub : Nat → Int) :
    ∀ ex ∈ leftConstraints,
      ev (cellsI bs rep r) (cellsI bs rep ((r + 1) % H))
        (if r = 0 then 1 else 0) (if r + 1 = H then 1 else 0)
        (if r + 1 = H then 0 else 1) pub ex = 0 := by
  by_cases hl : r + 1 = H
  · simp only [hl, ite_true]
    exact left_last _ _ _ 0 pub
  · have hm : (r + 1) % H = r + 1 := Nat.mod_eq_of_lt (by omega)
    simp only [hl, ite_false, hm]
    apply left_of_not_last _ _ _ 1 pub
    have hh := row_local h (2 * H) r (by omega) (by omega) pub
    have hg : r + 1 ≠ 2 * H := by omega
    have hmg : (r + 1) % (2 * H) = r + 1 := Nat.mod_eq_of_lt (by omega)
    simpa only [hg, ite_false, hmg] using hh

/-- Right physical rows begin on the overlap without global-first constraints.
Actual capacity slack places padding at the physical endpoint, so cyclic carry
rows cannot activate ungated segment-successor constraints there. -/
theorem right_rows {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    (H r : Nat) (hH : 2 ≤ H) (hR : R bs ≤ 2 * H - 2) (hr : r < H)
    (pub : Nat → Int) :
    ∀ ex ∈ rightConstraints,
      ev (cellsI bs rep (H - 1 + r)) (cellsI bs rep (H - 1 + ((r + 1) % H)))
        (if r = 0 then 1 else 0) (if r + 1 = H then 1 else 0)
        (if r + 1 = H then 0 else 1) pub ex = 0 := by
  by_cases hl : r + 1 = H
  · simp only [hl, ite_true, Nat.mod_self, Nat.add_zero]
    rw [padding_cellsI bs rep (H - 1 + r) (by omega)]
    apply right_of_zero_first _ _ _ 1 0 pub
    exact padding_physical_last (size bs) (cellsI bs rep (H - 1)) pub
  · have hm : (r + 1) % H = r + 1 := Nat.mod_eq_of_lt (by omega)
    simp only [hl, ite_false, hm]
    apply right_of_zero_first _ _ _ 0 1 pub
    have hh := row_local h (2 * H) (H - 1 + r) (by omega) (by omega) pub
    have hz : H - 1 + r ≠ 0 := by omega
    have hg : H - 1 + r + 1 ≠ 2 * H := by omega
    have hmg : (H - 1 + r + 1) % (2 * H) = H - 1 + r + 1 := Nat.mod_eq_of_lt (by omega)
    simp only [hz, hg, ite_false, hmg] at hh
    simpa only [Nat.add_assoc] using hh

end ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
