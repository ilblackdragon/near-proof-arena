import ZkFormal.NearV3.Rcpt.Candidates.DedupCellFacts
import ZkFormal.NearV3.Rcpt.Candidates.DedupRootLocal

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air Render.SrcpGen

/-- The actual first two renderer rows establish every initial constraint. -/
theorem first_local {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    (pub : Nat → Int) :
    ∀ ex ∈ DedupTable.constraints,
      ev (cellsI bs rep 0) (cellsI bs rep 1) 1 0 1 pub ex = 0 := by
  have hr := R_ge_33 h
  have hp : 0 < bs.length := by have hn := h.nonempty; cases bs <;> simp_all
  rw [active_cellsI bs rep 0 (by omega), active_cellsI bs rep 1 (by omega), firstAt h, secondAt h]
  have h1 : (decide (0 + 1 = R bs)) = false := by simp; omega
  have h2 : (decide (1 + 1 = R bs)) = false := by simp; omega
  simp only [h1, h2, List.take_zero, size, List.map_nil, List.sum_nil, leaf_metadata]
  exact first_root_to_leaf _ (rep 0) h.first_dup h.first_q (h.index 0 hp)
    (h.rep_length 0 hp) pub

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
