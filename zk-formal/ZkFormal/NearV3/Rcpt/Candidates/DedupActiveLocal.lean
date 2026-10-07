import ZkFormal.NearV3.Rcpt.Candidates.DedupCellFacts
import ZkFormal.NearV3.Rcpt.Candidates.DedupInternalLocal
import ZkFormal.NearV3.Rcpt.Candidates.DedupEndLocal

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air Render.SrcpGen

/-- Every consecutive active renderer pair satisfies the candidate polynomials.
The first physical selector is handled separately by `first_local`. -/
theorem active_step {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    (r : Nat) (hr : r + 1 < R bs) (pub : Nat → Int) :
    ∀ ex ∈ DedupTable.constraints,
      ev (cellsI bs rep r) (cellsI bs rep (r + 1)) 0 0 1 pub ex = 0 := by
  have hc : r < R bs := by omega
  have hm := mem_recs (descriptor_mem hc)
  have hm' := mem_recs (descriptor_mem hr)
  have ht : decide (r + 1 = R bs) = false := by simp; omega
  rw [active_cellsI bs rep r hc, active_cellsI bs rep (r + 1) hr]
  simp only [ht]
  rcases adjAt hr with ⟨hn, hi⟩ | ⟨hn, hi⟩
  · rw [hi]
    exact internal_local _ (h.block_at _ hm.1) _ _ _ hm.2 hn _ _ _
      (h.rep_length _ hm.1) pub
  · have hk := none_last _ _ hm.2 hn
    have hj : ((recs bs).getD r default).1 + 1 < bs.length := by
      simpa only [hi] using hm'.1
    rw [hi, hk]
    simp only
    rw [size_take_next bs _ hm.1]
    apply end_to_root _ _ (h.block_at _ hm.1) _ _ _ _
      (h.dup_rep _ hm.1) (h.rep_length _ hm.1) _ (h.next_q _ hj) pub
    rw [h.index _ hm.1, h.index _ hj]

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
