import ZkFormal.NearV3.Rcpt.Candidates.DedupCellFacts
import ZkFormal.NearV3.Rcpt.Candidates.DedupEndTerminal

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air Render.SrcpGen

/-- The actual final active row enters padding with the full table SIZE. -/
theorem last_to_padding {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    (pub : Nat → Int) :
    ∀ ex ∈ DedupTable.constraints,
      ev (cellsI bs rep (R bs - 1))
        (fun x => if x = SrcpV3.sz then (size bs : Int) else 0) 0 0 1 pub ex = 0 := by
  have hr := R_ge_33 h
  have hp : 0 < bs.length := by have hn := h.nonempty; cases bs <;> simp_all
  have hi : bs.length - 1 < bs.length := by omega
  have ht : decide (R bs - 1 + 1 = R bs) = true := by simp; omega
  rw [active_cellsI bs rep (R bs - 1) (by omega), lastAt h.nonempty]
  simp only [ht]
  have hh := end_to_padding _ (h.block_at _ hi) (size (bs.take (bs.length - 1)))
    (rep (bs.length - 1)) (h.dup_rep _ hi) (h.rep_length _ hi) pub
  simpa only [final_charge h] using hh

/-- The actual final active row may be physical-last when the cyclic successor
has no segment flag, as with the logical trace's initial source root. -/
theorem last_physical {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    (next pub : Nat → Int) (hsg : next SrcpV3.sg = 0) :
    ∀ ex ∈ DedupTable.constraints,
      ev (cellsI bs rep (R bs - 1)) next 0 1 0 pub ex = 0 := by
  have hr := R_ge_33 h
  have hp : 0 < bs.length := by have hn := h.nonempty; cases bs <;> simp_all
  have hi : bs.length - 1 < bs.length := by omega
  have ht : decide (R bs - 1 + 1 = R bs) = true := by simp; omega
  rw [active_cellsI bs rep (R bs - 1) (by omega), lastAt h.nonempty]
  simp only [ht]
  exact end_physical_last _ (h.block_at _ hi) (size (bs.take (bs.length - 1)))
    (rep (bs.length - 1)) (h.dup_rep _ hi) (h.rep_length _ hi) next pub hsg

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
