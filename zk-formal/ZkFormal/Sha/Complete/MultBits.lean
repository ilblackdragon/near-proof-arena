import ZkFormal.Sha.Complete.Cells

/-! # Completeness: multiplicity bits are boolean -/

namespace ZkFormal.Sha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Gen ZkFormal.Sha.Layout ZkFormal.Sha.Table

theorem cell_Dmult_le (row : Row) : rowCell row colDmult ≤ 1 := by
  cases row with
  | start id => rw [rowCell_start, sc_other id _ (by decide) (by decide) (by decide)]; decide
  | round j B => rw [rowCell_round, rc_Dmult]; decide
  | digest B => rw [rowCell_digest, dc_Dmult]; split <;> decide
  | pad => decide

theorem multBitsStmt : MultBitsStmt := by
  intro msgs _ t pub r _ busBytes busDigest i hi b hb
  rw [eval_honest]
  have key : ∃ x, b = E.c x ∧ rowCell (rowAt msgs r) x ≤ 1 := by
    simp only [interactions, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.mem_nil_iff, or_false] at hi
    rcases hi with ⟨q, hq, rfl⟩ | rfl
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      exact ⟨colF q, hb, rowCell_bool _ _ (by unfold colF; omega)⟩
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      exact ⟨colDmult, hb, cell_Dmult_le _⟩
  obtain ⟨x, rfl, hx⟩ := key
  simp only [zev_c, henv_cur]
  generalize rowCell (rowAt msgs r) x = v at hx
  rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
  · left; rfl
  · right; rfl

end ZkFormal.Sha.Complete
