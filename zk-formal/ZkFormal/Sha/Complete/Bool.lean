import ZkFormal.Sha.Complete.Cells

/-! # Completeness: `cBool` -/

namespace ZkFormal.Sha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Gen ZkFormal.Sha.Layout

theorem complete_cBool : CompleteFamStmt Table.cBool := by
  intro msgs _ t pub r _ e he
  apply eval_honest_zero
  simp only [Table.cBool, List.mem_map] at he
  obtain ⟨x, hx, rfl⟩ := he
  have hb := rowCell_bool (rowAt msgs r) x (mem_boolCols x hx)
  simp only [Table.boolC, zev_mul, zev_sub, zev_c, zev_k, henv_cur]
  generalize rowCell (rowAt msgs r) x = v at hb
  rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl <;> decide

end ZkFormal.Sha.Complete
