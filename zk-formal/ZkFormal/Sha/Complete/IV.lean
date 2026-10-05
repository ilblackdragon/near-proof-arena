import ZkFormal.Sha.Complete.Kind

/-! # Completeness: `cIV` -/

namespace ZkFormal.Sha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Gen ZkFormal.Sha.Layout

theorem complete_cIV : CompleteFamStmt Table.cIV := by
  intro msgs _ t pub r _ e he
  apply eval_honest_zero
  simp only [Table.cIV, List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨w, hw, b, hb, rfl⟩ := he
  simp only [zev_eqG, zev_c, zev_k, henv_cur]
  rw [cell_S]
  cases h : rowAt msgs r with
  | start id =>
    simp only [kS, rowCell_start, sc_St id w b hw hb]
    have : bit (ivW w) b = Table.iv w / 2 ^ b % 2 := rfl
    rw [this]; omega
  | _ => simp [kS]

end ZkFormal.Sha.Complete
