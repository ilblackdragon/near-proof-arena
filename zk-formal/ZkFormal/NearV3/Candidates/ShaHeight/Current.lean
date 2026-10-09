import ZkFormal.Sha.Complete.All
namespace ZkFormal.NearV3.Candidates.ShaHeight
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha ZkFormal.Sha.Complete ZkFormal.Sha.Gen ZkFormal.Sha.Layout

theorem family_bool (cur nx : Row) (f lst : Int) (p : Nat→Int)
    (e : Expr) (he : e∈Table.cBool) : zev (renv cur nx f lst p) e=0 := by
  simp only [Table.cBool, List.mem_map] at he
  obtain ⟨x, hx, rfl⟩ := he
  have hb := rowCell_bool (cur) x (mem_boolCols x hx)
  simp only [Table.boolC, zev_mul, zev_sub, zev_c, zev_k, renv_cur]
  generalize rowCell (cur) x = v at hb
  rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl <;> decide

theorem family_iv (cur nx : Row) (f lst : Int) (p : Nat→Int)
    (e : Expr) (he : e∈Table.cIV) : zev (renv cur nx f lst p) e=0 := by
  simp only [Table.cIV, List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨w, hw, b, hb, rfl⟩ := he
  simp only [zev_eqG, zev_c, zev_k, renv_cur]
  rw [cell_S]
  cases h : cur with
  | start id =>
    simp only [kS, rowCell_start, sc_St id w b hw hb]
    have : bit (ivW w) b = Table.iv w / 2 ^ b % 2 := rfl
    rw [this]; omega
  | _ => simp [kS]

theorem family_kind (cur nx : Row) (hstep : Step cur nx) (f lst : Int) (p : Nat→Int)
    (hfirst : f=0 ∨ cur=.pad ∨ ∃id,cur=.start id)
    (e : Expr) (he : e∈Table.cKind) : zev (renv cur nx f lst p) e=0 := by
  have hs := kind_step _ _ hstep
  simp only [Table.cKind, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.mem_nil_iff, or_false] at he
  rcases he with ((he | ⟨j, hj, rfl⟩) | he | he | he)
  · subst he
    simp only [zev_mul, zev_sub, zev_flagSum, zev_k, renv_cur]
    rw [sum_cell_R, cell_D, cell_S]
    cases cur with
    | round j B =>
      simp only [kD, kS]; split <;> decide
    | _ => simp [kD, kS]
  · simp only [zev_sub, zev_n, zev_c, renv_cur, renv_nxt]
    rw [cell_R _ _ (by omega), cell_R _ _ (by omega), hs.1 j hj]; omega
  · subst he
    simp only [zev_sub, zev_n, zev_c, renv_cur, renv_nxt]
    rw [cell_R _ _ (by omega), cell_D, hs.2.1]; omega
  · subst he
    simp only [zev_sub, zev_n, zev_c, zev_add, zev_mul, renv_cur, renv_nxt]
    rw [cell_R _ _ (by omega), cell_D, cell_S]
    have := hs.2.2
    generalize rowCell (cur) colLast = L at this ⊢
    generalize kD (cur) = d at this ⊢
    generalize kR (nx) 0 = a at this ⊢
    have h2 : ((d * L : Nat) : Int) = (d : Int) * (L : Int) := rfl
    omega
  · subst he
    simp only [zev_mul, zev_add, zev_isFirst, zev_kindC, zev_c, renv_cur]
    change f * _=0
    rcases hfirst with hf | hc
    · rw [hf]; simp
    · rw [sum_cell_R,cell_D]
      rcases hc with rfl | ⟨id,rfl⟩ <;> simp [kD]

end ZkFormal.NearV3.Candidates.ShaHeight
