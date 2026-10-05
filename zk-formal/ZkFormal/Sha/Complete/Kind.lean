import ZkFormal.Sha.Complete.Cells

/-! # Completeness: `cKind` -/

namespace ZkFormal.Sha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Gen ZkFormal.Sha.Layout

/-- Kind flags of a row. -/
def kR : Row → Nat → Nat
  | .round j _, j' => if j' = j then 1 else 0
  | _, _ => 0
def kD : Row → Nat
  | .digest _ => 1
  | _ => 0
def kS : Row → Nat
  | .start _ => 1
  | _ => 0

theorem cell_R (row : Row) (j : Nat) (hj : j < 16) : rowCell row (colR j) = kR row j := by
  cases row with
  | start id =>
    exact sc_other id (colR j) (by unfold colR; omega) (by unfold colR colS; omega)
      (by unfold colR colId; omega)
  | round j' B => exact rc_R j' B j hj
  | digest B => exact dc_R B j hj
  | pad => rfl

theorem cell_D (row : Row) : rowCell row colD = kD row := by
  cases row with
  | start id => exact sc_other id _ (by decide) (by decide) (by decide)
  | round j' B => exact rc_D j' B
  | digest B => exact dc_D B
  | pad => rfl

theorem cell_S (row : Row) : rowCell row colS = kS row := by
  cases row with
  | start id => exact sc_S id
  | round j' B => exact rc_S j' B
  | digest B => exact dc_S B
  | pad => rfl

/-- `Σ_{j<n} kR row j`, as an integer. -/
theorem sum_kR (row : Row) (n : Nat) :
    ((List.range n).map fun j => ((kR row j : Nat) : Int)).sum =
      match row with
      | .round j _ => if j < n then 1 else 0
      | _ => 0 := by
  induction n with
  | zero => cases row <;> simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    cases row with
    | round j B =>
      simp only [kR, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      by_cases h2 : n = j
      · subst h2; simp
      · by_cases h1 : j < n
        · simp [h1, h2, show j < n + 1 by omega]
        · simp [h1, h2, show ¬ j < n + 1 by omega]
    | _ => simp [kR]

theorem zev_kindN (Z : ZEnv) (js : List Nat) :
    zev Z (Table.kindN js) = (js.map fun j => (Z.nxt (colR j) : Int)).sum := by
  simp only [Table.kindN, zev_sum, List.map_map]; rfl

theorem zev_kindC (Z : ZEnv) (js : List Nat) :
    zev Z (Table.kindC js) = (js.map fun j => (Z.cur (colR j) : Int)).sum := by
  simp only [Table.kindC, zev_sum, List.map_map]; rfl

theorem sum_cell_R (row : Row) :
    ((List.range 16).map fun j => ((rowCell row (colR j) : Nat) : Int)).sum =
      match row with
      | .round j _ => if j < 16 then 1 else 0
      | _ => 0 := by
  rw [← sum_kR row 16]
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [cell_R row j (List.mem_range.mp hj)]

theorem zev_flagSum (Z : ZEnv) :
    zev Z Table.flagSum =
      ((List.range 16).map fun j => (Z.cur (colR j) : Int)).sum + Z.cur colD + Z.cur colS := by
  simp only [Table.flagSum, zev_sum, List.map_map, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [Function.comp_def, zev_c]
  omega

/-- Last flag of a block of a message. -/
theorem blkOf_last (M : Msg) (b : Nat) : (blkOf M b).last = (b + 1 == nb M) := rfl

theorem kind_step (row nx : Row) (h : Step row nx) :
    (∀ j, j < 15 → kR nx (j + 1) = kR row j) ∧ kD nx = kR row 15 ∧
    kR nx 0 + kD row * rowCell row colLast = kS row + kD row := by
  cases h with
  | start M hM => simp [kR, kD, kS]
  | round M b j hM hb hj =>
    refine ⟨fun j' _ => ?_, ?_, ?_⟩
    · simp only [kR]; split <;> split <;> omega
    · simp only [kR, kD]; split <;> omega
    · simp [kR, kD, kS]
  | r15 M b hM hb =>
    refine ⟨fun j hj => ?_, ?_, ?_⟩ <;> simp [kR, kD, kS]; omega
  | dnext M b hM hb =>
    refine ⟨fun j' _ => ?_, rfl, ?_⟩
    · simp [kR]
    · simp only [kR, kD, kS, rowCell_digest, dc_Last, blkOf_last]
      have : (b + 1 == nb M) = false := by simp; omega
      simp [this]
  | dlast M b hM hb _ hX =>
    have hX' : kR nx 0 = 0 ∧ (∀ j, kR nx j = 0) ∧ kD nx = 0 := by
      rcases hX with rfl | ⟨id, rfl⟩ <;> simp [kR, kD]
    refine ⟨fun j' _ => by rw [hX'.2.1]; rfl, by rw [hX'.2.2]; rfl, ?_⟩
    simp only [hX'.1, kD, kS, rowCell_digest, dc_Last, blkOf_last]
    have : (b + 1 == nb M) = true := by simp; omega
    simp [this]
  | pad _ hX =>
    rcases hX with rfl | ⟨id, rfl⟩ <;> simp [kR, kD, kS]

theorem complete_cKind : CompleteFamStmt Table.cKind := by
  intro msgs hok t pub r hr e he
  apply eval_honest_zero
  have hs := kind_step _ _ (step_at msgs hok t r hr)
  simp only [Table.cKind, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.mem_nil_iff, or_false] at he
  rcases he with ((he | ⟨j, hj, rfl⟩) | he | he | he)
  · subst he
    simp only [zev_mul, zev_sub, zev_flagSum, zev_k, henv_cur]
    rw [sum_cell_R, cell_D, cell_S]
    cases rowAt msgs r with
    | round j B =>
      simp only [kD, kS]; split <;> decide
    | _ => simp [kD, kS]
  · simp only [zev_sub, zev_n, zev_c, henv_cur, henv_nxt]
    rw [cell_R _ _ (by omega), cell_R _ _ (by omega), hs.1 j hj]; omega
  · subst he
    simp only [zev_sub, zev_n, zev_c, henv_cur, henv_nxt]
    rw [cell_R _ _ (by omega), cell_D, hs.2.1]; omega
  · subst he
    simp only [zev_sub, zev_n, zev_c, zev_add, zev_mul, henv_cur, henv_nxt]
    rw [cell_R _ _ (by omega), cell_D, cell_S]
    have := hs.2.2
    generalize rowCell (rowAt msgs r) colLast = L at this ⊢
    generalize kD (rowAt msgs r) = d at this ⊢
    generalize kR (rowAt msgs ((r + 1) % (honestTrace msgs).height t)) 0 = a at this ⊢
    have h2 : ((d * L : Nat) : Int) = (d : Int) * (L : Int) := rfl
    omega
  · subst he
    simp only [zev_mul, zev_add, zev_isFirst, zev_kindC, zev_c, henv_cur]
    simp only [henv]
    split
    · next h0 =>
      subst h0
      have hsum := sum_cell_R (rowAt msgs 0)
      rw [hsum, cell_D]
      rcases row0 msgs with h | ⟨id, h⟩ <;> rw [h] <;> simp [kD]
    · simp

end ZkFormal.Sha.Complete
