import ZkFormal.Sha.Complete.FrameCells

/-!
# ZkFormal.Sha.Complete.Frame1 — framing constraints: data flags, counters,
block flags, digest multiplicity
-/

namespace ZkFormal.Sha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Gen ZkFormal.Sha.Layout ZkFormal.Sha.Table

/-- Split every `if` and close the arithmetic. -/
macro "ites" : tactic => `(tactic| (repeat' split) <;> omega)

section
variable (f lst : Int) (p : Nat → Int)

@[simp] theorem cell_F_start (id q : Nat) (hq : q < 16) : startCell id (colF q) = 0 :=
  s_zero id _ (by unfold colF; omega) (by unfold colF colS; omega) (by unfold colF colId; omega)

@[simp] theorem sc_Fprev (id : Nat) : startCell id colFprev = 0 := s_zero id _ (by decide) (by decide) (by decide)
@[simp] theorem sc_Nd (id : Nat) : startCell id colNd = 0 := s_zero id _ (by decide) (by decide) (by decide)
@[simp] theorem sc_Last (id : Nat) : startCell id colLast = 0 := s_zero id _ (by decide) (by decide) (by decide)
@[simp] theorem sc_P80 (id : Nat) : startCell id colP80 = 0 := s_zero id _ (by decide) (by decide) (by decide)
@[simp] theorem sc_Seen (id : Nat) : startCell id colSeen = 0 := s_zero id _ (by decide) (by decide) (by decide)
@[simp] theorem sc_Pn (id : Nat) : startCell id colPn = 0 := s_zero id _ (by decide) (by decide) (by decide)
@[simp] theorem sc_Dmult (id : Nat) : startCell id colDmult = 0 := s_zero id _ (by decide) (by decide) (by decide)
@[simp] theorem sc_D (id : Nat) : startCell id colD = 0 := s_zero id _ (by decide) (by decide) (by decide)

/-! ## Current-row constraints -/

/-- A constraint reading only framing cells of the current row vanishes if it
does on every round and digest row (start and padding rows are all-zero there). -/
theorem cur_only (cur nx : Row) (hc : CurRow cur) (e : Expr)
    (hS : ∀ M, MOk M → zev (renv (.start M.id) nx f lst p) e = 0)
    (hR : ∀ M b j, MOk M → b < nb M → j < 16 → zev (renv (.round j (blkOf M b)) nx f lst p) e = 0)
    (hD : ∀ M b, MOk M → b < nb M → zev (renv (.digest (blkOf M b)) nx f lst p) e = 0)
    (hP : zev (renv .pad nx f lst p) e = 0) : zev (renv cur nx f lst p) e = 0 := by
  cases hc with
  | start M hM => exact hS M hM
  | round M b j hM hb hj => exact hR M b j hM hb hj
  | digest M b hM hb => exact hD M b hM hb
  | pad => exact hP

theorem fr_mono (cur nx : Row) (hc : CurRow cur) (q : Nat) (hq : q < 15) :
    zev (renv cur nx f lst p) (.mul (E.c (colF (q + 1))) (E.not (E.c (colF q)))) = 0 := by
  apply cur_only f lst p cur nx hc
  · intro M _; simp [cell_F_start _ _ (by omega : q + 1 < 16)]
  · intro M b j _ _ _
    simp only [zev_mul, zev_not, zev_c, renv_cur, rowCell_round, r_F M b j _ (by omega : q + 1 < 16),
      r_F M b j q (by omega)]
    ites
  · intro M b _ _; simp [dc_F _ _ (by omega : q + 1 < 16)]
  · simp

theorem fr_F0prev (cur nx : Row) (hc : CurRow cur) :
    zev (renv cur nx f lst p) (.mul (E.c (colF 0)) (E.not (E.c colFprev))) = 0 := by
  apply cur_only f lst p cur nx hc
  · intro M _; simp [cell_F_start _ 0 (by decide)]
  · intro M b j _ _ _
    simp only [zev_mul, zev_not, zev_c, renv_cur, rowCell_round, r_F M b j 0 (by decide), r_Fprev]
    ites
  · intro M b _ _; simp [dc_F _ 0 (by decide)]
  · simp

theorem fr_msgC (cur nx : Row) (hc : CurRow cur) :
    zev (renv cur nx f lst p) (.mul (E.not gMsgC) (E.c (colF 0))) = 0 := by
  apply cur_only f lst p cur nx hc
  · intro M _; simp [cell_F_start _ 0 (by decide)]
  · intro M b j _ _ _
    simp only [zev_mul, zev_not, zev_gMsgC, zev_c, renv_cur, rowCell_round, r_F M b j 0 (by decide),
      gateV, List.mem_range]
    ites
  · intro M b _ _; simp [dc_F _ 0 (by decide)]
  · simp

theorem fr_R0prev (cur nx : Row) (hc : CurRow cur) :
    zev (renv cur nx f lst p) (.mul (E.c (colR 0)) (E.not (E.c colFprev))) = 0 := by
  apply cur_only f lst p cur nx hc
  · intro M _; simp [zev_cR _ _ _ _ _ 0 (by decide), kR]
  · intro M b j _ _ _
    simp only [zev_mul, zev_not, zev_cR _ _ _ _ _ 0 (by decide), kR, zev_c, renv_cur, rowCell_round, r_Fprev]
    ites
  · intro M b _ _; simp [zev_cR _ _ _ _ _ 0 (by decide), kR]
  · simp [zev_cR _ _ _ _ _ 0 (by decide), kR]

theorem fr_Pn (cur nx : Row) (hc : CurRow cur) :
    zev (renv cur nx f lst p) (E.sub (E.c colPn) (.mul (E.c colP80) (E.not (E.c colLast)))) = 0 := by
  apply cur_only f lst p cur nx hc
  · intro M _; simp
  · intro M b j _ _ _
    simp only [zev_sub, zev_mul, zev_not, zev_c, renv_cur, rowCell_round, r_Pn, r_P80, r_Last]
    ites
  · intro M b _ _
    simp only [zev_sub, zev_mul, zev_not, zev_c, renv_cur, rowCell_digest, d_Pn, d_P80, d_Last]
    ites
  · simp

theorem fr_SeenP80 (cur nx : Row) (hc : CurRow cur) :
    zev (renv cur nx f lst p) (.mul (E.c colSeen) (E.c colP80)) = 0 := by
  apply cur_only f lst p cur nx hc
  · intro M _; simp
  · intro M b j _ _ _
    simp only [zev_mul, zev_c, renv_cur, rowCell_round, r_Seen, r_P80]
    ites
  · intro M b _ _
    simp only [zev_mul, zev_c, renv_cur, rowCell_digest, d_Seen, d_P80]
    ites
  · simp

theorem fr_Dmult1 (cur nx : Row) (hc : CurRow cur) :
    zev (renv cur nx f lst p) (.mul (E.c colDmult) (E.not (E.c colD))) = 0 := by
  apply cur_only f lst p cur nx hc
  · intro M _; simp
  · intro M b j _ _ _; simp [rc_Dmult]
  · intro M b _ _
    simp only [zev_mul, zev_not, zev_c, renv_cur, rowCell_digest, d_Dmult, dc_D]
    ites
  · simp

theorem fr_Dmult2 (cur nx : Row) (hc : CurRow cur) :
    zev (renv cur nx f lst p) (.mul (E.c colDmult) (E.not (E.c colLast))) = 0 := by
  apply cur_only f lst p cur nx hc
  · intro M _; simp
  · intro M b j _ _ _; simp [rc_Dmult]
  · intro M b _ _
    simp only [zev_mul, zev_not, zev_c, renv_cur, rowCell_digest, d_Dmult, d_Last]
    ites
  · simp

/-! ## Block-level padding structure (round rows only) -/

/-- A constraint gated by `R j` on the current row only needs round rows `Rj`. -/
theorem cur_round (cur nx : Row) (hc : CurRow cur) (j : Nat) (hj : j < 16) (x : Expr)
    (h : ∀ M b, MOk M → b < nb M → zev (renv (.round j (blkOf M b)) nx f lst p) x = 0) :
    zev (renv cur nx f lst p) (.mul (E.c (colR j)) x) = 0 := by
  rw [zev_mul, zev_cR _ _ _ _ _ j hj]
  cases hc with
  | round M b j' hM hb _ =>
    simp only [kR]
    split
    · next h' => subst h'; rw [h M b hM hb]; simp
    · simp
  | _ => simp [kR]

theorem cur_round' (cur nx : Row) (hc : CurRow cur) (j : Nat) (hj : j < 16) (x y : Expr)
    (h : ∀ M b, MOk M → b < nb M → zev (renv (.round j (blkOf M b)) nx f lst p) (.mul x y) = 0) :
    zev (renv cur nx f lst p) (.mul (.mul (E.c (colR j)) x) y) = 0 := by
  have := cur_round f lst p cur nx hc j hj (.mul x y) h
  simp only [zev_mul] at this ⊢
  rw [Int.mul_assoc]; exact this

theorem cur_round'' (cur nx : Row) (hc : CurRow cur) (j : Nat) (hj : j < 16) (x y z : Expr)
    (h : ∀ M b, MOk M → b < nb M → zev (renv (.round j (blkOf M b)) nx f lst p) (.mul (.mul x y) z) = 0) :
    zev (renv cur nx f lst p) (.mul (.mul (.mul (E.c (colR j)) x) y) z) = 0 := by
  have := cur_round f lst p cur nx hc j hj (.mul (.mul x y) z) h
  simp only [zev_mul] at this ⊢
  rw [Int.mul_assoc, Int.mul_assoc, ← Int.mul_assoc (zev _ x)]; exact this

/-- Arithmetic facts of a block, for `omega`. -/
theorem blk_arith (M : Msg) (b : Nat) (hb : b < nb M) :
    64 * nb M = M.bytes.length + 9 + (119 - M.bytes.length % 64) % 64 ∧ b < nb M :=
  ⟨nb_eq M, hb⟩

theorem fr_blk1 (cur nx : Row) (hc : CurRow cur) :
    zev (renv cur nx f lst p) (.mul (.mul (E.c (colR 3)) (E.c colP80)) (E.c (colF 15))) = 0 := by
  apply cur_round' f lst p cur nx hc 3 (by decide)
  intro M b _ hb
  have := blk_arith M b hb
  simp only [zev_mul, zev_c, renv_cur, rowCell_round, r_P80, r_F M b 3 15 (by decide)]
  ites

theorem fr_blk2 (cur nx : Row) (hc : CurRow cur) :
    zev (renv cur nx f lst p)
      (.mul (.mul (E.c (colR 3)) (E.sub (E.not (E.c colSeen)) (E.c colP80))) (E.not (E.c (colF 15)))) = 0 := by
  apply cur_round' f lst p cur nx hc 3 (by decide)
  intro M b _ hb
  have := blk_arith M b hb
  simp only [zev_mul, zev_sub, zev_not, zev_c, renv_cur, rowCell_round, r_P80, r_Seen,
    r_F M b 3 15 (by decide)]
  ites

theorem fr_blk3 (cur nx : Row) (hc : CurRow cur) :
    zev (renv cur nx f lst p) (.mul (.mul (E.c (colR 0)) (E.c colSeen)) (E.c (colF 0))) = 0 := by
  apply cur_round' f lst p cur nx hc 0 (by decide)
  intro M b _ hb
  simp only [zev_mul, zev_c, renv_cur, rowCell_round, r_Seen, r_F M b 0 0 (by decide)]
  ites

theorem fr_blk4 (cur nx : Row) (hc : CurRow cur) :
    zev (renv cur nx f lst p)
      (.mul (.mul (E.c (colR 0)) (E.c colLast)) (E.sub (E.not (E.c colSeen)) (E.c colP80))) = 0 := by
  apply cur_round' f lst p cur nx hc 0 (by decide)
  intro M b _ hb
  have := blk_arith M b hb
  simp only [zev_mul, zev_sub, zev_not, zev_c, renv_cur, rowCell_round, r_Seen, r_P80, r_Last]
  ites

theorem fr_blk5 (cur nx : Row) (hc : CurRow cur) :
    zev (renv cur nx f lst p) (.mul (.mul (E.c (colR 0)) (E.c colSeen)) (E.not (E.c colLast))) = 0 := by
  apply cur_round' f lst p cur nx hc 0 (by decide)
  intro M b _ hb
  have := blk_arith M b hb
  simp only [zev_mul, zev_not, zev_c, renv_cur, rowCell_round, r_Seen, r_Last]
  ites

theorem fr_blk6 (cur nx : Row) (hc : CurRow cur) :
    zev (renv cur nx f lst p) (.mul (.mul (E.c (colR 3)) (E.c colLast)) (E.c (colF 8))) = 0 := by
  apply cur_round' f lst p cur nx hc 3 (by decide)
  intro M b _ hb
  have := blk_arith M b hb
  simp only [zev_mul, zev_c, renv_cur, rowCell_round, r_Last, r_F M b 3 8 (by decide)]
  ites

theorem fr_blk7 (cur nx : Row) (hc : CurRow cur) :
    zev (renv cur nx f lst p)
      (.mul (.mul (.mul (E.c (colR 3)) (E.c colLast)) (E.c colP80)) (dropE 8)) = 0 := by
  apply cur_round'' f lst p cur nx hc 3 (by decide)
  intro M b _ hb
  have := blk_arith M b hb
  simp only [dropE, zev_mul, zev_sub, zev_c, renv_cur, rowCell_round, r_Last, r_P80,
    r_F M b 3 8 (by decide)]
  simp only [Nat.reduceEqDiff, if_false]
  simp only [zev_c, renv_cur, rowCell_round, r_F M b 3 7 (by decide)]
  ites

theorem fr_blk8 (cur nx : Row) (hc : CurRow cur) :
    zev (renv cur nx f lst p) (.mul (.mul (E.c (colR 3)) (E.c colPn)) (E.not (E.c (colF 7)))) = 0 := by
  apply cur_round' f lst p cur nx hc 3 (by decide)
  intro M b _ hb
  have := blk_arith M b hb
  simp only [zev_mul, zev_not, zev_c, renv_cur, rowCell_round, r_Pn, r_F M b 3 7 (by decide)]
  ites

end

end ZkFormal.Sha.Complete
