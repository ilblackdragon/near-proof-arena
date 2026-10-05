import ZkFormal.Sha.Complete.Frame1

/-!
# ZkFormal.Sha.Complete.Frame2 — framing constraints across rows
(`Fprev` chaining, counters, block/message constants)
-/

namespace ZkFormal.Sha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Gen ZkFormal.Sha.Layout ZkFormal.Sha.Table

section
variable (f lst : Int) (p : Nat → Int)

theorem zev_nD (cur nx : Row) : zev (renv cur nx f lst p) (E.n colD) = ((kD nx : Nat) : Int) := by
  simp [cell_D]

theorem zev_cD (cur nx : Row) : zev (renv cur nx f lst p) (E.c colD) = ((kD cur : Nat) : Int) := by
  simp [cell_D]

theorem zev_cS (cur nx : Row) : zev (renv cur nx f lst p) (E.c colS) = ((kS cur : Nat) : Int) := by
  simp [cell_S]

theorem zev_gBlockN (cur nx : Row) :
    zev (renv cur nx f lst p) gBlockN = gateV nx (List.range 16) + ((kD nx : Nat) : Int) := by
  simp only [gBlockN, zev_add, zev_gRound, zev_nD]

theorem zev_gInnerN (cur nx : Row) :
    zev (renv cur nx f lst p) gInnerN = gateV nx (List.range' 1 15) + ((kD nx : Nat) : Int) := by
  simp only [gInnerN, zev_add, zev_gHelp, zev_nD]

theorem fsum_round (cur : Row) (M : Msg) (b j : Nat) :
    zev (renv cur (.round j (blkOf M b)) f lst p) fSumN =
      if j < 4 then ((min 16 (M.bytes.length - (64 * b + 16 * j)) : Nat) : Int) else 0 := by
  unfold fSumN
  rw [zev_sum, List.map_map]
  have e : ((List.range 16).map ((zev (renv cur (.round j (blkOf M b)) f lst p)) ∘ fun q => E.n (colF q))) =
      (List.range 16).map fun q =>
        (((if j < 4 ∧ 64 * b + (16 * j + q) < M.bytes.length then 1 else 0 : Nat)) : Int) := by
    apply List.map_congr_left
    intro q hq
    rw [List.mem_range] at hq
    simp only [Function.comp, zev_n, renv_nxt, rowCell_round, r_F M b j q hq]
  rw [e]
  split
  · next hj =>
    have e2 : ((List.range 16).map fun q =>
        (((if j < 4 ∧ 64 * b + (16 * j + q) < M.bytes.length then 1 else 0 : Nat)) : Int)) =
        (List.range 16).map fun q => (((if (64 * b + 16 * j) + q < M.bytes.length then 1 else 0 : Nat)) : Int) := by
      apply List.map_congr_left
      intro q _
      rw [← Nat.add_assoc]; simp [hj]
    rw [e2, count_lt]
  · next hj =>
    have e2 : ((List.range 16).map fun q =>
        (((if j < 4 ∧ 64 * b + (16 * j + q) < M.bytes.length then 1 else 0 : Nat)) : Int)) =
        (List.range 16).map fun _ => ((0 : Nat) : Int) := by
      apply List.map_congr_left
      intro q _
      simp [hj]
    rw [e2, sum_zero_map]

theorem fsum_digest (cur : Row) (B : Blk) : zev (renv cur (.digest B) f lst p) fSumN = 0 := by
  unfold fSumN
  rw [zev_sum, List.map_map]
  have e : ((List.range 16).map ((zev (renv cur (.digest B) f lst p)) ∘ fun q => E.n (colF q))) =
      (List.range 16).map fun _ => ((0 : Nat) : Int) := by
    apply List.map_congr_left
    intro q hq
    rw [List.mem_range] at hq
    simp only [Function.comp, zev_n, renv_nxt, rowCell_digest, dc_F B q hq]
  rw [e, sum_zero_map]

/-- Next-row gated constraints vanish on transitions into padding / start rows. -/
theorem ps_kD (X : Row) (hX : X = .pad ∨ ∃ id, X = .start id) : kD X = 0 := by
  rcases hX with rfl | ⟨id, rfl⟩ <;> rfl

theorem ps_kR (X : Row) (hX : X = .pad ∨ ∃ id, X = .start id) (j : Nat) : kR X j = 0 := by
  rcases hX with rfl | ⟨id, rfl⟩ <;> rfl

theorem fr_Fchain (cur nx : Row) (hs : Step cur nx) (j : Nat) (hj1 : 1 ≤ j) (hj : j < 4) :
    zev (renv cur nx f lst p) (E.eqG (E.n (colR j)) (E.n colFprev) (E.c (colF 15))) = 0 := by
  rw [zev_eqG, zev_nR _ _ _ _ _ j (by omega)]
  cases hs with
  | round M b j' hM hb hj' =>
    simp only [kR, zev_n, zev_c, renv_nxt, renv_cur, rowCell_round, r_Fprev, r_F M b j' 15 (by decide)]
    ites
  | start M hM => simp only [kR]; rw [if_neg (by omega)]; simp
  | dnext M b hM hb => simp only [kR]; rw [if_neg (by omega)]; simp
  | r15 M b hM hb => simp [kR]
  | dlast M b hM hb _ hX => rw [ps_kR _ hX]; simp
  | pad _ hX => rw [ps_kR _ hX]; simp

theorem fr_Nd (cur nx : Row) (hs : Step cur nx) :
    zev (renv cur nx f lst p)
      (E.eqG gBlockN (E.n colNd) (.add (.mul (E.not (E.c colS)) (E.c colNd)) fSumN)) = 0 := by
  rw [zev_eqG, zev_gBlockN, zev_add, zev_mul, zev_not, zev_cS]
  cases hs with
  | start M hM =>
    rw [fsum_round]
    simp only [kS, kD, gateV, List.mem_range, zev_n, zev_c, renv_nxt, renv_cur, rowCell_round, r_Nd]
    ites
  | round M b j hM hb hj =>
    rw [fsum_round]
    simp only [kS, kD, gateV, List.mem_range, zev_n, zev_c, renv_nxt, renv_cur, rowCell_round, r_Nd]
    ites
  | r15 M b hM hb =>
    rw [fsum_digest]
    simp only [kS, kD, gateV, zev_n, zev_c, renv_nxt, renv_cur, rowCell_round, rowCell_digest, r_Nd, d_Nd]
    omega
  | dnext M b hM hb =>
    rw [fsum_round]
    simp only [kS, kD, gateV, List.mem_range, zev_n, zev_c, renv_nxt, renv_cur, rowCell_round,
      rowCell_digest, r_Nd, d_Nd]
    ites
  | dlast M b hM hb _ hX => rw [gateV_ps _ hX, ps_kD _ hX]; simp
  | pad _ hX => rw [gateV_ps _ hX, ps_kD _ hX]; simp

theorem fr_Id (cur nx : Row) (hs : Step cur nx) :
    zev (renv cur nx f lst p) (E.eqG gBlockN (E.n colId) (E.c colId)) = 0 := by
  rw [zev_eqG, zev_gBlockN]
  cases hs with
  | start M hM => simp [rc_Id, sc_Id]
  | round M b j hM hb hj => simp [rc_Id]
  | r15 M b hM hb => simp [rc_Id, dc_Id]
  | dnext M b hM hb => simp [rc_Id, dc_Id]
  | dlast M b hM hb _ hX => rw [gateV_ps _ hX, ps_kD _ hX]; simp
  | pad _ hX => rw [gateV_ps _ hX, ps_kD _ hX]; simp

/-- Block constants are copied along `R1..R15, D`. -/
theorem fr_inner (cur nx : Row) (hs : Step cur nx) (col : Nat)
    (hcol : ∀ M b j, roundCell j (blkOf M b) col = roundCell 0 (blkOf M b) col)
    (hcolD : ∀ M b, digestCell (blkOf M b) col = roundCell 0 (blkOf M b) col) :
    zev (renv cur nx f lst p) (E.eqG gInnerN (E.n col) (E.c col)) = 0 := by
  rw [zev_eqG, zev_gInnerN]
  cases hs with
  | start M hM => simp [gateV, kD]
  | round M b j hM hb hj => simp [hcol M b (j + 1), hcol M b j]
  | r15 M b hM hb => simp [hcolD, hcol M b 15]
  | dnext M b hM hb => simp [gateV, kD]
  | dlast M b hM hb _ hX => rw [gateV_ps _ hX, ps_kD _ hX]; simp
  | pad _ hX => rw [gateV_ps _ hX, ps_kD _ hX]; simp

theorem fr_Seen (cur nx : Row) (hs : Step cur nx) :
    zev (renv cur nx f lst p) (E.eqG gInnerN (E.n colSeen) (E.c colSeen)) = 0 :=
  fr_inner f lst p cur nx hs colSeen (fun M b j => by rw [r_Seen, r_Seen])
    (fun M b => by rw [d_Seen, r_Seen])

theorem fr_P80 (cur nx : Row) (hs : Step cur nx) :
    zev (renv cur nx f lst p) (E.eqG gInnerN (E.n colP80) (E.c colP80)) = 0 :=
  fr_inner f lst p cur nx hs colP80 (fun M b j => by rw [r_P80, r_P80])
    (fun M b => by rw [d_P80, r_P80])

theorem fr_Last (cur nx : Row) (hs : Step cur nx) :
    zev (renv cur nx f lst p) (E.eqG gInnerN (E.n colLast) (E.c colLast)) = 0 :=
  fr_inner f lst p cur nx hs colLast (fun M b j => by rw [r_Last, r_Last])
    (fun M b => by rw [d_Last, r_Last])

theorem fr_SeenR0 (cur nx : Row) (hs : Step cur nx) :
    zev (renv cur nx f lst p)
      (E.eqG (E.n (colR 0)) (E.n colSeen) (.mul (E.c colD) (.add (E.c colSeen) (E.c colP80)))) = 0 := by
  rw [zev_eqG, zev_nR _ _ _ _ _ 0 (by decide)]
  cases hs with
  | start M hM =>
    simp only [kR, zev_n, zev_mul, zev_add, zev_c, renv_nxt, renv_cur, rowCell_round, rowCell_start, r_Seen,
      sc_D, sc_Seen, sc_P80]
    ites
  | dnext M b hM hb =>
    simp only [kR, zev_n, zev_mul, zev_add, zev_c, renv_nxt, renv_cur, rowCell_round, rowCell_digest,
      r_Seen, d_Seen, d_P80, dc_D]
    ites
  | round M b j hM hb hj => simp [kR]
  | r15 M b hM hb => simp [kR]
  | dlast M b hM hb _ hX => rw [ps_kR _ hX]; simp
  | pad _ hX => rw [ps_kR _ hX]; simp

end

end ZkFormal.Sha.Complete
