import ZkFormal.Sha.Complete.Round

/-! # Completeness: `cSched` (message schedule for `R4..R15`) -/

namespace ZkFormal.Sha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Gen ZkFormal.Sha.Layout ZkFormal.Sha.Table
open ZkFormal.Sha.Spec

/-- A `gSched`-gated constraint vanishes unless the next row is `R(j+1)`, `j ≥ 3`, after `Rj`. -/
theorem schedGate (cur nx : Row) (hs : Step cur nx) (f lst : Int) (p : Nat → Int) (x : Int)
    (h : ∀ M b j, MOk M → b < nb M → 3 ≤ j → j < 15 → cur = .round j (blkOf M b) →
      nx = .round (j + 1) (blkOf M b) → x = 0) :
    zev (renv cur nx f lst p) gSched * x = 0 := by
  rw [zev_gSched]
  cases hs with
  | round M b j hM hb hj =>
    by_cases h3 : 3 ≤ j
    · rw [h M b j hM hb h3 hj rfl rfl, Int.mul_zero]
    · rw [gateV_round0 _ _ _ (by rw [List.mem_range'_1]; omega), Int.zero_mul]
  | start M hM => rw [gateV_round0 _ _ _ (by decide), Int.zero_mul]
  | dnext M b hM hb => rw [gateV_round0 _ _ _ (by decide), Int.zero_mul]
  | r15 M b hM hb => simp [gateV]
  | dlast M b hM hb _ hX => rw [gateV_ps _ hX, Int.zero_mul]
  | pad _ hX => rw [gateV_ps _ hX, Int.zero_mul]

theorem complete_cSched : CompleteFamStmt cSched := by
  intro msgs hok t pub r hr e he
  apply eval_honest_zero
  rw [henv_eq]
  have hs := step_at msgs hok t r hr
  generalize rowAt msgs r = cur at hs ⊢
  generalize rowAt msgs ((r + 1) % (honestTrace msgs).height t) = nx at hs ⊢
  generalize (if r = 0 then 1 else 0 : Int) = f
  generalize (if r + 1 = (honestTrace msgs).height t then 1 else 0 : Int) = lst
  generalize (fun i => ((pub.getD i 0).toNat : Int)) = p
  simp only [cSched, List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨i, hi, l, hl, rfl⟩ := he
  unfold sched; rw [zev_addC]
  apply schedGate cur nx hs
  intro M b j hM hb hj3 hj hc hn
  subst hc hn
  -- the schedule word `t = 4(j+1)+i` and its inputs
  have hW := fun s => W_lt M b hM hb s
  have hx2 : Holds32 (renv (.round j (blkOf M b)) (.round (j + 1) (blkOf M b)) f lst p) (w2 i)
      ((blkOf M b).W (4 * j + i + 2)) := by
    intro b' hb'
    unfold w2
    split
    · exact zev_bit_c _ (by
        rw [renv_cur, rowCell_round, rc_W j _ (i + 2) b' (by omega) hb', ← Nat.add_assoc])
    · exact zev_bit_n _ (by
        rw [renv_nxt, rowCell_round, rc_W (j + 1) _ (i - 2) b' (by omega) hb',
          show 4 * (j + 1) + (i - 2) = 4 * j + i + 2 by omega])
  have hx7 : zev (renv (.round j (blkOf M b)) (.round (j + 1) (blkOf M b)) f lst p) (w7 i l) =
      (limbN ((blkOf M b).W (4 * j + i - 3)) l : Int) := by
    unfold w7
    split
    · rw [zev_c, renv_cur, rowCell_round, rc_W3 j _ i l (by omega) hl, if_pos (by omega),
        show 4 * (j - 1) + i + 1 = 4 * j + i - 3 by omega]
    · rw [limb_word _ _ _ l (hW _) hl (hold_cW f lst p _ _ j _ rfl 0 (by decide)),
        show 4 * j + 0 = 4 * j + i - 3 by omega]
  have hres : Holds32 (renv (.round j (blkOf M b)) (.round (j + 1) (blkOf M b)) f lst p)
      (fun b => E.n (colW i b)) ((blkOf M b).W (4 * j + i + 4)) := by
    intro b' hb'
    exact zev_bit_n _ (by
      rw [renv_nxt, rowCell_round, rc_W (j + 1) _ i b' hi hb', show 4 * (j + 1) + i = 4 * j + i + 4 by omega])
  have hscl : ∀ l', l' < 2 → (blkOf M b).schedCarry (4 * j + i + 4) l' < 8 := by
    intro l' _
    have h1 := ssig1_lt _ (hW (4 * j + i + 4 - 2))
    have h2 := hW (4 * j + i + 4 - 7)
    have h3 := ssig0_lt _ (hW (4 * j + i + 4 - 16 + 1))
    have h4 := hW (4 * j + i + 4 - 16)
    unfold Blk.schedCarry Blk.help limbN lo16 hi16
    dsimp only
    split <;> simp only [if_true, Nat.one_ne_zero, if_false] <;> omega
  have hcar : ∀ l', l' < 2 →
      zev (renv (.round j (blkOf M b)) (.round (j + 1) (blkOf M b)) f lst p) (carryN (colCW i) l') =
        ((blkOf M b).schedCarry (4 * j + i + 4) l' : Int) := fun l' hl' =>
    zev_carryN _ _ _ _ (hscl l' hl') (fun k hk => by
      rw [renv_nxt, rowCell_round, rc_CW (j + 1) _ i l' k hi hl' hk, if_pos (by omega),
        show 4 * (j + 1) + i = 4 * j + i + 4 by omega])
  have hcin : zev (renv (.round j (blkOf M b)) (.round (j + 1) (blkOf M b)) f lst p)
      (if l = 0 then E.k 0 else carryN (colCW i) 0) =
      if l = 0 then 0 else ((blkOf M b).schedCarry (4 * j + i + 4) 0 : Int) := by
    split
    · rfl
    · exact hcar 0 (by decide)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [limb_ssig1 _ _ _ l (hW _) hl hx2, hx7, zev_c, renv_cur, rowCell_round,
    rc_I12 j _ i l hi hl, if_pos hj3, limb_word _ _ _ l (hW _) hl hres, hcar l hl, hcin]
  -- arithmetic
  have hrec : (blkOf M b).W (4 * j + i + 4) =
      (ArenaCore.SHA256.ssig1 ((blkOf M b).W (4 * j + i + 2)) + (blkOf M b).W (4 * j + i - 3) +
        ArenaCore.SHA256.ssig0 ((blkOf M b).W (4 * j + i - 11)) + (blkOf M b).W (4 * j + i - 12)) % 2 ^ 32 := by
    unfold Blk.W
    rw [show 4 * j + i + 4 = (4 * j + i - 12) + 16 by omega, Wt_rec' _ (words16 M b hb),
      show 4 * j + i - 12 + 14 = 4 * j + i + 2 by omega, show 4 * j + i - 12 + 9 = 4 * j + i - 3 by omega,
      show 4 * j + i - 12 + 1 = 4 * j + i - 11 by omega]
  have h1 := ssig1_lt _ (hW (4 * j + i + 2))
  have h2 := hW (4 * j + i - 3)
  have h3 := ssig0_lt _ (hW (4 * j + i - 11))
  have h4 := hW (4 * j + i - 12)
  have hh : 4 * (j - 3) + i = 4 * j + i - 12 := by omega
  have hs1 : 4 * j + i - 12 + 1 = 4 * j + i - 11 := by omega
  have hs2 : 4 * j + i + 4 - 2 = 4 * j + i + 2 := by omega
  have hs3 : 4 * j + i + 4 - 7 = 4 * j + i - 3 := by omega
  have hs4 : 4 * j + i + 4 - 16 = 4 * j + i - 12 := by omega
  unfold Blk.schedCarry Blk.help
  simp only [hh, hs1, hs2, hs3, hs4]
  rw [hrec]
  generalize ArenaCore.SHA256.ssig1 ((blkOf M b).W (4 * j + i + 2)) = a at h1 ⊢
  generalize (blkOf M b).W (4 * j + i - 3) = b7 at h2 ⊢
  generalize ArenaCore.SHA256.ssig0 ((blkOf M b).W (4 * j + i - 11)) = c at h3 ⊢
  generalize (blkOf M b).W (4 * j + i - 12) = d at h4 ⊢
  unfold limbN lo16 hi16
  rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
  · simp only [if_true]; omega
  · simp only [Nat.one_ne_zero, if_false, if_true]; omega

end ZkFormal.Sha.Complete
