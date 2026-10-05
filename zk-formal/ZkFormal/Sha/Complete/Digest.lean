import ZkFormal.Sha.Complete.Help

/-! # Completeness: `cDigest` (final addition) -/

namespace ZkFormal.Sha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Gen ZkFormal.Sha.Layout ZkFormal.Sha.Table

theorem fin_lt (M : Msg) (b w : Nat) : (blkOf M b).fin w < 2 ^ 32 := by
  unfold Blk.fin; split
  · exact A_lt M b _
  · exact E_lt M b _

theorem limbN_zero (x : Nat) : limbN x 0 = lo16 x := rfl
theorem limbN_one (x : Nat) : limbN x 1 = hi16 x := rfl

theorem complete_cDigest : CompleteFamStmt cDigest := by
  intro msgs hok t pub r hr e he
  apply eval_honest_zero
  rw [henv_eq]
  have hs := step_at msgs hok t r hr
  generalize rowAt msgs r = cur at hs ⊢
  generalize rowAt msgs ((r + 1) % (honestTrace msgs).height t) = nx at hs ⊢
  generalize (if r = 0 then 1 else 0 : Int) = f
  generalize (if r + 1 = (honestTrace msgs).height t then 1 else 0 : Int) = lst
  generalize (fun i => ((pub.getD i 0).toNat : Int)) = p
  simp only [cDigest, List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨w, hw, l, hl, rfl⟩ := he
  rw [zev_addC]
  have hD : zev (renv cur nx f lst p) (E.n colD) = ((kD nx : Nat) : Int) := by simp [cell_D]
  rw [hD]
  cases hs with
  | r15 M b hM hb =>
    simp only [kD]
    have hfin := fin_lt M b w
    have hin := getD_lt (hin_w32 M b) w
    have hcl : ∀ l, carry [(blkOf M b).hin.getD w 0, (blkOf M b).fin w] l < 8 := fun l =>
      carry_lt _ (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption) (by simp) l
    have hc : ∀ l', l' < 2 → zev (renv (.round 15 (blkOf M b)) (.digest (blkOf M b)) f lst p)
        (carryN (colCSt w) l') = (carry [(blkOf M b).hin.getD w 0, (blkOf M b).fin w] l' : Int) :=
      fun l' hl' => zev_carryN _ _ _ _ (hcl l') (fun k hk => by
        rw [renv_nxt, rowCell_digest, dc_CSt _ w l' k hw hl' hk])
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [limb_word _ _ ((blkOf M b).fin w) l hfin hl (fun b' hb' => zev_bit_c _ (by
          rw [renv_cur, rowCell_round, rc_St 15 _ w b' hw hb']; unfold Blk.fin; split <;>
            first | rfl | (congr 2; omega))),
      limb_word _ _ ((blkOf M b).hout w) l (hout_lt M b w) hl (fun b' hb' => zev_bit_n _ (by
          rw [renv_nxt, rowCell_digest, dc_St _ w b' hw hb'])), hc l hl]
    simp only [zev_c, renv_cur, rowCell_round, rc_Hin _ _ w l hw hl]
    have hsp := carry_spec [(blkOf M b).hin.getD w 0, (blkOf M b).fin w]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsp
    have hout : (blkOf M b).hout w = ((blkOf M b).hin.getD w 0 + ((blkOf M b).fin w + 0)) % 2 ^ 32 := by
      simp [Blk.hout, ArenaCore.SHA256.add32]
    rw [← hout] at hsp
    rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
    · simp only [if_true, zev_k, limbN_zero]; omega
    · simp only [Nat.one_ne_zero, if_false, limbN_one]
      rw [hc 0 (by decide)]; omega
  | start M hM => simp [kD]
  | round M b j hM hb hj => simp [kD]
  | dnext M b hM hb => simp [kD]
  | dlast M b hM hb _ hX => rcases hX with rfl | ⟨id, rfl⟩ <;> simp [kD]
  | pad _ hX => rcases hX with rfl | ⟨id, rfl⟩ <;> simp [kD]

end ZkFormal.Sha.Complete
