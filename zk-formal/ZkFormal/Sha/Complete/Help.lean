import ZkFormal.Sha.Complete.Words

/-! # Completeness: `cHelp` (schedule helpers and the chaining value) -/

namespace ZkFormal.Sha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Gen ZkFormal.Sha.Layout ZkFormal.Sha.Table

theorem gateV_ps (X : Row) (hX : X = .pad ∨ ∃ id, X = .start id) (js : List Nat) : gateV X js = 0 := by
  rcases hX with rfl | ⟨id, rfl⟩ <;> rfl

theorem gateV_round (j : Nat) (B : Blk) (js : List Nat) (h : j ∈ js) : gateV (.round j B) js = 1 := by
  simp [gateV, h]

theorem gateV_round0 (j : Nat) (B : Blk) (js : List Nat) (h : j ∉ js) : gateV (.round j B) js = 0 := by
  simp [gateV, h]

theorem mem_help (j : Nat) (hj : j < 15) : j + 1 ∈ List.range' 1 15 := by
  rw [List.mem_range'_1]; omega

theorem nmem_help0 : 0 ∉ List.range' 1 15 := by decide

/-- A `gHelp`-gated constraint vanishes unless the next row is `R(j+1)` after `Rj`. -/
theorem helpGate (cur nx : Row) (hs : Step cur nx) (f lst : Int) (p : Nat → Int) (x : Int)
    (h : ∀ M b j, MOk M → b < nb M → j < 15 → cur = .round j (blkOf M b) →
      nx = .round (j + 1) (blkOf M b) → x = 0) :
    zev (renv cur nx f lst p) gHelp * x = 0 := by
  rw [zev_gHelp]
  cases hs with
  | round M b j hM hb hj => rw [h M b j hM hb hj rfl rfl, Int.mul_zero]
  | start M hM => rw [gateV_round0 _ _ _ nmem_help0, Int.zero_mul]
  | dnext M b hM hb => rw [gateV_round0 _ _ _ nmem_help0, Int.zero_mul]
  | r15 M b hM hb => simp [gateV]
  | dlast M b hM hb _ hX => rw [gateV_ps _ hX, Int.zero_mul]
  | pad _ hX => rw [gateV_ps _ hX, Int.zero_mul]

section
variable (M : Msg) (b j : Nat) (hM : MOk M) (hb : b < nb M) (f lst : Int) (p : Nat → Int)

theorem hold_cW (cur nx : Row) (j : Nat) (B : Blk) (hc : cur = .round j B) (i : Nat) (hi : i < 4) :
    Holds32 (renv cur nx f lst p) (fun b => E.c (colW i b)) (B.W (4 * j + i)) := by
  intro b hb; subst hc
  exact zev_bit_c _ (by rw [renv_cur, rowCell_round, rc_W j B i b hi hb])

theorem hold_nW (cur nx : Row) (j : Nat) (B : Blk) (hc : nx = .round j B) (i : Nat) (hi : i < 4) :
    Holds32 (renv cur nx f lst p) (fun b => E.n (colW i b)) (B.W (4 * j + i)) := by
  intro b hb; subst hc
  exact zev_bit_n _ (by rw [renv_nxt, rowCell_round, rc_W j B i b hi hb])

theorem hold_w15 (j : Nat) (B : Blk) (_hj : j < 15) (i : Nat) (hi : i < 4) :
    Holds32 (renv (.round j B) (.round (j + 1) B) f lst p) (w15 i) (B.W (4 * j + i + 1)) := by
  intro b hb
  unfold w15
  split
  · exact hold_cW f lst p _ _ j B rfl (i + 1) (by omega) b hb
  · have := hold_nW f lst p (.round j B) _ (j + 1) B rfl 0 (by decide) b hb
    rw [show 4 * (j + 1) + 0 = 4 * j + i + 1 by omega] at this
    exact this
end

theorem complete_cHelp : CompleteFamStmt cHelp := by
  intro msgs hok t pub r hr e he
  apply eval_honest_zero
  rw [henv_eq]
  have hs := step_at msgs hok t r hr
  generalize rowAt msgs r = cur at hs ⊢
  generalize rowAt msgs ((r + 1) % (honestTrace msgs).height t) = nx at hs ⊢
  generalize (if r = 0 then 1 else 0 : Int) = f
  generalize (if r + 1 = (honestTrace msgs).height t then 1 else 0 : Int) = lst
  generalize (fun i => ((pub.getD i 0).toNat : Int)) = p
  simp only [cHelp, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
    List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with ((⟨i, hi, l, hl, he⟩ | ⟨i, hi, l, hl, rfl⟩) | ⟨w, hw, l, hl, he⟩)
  · rcases he with rfl | rfl | rfl
    · -- I4
      rw [zev_eqG]
      apply helpGate cur nx hs
      intro M b j hM hb hj hc hn
      subst hc hn
      rw [zev_add, limb_ssig0 _ _ _ l (W_lt M b hM hb _) hl (hold_w15 f lst p j _ hj i hi),
        limb_word _ _ _ l (W_lt M b hM hb _) hl (hold_cW f lst p _ _ j _ rfl i hi)]
      simp only [zev_n, renv_nxt, rowCell_round, rc_I4 _ _ i l hi hl, Blk.help]
      rw [if_pos (by omega), show 4 * (j + 1 - 1) + i = 4 * j + i by omega]
      simp only [Int.natCast_add]; omega
    · -- I8
      rw [zev_eqG]
      apply helpGate cur nx hs
      intro M b j hM hb hj hc hn
      subst hc hn
      simp only [zev_n, zev_c, renv_nxt, renv_cur, rowCell_round, rc_I8 _ _ i l hi hl,
        rc_I4 _ _ i l hi hl]
      by_cases h1 : 1 ≤ j
      · rw [if_pos (by omega), if_pos h1, show j + 1 - 2 = j - 1 by omega]; omega
      · rw [if_neg (by omega), if_neg h1]; omega
    · -- I12
      rw [zev_eqG]
      apply helpGate cur nx hs
      intro M b j hM hb hj hc hn
      subst hc hn
      simp only [zev_n, zev_c, renv_nxt, renv_cur, rowCell_round, rc_I12 _ _ i l hi hl,
        rc_I8 _ _ i l hi hl]
      by_cases h1 : 2 ≤ j
      · rw [if_pos (by omega), if_pos h1, show j + 1 - 3 = j - 2 by omega]; omega
      · rw [if_neg (by omega), if_neg h1]; omega
  · -- W3
    rw [zev_eqG]
    apply helpGate cur nx hs
    intro M b j hM hb hj hc hn
    subst hc hn
    rw [limb_word _ _ _ l (W_lt M b hM hb _) hl (hold_cW f lst p _ _ j _ rfl (i + 1) (by omega))]
    simp only [zev_n, renv_nxt, rowCell_round, rc_W3 _ _ i l hi hl]
    rw [if_pos (by omega), show 4 * (j + 1 - 1) + i + 1 = 4 * j + (i + 1) by omega]; omega
  · rcases he with rfl | rfl
    · -- Hin copy
      rw [zev_eqG]
      apply helpGate cur nx hs
      intro M b j hM hb hj hc hn
      subst hc hn
      simp only [zev_n, zev_c, renv_nxt, renv_cur, rowCell_round, rc_Hin _ _ w l hw hl]
      omega
    · -- Hin load on R0
      rw [zev_eqG, zev_nR _ _ _ _ _ 0 (by decide)]
      cases hs with
      | start M hM =>
        rw [limb_word _ _ (ivW w) l (ivW_lt w) hl (fun b hb => zev_bit_c _ (by
          rw [renv_cur, rowCell_start, sc_St _ w b hw hb]))]
        simp only [kR, zev_n, renv_nxt, rowCell_round, rc_Hin _ _ w l hw hl, hin_zero]
        simp [ivW]
      | dnext M b hM hb =>
        rw [limb_word _ _ ((blkOf M b).hout w) l (hout_lt M b w) hl (fun b hb => zev_bit_c _ (by
          rw [renv_cur, rowCell_digest, dc_St _ w b hw hb]))]
        simp only [kR, zev_n, renv_nxt, rowCell_round, rc_Hin _ _ w l hw hl,
          hin_succ_getD M b (by omega) w hw]
        simp
      | round M b j hM hb hj => simp [kR]
      | r15 M b hM hb => simp [kR]
      | dlast M b hM hb _ hX => rcases hX with rfl | ⟨id, rfl⟩ <;> simp [kR]
      | pad _ hX => rcases hX with rfl | ⟨id, rfl⟩ <;> simp [kR]

end ZkFormal.Sha.Complete
