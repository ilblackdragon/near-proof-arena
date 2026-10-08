import ZkFormal.Sha.Complete.All
namespace ZkFormal.NearV3.Candidates.ShaHeight
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha ZkFormal.Sha.Complete
open ZkFormal.Sha.Gen ZkFormal.Sha.Layout ZkFormal.Sha.Table ZkFormal.Sha.Spec

/-! Height-independent transition completeness, using the same native SHA row
semantics as the original completeness proof. No new arithmetic premises. -/

theorem family_round (cur nx : Row) (hs : Step cur nx) (f lst : Int) (p : Nat→Int)
    (e : Expr) (he : e∈cRound) : zev (renv cur nx f lst p) e=0 := by
  simp only [cRound, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff,
    or_false] at he
  obtain ⟨i, hi, l, hl, he⟩ := he
  rcases he with rfl | rfl
  · unfold roundA; rw [zev_addC]
    apply round_ctx cur nx hs
    intro M b j hM hb hj hn hW
    subst hn
    have w0 := window_at _ _ j hW i 0 (by omega)
    have w1 := window_at _ _ j hW i 1 (by omega)
    have w2 := window_at _ _ j hW i 2 (by omega)
    have w3 := window_at _ _ j hW i 3 (by omega)
    simp only [Nat.add_zero] at w0
    have hres : Holds32 (renv cur (.round j (blkOf M b)) f lst p) (fun b => E.n (colA i b))
        ((blkOf M b).A (4 * j + i + 4)) := fun b' hb' => zev_bit_n _ (by
      rw [renv_nxt, rowCell_round, rc_A j _ i b' hi hb', show 4 * j + 4 + i = 4 * j + i + 4 by omega])
    have hcar : ∀ l', l' < 2 → zev (renv cur (.round j (blkOf M b)) f lst p) (carryN (colCA i) l') =
        (carry ((blkOf M b).termsA (4 * j + i)) l' : Int) := fun l' hl' =>
      zev_carryN _ _ _ _ (carry_lt _ (termsA_lt M b hM hb _) (by simp [Blk.termsA]) l') (fun k hk => by
        rw [renv_nxt, rowCell_round, rc_CA j _ i l' k hi hl' hk])
    simp only [List.map_cons, List.map_nil]
    rw [limb_word _ _ _ l (E_lt M b _) hl w0.2,
      limb_bsig1 _ _ _ l (E_lt M b _) hl w3.2,
      limb_ch _ _ _ _ _ _ _ l (E_lt M b _) (E_lt M b _) hl w3.2 w2.2 w1.2,
      zev_kLimb M b j hj cur f lst p i l hl,
      limb_word _ _ _ l (W_lt M b hM hb _) hl (hold_nW f lst p cur _ j _ rfl i hi),
      limb_bsig0 _ _ _ l (A_lt M b _) hl w3.1,
      limb_maj _ _ _ _ _ _ _ l (A_lt M b _) (A_lt M b _) hl w3.1 w2.1 w1.1,
      limb_word _ _ _ l (A_lt M b _) hl hres, hcar l hl, A_succ4]
    have key := addC_limbs ((blkOf M b).termsA (4 * j + i)) l hl
      (zev (renv cur (.round j (blkOf M b)) f lst p) (if l = 0 then E.k 0 else carryN (colCA i) 0))
      (by split
          · rfl
          · rw [hcar 0 (by decide)])
    simp only [Blk.termsA, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at key ⊢
    omega
  · unfold roundE; rw [zev_addC]
    apply round_ctx cur nx hs
    intro M b j hM hb hj hn hW
    subst hn
    have w0 := window_at _ _ j hW i 0 (by omega)
    have w1 := window_at _ _ j hW i 1 (by omega)
    have w2 := window_at _ _ j hW i 2 (by omega)
    have w3 := window_at _ _ j hW i 3 (by omega)
    simp only [Nat.add_zero] at w0
    have hres : Holds32 (renv cur (.round j (blkOf M b)) f lst p) (fun b => E.n (colE i b))
        ((blkOf M b).Ee (4 * j + i + 4)) := fun b' hb' => zev_bit_n _ (by
      rw [renv_nxt, rowCell_round, rc_E j _ i b' hi hb', show 4 * j + 4 + i = 4 * j + i + 4 by omega])
    have hcar : ∀ l', l' < 2 → zev (renv cur (.round j (blkOf M b)) f lst p) (carryN (colCE i) l') =
        (carry ((blkOf M b).termsE (4 * j + i)) l' : Int) := fun l' hl' =>
      zev_carryN _ _ _ _ (carry_lt _ (termsE_lt M b hM hb _) (by simp [Blk.termsE]) l') (fun k hk => by
        rw [renv_nxt, rowCell_round, rc_CE j _ i l' k hi hl' hk])
    simp only [List.map_cons, List.map_nil]
    rw [limb_word _ _ _ l (A_lt M b _) hl w0.1,
      limb_word _ _ _ l (E_lt M b _) hl w0.2,
      limb_bsig1 _ _ _ l (E_lt M b _) hl w3.2,
      limb_ch _ _ _ _ _ _ _ l (E_lt M b _) (E_lt M b _) hl w3.2 w2.2 w1.2,
      zev_kLimb M b j hj cur f lst p i l hl,
      limb_word _ _ _ l (W_lt M b hM hb _) hl (hold_nW f lst p cur _ j _ rfl i hi),
      limb_word _ _ _ l (E_lt M b _) hl hres, hcar l hl, E_succ4]
    have key := addC_limbs ((blkOf M b).termsE (4 * j + i)) l hl
      (zev (renv cur (.round j (blkOf M b)) f lst p) (if l = 0 then E.k 0 else carryN (colCE i) 0))
      (by split
          · rfl
          · rw [hcar 0 (by decide)])
    simp only [Blk.termsE, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at key ⊢
    omega


theorem family_sched (cur nx : Row) (hs : Step cur nx) (f lst : Int) (p : Nat→Int)
    (e : Expr) (he : e∈cSched) : zev (renv cur nx f lst p) e=0 := by
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


theorem family_help (cur nx : Row) (hs : Step cur nx) (f lst : Int) (p : Nat→Int)
    (e : Expr) (he : e∈cHelp) : zev (renv cur nx f lst p) e=0 := by
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


theorem family_digest (cur nx : Row) (hs : Step cur nx) (f lst : Int) (p : Nat→Int)
    (e : Expr) (he : e∈cDigest) : zev (renv cur nx f lst p) e=0 := by
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


theorem family_frame (cur nx : Row) (hs : Step cur nx) (f lst : Int) (p : Nat→Int)
    (e : Expr) (he : e∈cFrame) : zev (renv cur nx f lst p) e=0 := by
  have hc := curRow_of_step cur nx hs
  simp only [cFrame, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with ((((((((he | he) | he) | he) | he) | he) | he) | he) | he)
  · simp only [List.mem_map, List.mem_range] at he
    obtain ⟨q, hq, rfl⟩ := he
    exact fr_mono f lst p cur nx hc q hq
  · rcases he with rfl | rfl | rfl
    · exact fr_F0prev f lst p cur nx hc
    · exact fr_msgC f lst p cur nx hc
    · exact fr_R0prev f lst p cur nx hc
  · simp only [List.mem_map, List.mem_range'_1] at he
    obtain ⟨j, hj, rfl⟩ := he
    exact fr_Fchain f lst p cur nx hs j (by omega) (by omega)
  · rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fr_Nd f lst p cur nx hs
    · exact fr_Id f lst p cur nx hs
    · exact fr_Seen f lst p cur nx hs
    · exact fr_P80 f lst p cur nx hs
    · exact fr_Last f lst p cur nx hs
    · exact fr_SeenR0 f lst p cur nx hs
    · exact fr_Pn f lst p cur nx hc
    · exact fr_SeenP80 f lst p cur nx hc
  · rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fr_blk1 f lst p cur nx hc
    · exact fr_blk2 f lst p cur nx hc
    · exact fr_blk3 f lst p cur nx hc
    · exact fr_blk4 f lst p cur nx hc
    · exact fr_blk5 f lst p cur nx hc
    · exact fr_blk6 f lst p cur nx hc
    · exact fr_blk7 f lst p cur nx hc
    · exact fr_blk8 f lst p cur nx hc
  · simp only [List.mem_flatMap, List.mem_map, List.mem_range] at he
    obtain ⟨j, hj, q, hq, rfl⟩ := he
    exact fr_padbyte f lst p cur nx hc j q hj hq
  · simp only [List.mem_map, List.mem_range] at he
    obtain ⟨k, hk, rfl⟩ := he
    exact fr_len14 f lst p cur nx hc k hk
  · simp only [List.mem_map, List.mem_range'_1] at he
    obtain ⟨k, hk, rfl⟩ := he
    exact fr_len15 f lst p cur nx hc k (by omega) (by omega)
  · rcases he with rfl | rfl | rfl
    · exact fr_lenNd f lst p cur nx hc
    · exact fr_Dmult1 f lst p cur nx hc
    · exact fr_Dmult2 f lst p cur nx hc

end ZkFormal.NearV3.Candidates.ShaHeight
