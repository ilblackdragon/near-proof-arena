import ZkFormal.Near.Render.Proof.RcptDep1

/-!
# ZkFormal.Near.Render.Proof.RcptDep2 — `cDep` on a `DEP` row: `aft`, `tot`, `q`, `tot − q`
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false

namespace RcptP

open RcptGen

theorem conv8_eq (x : Expr) (dl : Nat → Expr) : Rcpt.conv Rcpt.S_LE x dl =
    sum [smul 0 x, smul 0 (dl 0), smul 232 (dl 1), smul 137 (dl 2), smul 4 (dl 3), smul 35 (dl 4),
      smul 199 (dl 5), smul 138 (dl 6)] := rfl

theorem convS_row (v : Nat → Nat) (i : Nat) : conv Rcpt.S_LE v i =
    232 * (if 2 ≤ i then v (i - 2) else 0) + 137 * (if 3 ≤ i then v (i - 3) else 0) +
      4 * (if 4 ≤ i then v (i - 4) else 0) + 35 * (if 5 ≤ i then v (i - 5) else 0) +
      199 * (if 6 ≤ i then v (i - 6) else 0) + 138 * (if 7 ≤ i then v (i - 7) else 0) := by
  rw [conv_eq]
  simp only [sumR, Rcpt.S_LE, List.length_cons, List.length_nil, List.getD_cons_zero, List.getD_cons_succ]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ 7 ≤ i by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  any_goals simp
  all_goals simp only [show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega,
    show 5 ≤ i by omega, show 6 ≤ i by omega, show 7 ≤ i by omega, show 0 ≤ i by omega, ↓reduceIte]
  all_goals omega

section
variable {c : WfClaim} {e : Ext} {r i : Nat}

/-- **`pA`–`pD` on a `DEP` row.** -/
theorem dp_ABCD (hg : Good c.1 e) (hr : r < NN e) (hi : i < 16) {nx : Nat → Fp}
    (hn : i < 15 → nx = cF c.1 e (.seg r 17 (i + 1))) :
    ∀ x ∈ pA ++ pB ++ pC ++ pD, evR (cF c.1 e (.seg r 17 i)) nx false false (publicOf c) x = 0 := by
  have D := depOk hg hr
  have hAft : ∀ {i' : Nat} {nx' : Nat → Fp}, i' < 16 →
      evR (cF c.1 e (.seg r 17 i')) nx' false false (publicOf c) Rcpt.aftE = Fp.ofNat (Seg.aftB (Df c.1 e r) i') :=
    fun hi' => by rw [Rcpt.aftE, bitsX_seg (by decide) (fun j hj => dx_A hj) (Nat.mod_lt _ (by decide)), sa_mod D hi']
  have h8 : cF c.1 e (.seg r 17 i) (Rcpt.xb 8) = Fp.ofNat (chain (Seg.y1 (Df c.1 e r)) (i + 1)) := by
    rw [cF_xb (by decide), dx_8, sa_div D, bitOf_small (c1d_le D _)]
  have hTot : ∀ {nx' : Nat → Fp}, evR (cF c.1 e (.seg r 17 i)) nx' false false (publicOf c) (Rcpt.bitsX 9 8) =
      Fp.ofNat (Seg.totB (Df c.1 e r) i) := by
    intro nx'; rw [bitsX_seg (by decide) (fun j hj => dx_B hj) (Nat.mod_lt _ (by decide)), stt_mod D hi]
  have h17 : cF c.1 e (.seg r 17 i) (Rcpt.xb 17) = Fp.ofNat (chain (Seg.y2 (Df c.1 e r)) (i + 1)) := by
    rw [cF_xb (by decide), dx_17, stt_div D, bitOf_small (c2d_le D _)]
  have hQ : ∀ {nx' : Nat → Fp}, evR (cF c.1 e (.seg r 17 i)) nx' false false (publicOf c) (Rcpt.bitsX 18 8) =
      Fp.ofNat (Seg.qB (Df c.1 e r) i) := by
    intro nx'; rw [bitsX_seg (by decide) (fun j hj => dx_C hj) (Nat.mod_lt _ (by decide)), sq_mod D hi]
  have hQ2 : ∀ {nx' : Nat → Fp}, evR (cF c.1 e (.seg r 17 i)) nx' false false (publicOf c) (Rcpt.bitsX 26 12) =
      Fp.ofNat (chain (Seg.y3 (Df c.1 e r)) (i + 1)) := by
    intro nx'; rw [bitsX_seg (by decide) (fun j hj => dx_D hj) (by rw [sq_div D]; have := c3d_le D (i + 1); omega),
      sq_div D]
  have hDv : ∀ {nx' : Nat → Fp}, evR (cF c.1 e (.seg r 17 i)) nx' false false (publicOf c) (Rcpt.bitsX 38 8) =
      Fp.ofNat (Seg.ddv (Df c.1 e r) i) :=
    bitsX_seg (by decide) (fun j hj => dx_E hj) (ddv_lt D i)
  have h46 : cF c.1 e (.seg r 17 i) (Rcpt.xb 46) = Fp.ofNat (Seg.dbr (Df c.1 e r) (i + 1)) := by
    rw [cF_xb (by decide), dx_46, bitOf_small (dbr_le D _)]
  intro x hx
  simp only [List.mem_append] at hx
  rcases hx with ((hA | hB) | hC) | hD
  · simp only [pA, List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Rcpt.dp, evR_mul, evR_sub, evR_add, evR_c, evR_smul, evR_sum_cons, evR_sum_nil, dp_one, dp_bef,
        dp_b, dp_c1, hAft hi, h8]
      have E := fp_eq (chain_step (Seg.y1 (Df c.1 e r)) i)
      simp only [Seg.y1, ofNat_add_e, ofNat_mul_e] at E
      have E2 := sa_mod D hi
      simp only [Seg.sa, Seg.y1] at E2
      rw [E2] at E
      simp only [natCast_eq]; grind
    · simp only [Rcpt.dp, evR_mul, evR_c, dp_one, cF_fs, dp_c1]
      by_cases h0 : i = 0
      · subst h0; simp only [↓reduceIte, chain, ofNat0]; grind
      · simp only [h0, ↓reduceIte]; grind
    · simp only [Rcpt.dp, evR_mul3, evR_not, evR_sub, evR_c, evR_n, dp_one, dp_fe, h8]
      by_cases h15 : i = 15
      · simp only [h15, ↓reduceIte]; grind
      · simp only [h15, ↓reduceIte, hn (by omega), dp_c1]; grind
    · simp only [Rcpt.dp, evR_mul3, evR_c, dp_one, dp_fe, h8]
      by_cases h15 : i = 15
      · subst h15; simp only [↓reduceIte, c1d_final D, ofNat0]; grind
      · simp only [h15, ↓reduceIte]; grind
    · simp only [Rcpt.dp, evR_mul3, evR_sub, evR_c, evR_k, dp_one, cF_fs, dp_dsum, hAft hi]
      by_cases h0 : i = 0
      · subst h0
        simp only [↓reduceIte, runA_zero D, ofNat_sub (show Seg.aftB (Df c.1 e r) 0 ≤ 255 from
          Nat.le_of_lt_succ (leBytes_getD_lt _ _ _)), natCast_eq]; grind
      · simp only [h0, ↓reduceIte]; grind
    · simp only [Rcpt.dp, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, dp_one, dp_fe, dp_dsum]
      by_cases h15 : i = 15
      · simp only [h15, ↓reduceIte]; grind
      · rw [hn (by omega), bitsXn_seg (by decide) (fun j hj => dx_A hj) (Nat.mod_lt _ (by decide)),
          sa_mod D (by omega), dp_dsum, runA_succ D, ofNat_add_e, ofNat_sub (show Seg.aftB (Df c.1 e r) (i + 1) ≤ 255 from
          Nat.le_of_lt_succ (leBytes_getD_lt _ _ _))]
        simp only [h15, ↓reduceIte, natCast_eq]; grind
    · simp only [Rcpt.dp, evR_mul3, evR_mul, evR_sub, evR_c, evR_k, dp_one, dp_fe, dp_dsum, dp_invB]
      by_cases h15 : i = 15
      · subst h15
        simp only [↓reduceIte]
        rw [ofNat_invP (ofNat_ne_zero (runA_ne D) (by
          have := runA_lt D 15 (by omega); have : 4096 < ZkFormal.Algebra.P := by decide
          rw [P_def]; omega))]
        simp only [natCast_eq, ofNat1]; grind
      · simp only [h15, ↓reduceIte]; grind
  · simp only [pB, List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl | rfl | rfl
    · simp only [Rcpt.dp, evR_mul, evR_sub, evR_add, evR_c, evR_smul, evR_sum_cons, evR_sum_nil, dp_one, dp_lk,
        dp_c2, hAft hi, hTot, h17]
      have E := fp_eq (chain_step (Seg.y2 (Df c.1 e r)) i)
      simp only [Seg.y2, ofNat_add_e, ofNat_mul_e] at E
      have E2 := stt_mod D hi
      simp only [Seg.stt, Seg.y2] at E2
      rw [E2] at E
      simp only [natCast_eq]; grind
    · simp only [Rcpt.dp, evR_mul, evR_c, dp_one, cF_fs, dp_c2]
      by_cases h0 : i = 0
      · subst h0; simp only [↓reduceIte, chain, ofNat0]; grind
      · simp only [h0, ↓reduceIte]; grind
    · simp only [Rcpt.dp, evR_mul3, evR_not, evR_sub, evR_c, evR_n, dp_one, dp_fe, h17]
      by_cases h15 : i = 15
      · simp only [h15, ↓reduceIte]; grind
      · simp only [h15, ↓reduceIte, hn (by omega), dp_c2]; grind
    · simp only [Rcpt.dp, evR_mul3, evR_c, dp_one, dp_fe, h17]
      by_cases h15 : i = 15
      · subst h15; simp only [↓reduceIte, c2d_final D, ofNat0]; grind
      · simp only [h15, ↓reduceIte]; grind
  · simp only [pC, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl | rfl
    · simp only [Rcpt.dp, conv8_eq, dD, evR_mul, evR_sub, evR_add, evR_c, evR_smul, evR_sum_cons, evR_sum_nil,
        dp_one, dp_st, dp_c3, hQ, hQ2, dp_dl (show 0 < 7 by decide), dp_dl (show 1 < 7 by decide),
        dp_dl (show 2 < 7 by decide), dp_dl (show 3 < 7 by decide), dp_dl (show 4 < 7 by decide),
        dp_dl (show 5 < 7 by decide), dp_dl (show 6 < 7 by decide)]
      have E := fp_eq (chain_step (Seg.y3 (Df c.1 e r)) i)
      have E3 := fp_eq (convS_row (Seg.stB (Df c.1 e r)) i)
      simp only [ofNat_add_e, ofNat_mul_e] at E E3
      have E2 := sq_mod D hi
      simp only [Seg.sq] at E2
      rw [E2] at E
      simp only [Seg.y3] at E E3 ⊢
      simp only [natCast_eq, ofNat0] at E E3 ⊢; grind
    · simp only [Rcpt.dp, evR_mul, evR_c, dp_one, cF_fs, dp_c3]
      by_cases h0 : i = 0
      · subst h0; simp only [↓reduceIte, chain, ofNat0]; grind
      · simp only [h0, ↓reduceIte]; grind
    · simp only [Rcpt.dp, evR_mul3, evR_not, evR_sub, evR_c, evR_n, dp_one, dp_fe, hQ2]
      by_cases h15 : i = 15
      · simp only [h15, ↓reduceIte]; grind
      · simp only [h15, ↓reduceIte, hn (by omega), dp_c3]; grind
    · simp only [Rcpt.dp, evR_mul3, evR_c, dp_one, dp_fe, hQ2]
      by_cases h15 : i = 15
      · subst h15; simp only [↓reduceIte, c3d_final D, ofNat0]; grind
      · simp only [h15, ↓reduceIte]; grind
    · simp only [Rcpt.dp, evR_mul3, evR_not, evR_sub, evR_c, evR_n, dp_one, dp_fe, dp_st]
      by_cases h15 : i = 15
      · simp only [h15, ↓reduceIte]; grind
      · simp only [h15, ↓reduceIte, hn (by omega), dp_dl (show 0 < 7 by decide), show 0 < i + 1 by omega,
          show i + 1 - 1 - 0 = i by omega]; grind
  · simp only [pD, List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl | rfl | rfl
    · simp only [Rcpt.dp, evR_mul, evR_sub, evR_add, evR_c, evR_smul, dp_one, hTot, hQ, hDv, h46, dp_c4]
      have E := fp_eq (ddv_step D i)
      simp only [ofNat_add_e, ofNat_mul_e] at E
      simp only [natCast_eq]; grind
    · simp only [Rcpt.dp, evR_mul, evR_c, dp_one, cF_fs, dp_c4]
      by_cases h0 : i = 0
      · subst h0; simp only [↓reduceIte, dbr_zero D, ofNat0]; grind
      · simp only [h0, ↓reduceIte]; grind
    · simp only [Rcpt.dp, evR_mul3, evR_not, evR_sub, evR_c, evR_n, dp_one, dp_fe, h46]
      by_cases h15 : i = 15
      · simp only [h15, ↓reduceIte]; grind
      · simp only [h15, ↓reduceIte, hn (by omega), dp_c4]; grind
    · simp only [Rcpt.dp, evR_mul, evR_mul3, evR_c, dp_one, dp_fe, h46, cF_big]
      by_cases h15 : i = 15
      · subst h15
        cases hb : (Df c.1 e r).big
        · simp only [b2n_false, ofNat0]; grind
        · simp only [↓reduceIte, dbr_final D hb, ofNat0]; grind
      · simp only [h15, ↓reduceIte]; grind

end

end RcptP

end ZkFormal.Near.Render
