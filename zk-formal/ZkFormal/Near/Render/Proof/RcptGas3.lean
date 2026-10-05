import ZkFormal.Near.Render.Proof.RcptGas2

/-!
# ZkFormal.Near.Render.Proof.RcptGas3 — `cGas`: `burnt = G·p`, `ramt = G·surplus`, running tokens;
`gasFam : FamOk cGas`
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false

namespace RcptP

open RcptGen

theorem conv5_eq (x : Expr) (dl : Nat → Expr) : Rcpt.conv (Rcpt.G_LE.take 5) x dl =
    sum [smul 196 x, smul 164 (dl 0), smul 183 (dl 1), smul 246 (dl 2), smul 51 (dl 3)] := rfl

/-- The convolution by `G` on row `i`, with the delay line `[j < i] v (i − 1 − j)`. -/
theorem convG_row (v : Nat → Nat) (i : Nat) : conv (Rcpt.G_LE.take 5) v i =
    196 * v i + 164 * (if 0 < i then v (i - 1 - 0) else 0) + 183 * (if 1 < i then v (i - 1 - 1) else 0) +
      246 * (if 2 < i then v (i - 1 - 2) else 0) + 51 * (if 3 < i then v (i - 1 - 3) else 0) := by
  rw [conv_eq]
  simp only [sumR, Rcpt.G_LE, List.take, List.length_cons, List.length_nil, List.getD_cons_zero,
    List.getD_cons_succ, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i by omega) with rfl | rfl | rfl | rfl | h
  · simp
  · simp
  · simp
  · simp
  · simp only [show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega,
      show 0 < i by omega, show 1 < i by omega, show 2 < i by omega, show 3 < i by omega, ↓reduceIte,
      show i - 1 - 0 = i - 1 by omega, show i - 1 - 1 = i - 2 by omega, show i - 1 - 2 = i - 3 by omega,
      show i - 1 - 3 = i - 4 by omega]
    omega

section
variable {c : WfClaim} {e : Ext} {r i : Nat}

/-- **`gB`, `gC`, `gD` on a `GP` row.** -/
theorem gp_BCD (hg : Good c.1 e) (hr : r < NN e) (hi : i < 16) {nx : Nat → Fp}
    (hn : i < 15 → nx = cF c.1 e (.seg r 15 (i + 1))) :
    ∀ x ∈ gB ++ gC ++ gD, evR (cF c.1 e (.seg r 15 i)) nx false false (publicOf c) x = 0 := by
  have G := gasOk hg hr (Link.wf_bounds c).2.2.1
  have hh : Link.Hdr c := ⟨hg.pv, hg.chain⟩
  have hB : ∀ {nx' : Nat → Fp}, evR (cF c.1 e (.seg r 15 i)) nx' false false (publicOf c) (Rcpt.bitsX 9 11) =
      Fp.ofNat (Seg.sb (Df c.1 e r) (BG c.1) i / 256) :=
    bitsX_seg (by decide) (fun j hj => gx_B hj) (by rw [sb_div G]; have := c2_le G (i + 1); omega)
  have hR : ∀ {nx' : Nat → Fp}, evR (cF c.1 e (.seg r 15 i)) nx' false false (publicOf c) (Rcpt.bitsX 20 11) =
      Fp.ofNat (Seg.sr (Df c.1 e r) (BG c.1) i / 256) :=
    bitsX_seg (by decide) (fun j hj => gx_R hj) (by rw [sr_div G]; have := c3_le G (i + 1); omega)
  have hT : ∀ {nx' : Nat → Fp}, evR (cF c.1 e (.seg r 15 i)) nx' false false (publicOf c) (Rcpt.bitsX 31 8) =
      Fp.ofNat (Seg.tt (Df c.1 e r) (BG c.1) i % 256) :=
    bitsX_seg (by decide) (fun j hj => gx_T hj) (Nat.mod_lt _ (by decide))
  have h39 : cF c.1 e (.seg r 15 i) (Rcpt.xb 39) = Fp.ofNat (Seg.tt (Df c.1 e r) (BG c.1) i / 256) := by
    rw [cF_xb (by decide), gx_39, bitOf_small (by rw [tt_div G]; exact c4_le G _)]
  intro x hx
  simp only [List.mem_append] at hx
  rcases hx with (hB' | hC') | hD'
  · simp only [gB, List.mem_cons, List.not_mem_nil, or_false] at hB'
    rcases hB' with rfl | rfl | rfl | rfl | rfl
    · simp only [Rcpt.gp, conv5_eq, dD, evR_mul, evR_sub, evR_add, evR_c, evR_smul, evR_sum_cons, evR_sum_nil,
        gp_one, gp_burnt, hB, gp_pE hh hi, gp_dlP (show 0 < 4 by decide), gp_dlP (show 1 < 4 by decide),
        gp_dlP (show 2 < 4 by decide), gp_dlP (show 3 < 4 by decide), gp_c2]
      have E := fp_eq (Nat.mod_add_div (Seg.sb (Df c.1 e r) (BG c.1) i) 256)
      have E2 := fp_eq (convG_row (Seg.pB (Df c.1 e r) (BG c.1)) i)
      simp only [Seg.sb, ofNat_add_e, ofNat_mul_e] at E E2
      simp only [Seg.sb, Seg.x2] at E ⊢
      simp only [natCast_eq]; grind
    · simp only [Rcpt.gp, evR_mul, evR_c, gp_one, cF_fs, gp_c2]
      by_cases h0 : i = 0
      · subst h0; simp only [↓reduceIte, chain, ofNat0]; grind
      · simp only [h0, ↓reduceIte]; grind
    · simp only [Rcpt.gp, evR_mul3, evR_not, evR_sub, evR_c, evR_n, gp_one, gp_fe, hB]
      by_cases h15 : i = 15
      · simp only [h15, ↓reduceIte]; grind
      · simp only [h15, ↓reduceIte, hn (by omega), gp_c2, sb_div G]; grind
    · simp only [Rcpt.gp, evR_mul3, evR_c, gp_one, gp_fe, hB]
      by_cases h15 : i = 15
      · subst h15; simp only [↓reduceIte, sb_div G, c2_final G, ofNat0]; grind
      · simp only [h15, ↓reduceIte]; grind
    · simp only [Rcpt.gp, Rcpt.ovf, dD, evR_mul3, evR_c, evR_smul, evR_sum_cons, evR_sum_nil, gp_one, gp_fe,
        gp_pE hh hi, gp_dlP (show 0 < 4 by decide), gp_dlP (show 1 < 4 by decide), gp_dlP (show 2 < 4 by decide)]
      by_cases h15 : i = 15
      · subst h15
        simp only [↓reduceIte, show 0 < 15 by decide, show 1 < 15 by decide, show 2 < 15 by decide,
          pB_hi G (show 12 ≤ 15 by decide), pB_hi G (show 12 ≤ 15 - 1 - 0 by decide),
          pB_hi G (show 12 ≤ 15 - 1 - 1 by decide), pB_hi G (show 12 ≤ 15 - 1 - 2 by decide), ofNat0]
        grind
      · simp only [h15, ↓reduceIte]; grind
  · simp only [gC, List.mem_cons, List.not_mem_nil, or_false] at hC'
    rcases hC' with rfl | rfl | rfl | rfl | rfl
    · simp only [Rcpt.gp, conv5_eq, dD, evR_mul, evR_sub, evR_add, evR_c, evR_smul, evR_sum_cons, evR_sum_nil,
        gp_one, gp_ramt, hR, gp_surE G, gp_dlS (show 0 < 4 by decide), gp_dlS (show 1 < 4 by decide),
        gp_dlS (show 2 < 4 by decide), gp_dlS (show 3 < 4 by decide), gp_c3]
      have E := fp_eq (Nat.mod_add_div (Seg.sr (Df c.1 e r) (BG c.1) i) 256)
      have E2 := fp_eq (convG_row (Seg.surB (Df c.1 e r) (BG c.1)) i)
      simp only [Seg.sr, ofNat_add_e, ofNat_mul_e] at E E2
      simp only [Seg.sr, Seg.x3] at E ⊢
      simp only [natCast_eq]; grind
    · simp only [Rcpt.gp, evR_mul, evR_c, gp_one, cF_fs, gp_c3]
      by_cases h0 : i = 0
      · subst h0; simp only [↓reduceIte, chain, ofNat0]; grind
      · simp only [h0, ↓reduceIte]; grind
    · simp only [Rcpt.gp, evR_mul3, evR_not, evR_sub, evR_c, evR_n, gp_one, gp_fe, hR]
      by_cases h15 : i = 15
      · simp only [h15, ↓reduceIte]; grind
      · simp only [h15, ↓reduceIte, hn (by omega), gp_c3, sr_div G]; grind
    · simp only [Rcpt.gp, evR_mul3, evR_c, gp_one, gp_fe, hR]
      by_cases h15 : i = 15
      · subst h15; simp only [↓reduceIte, sr_div G, c3_final G, ofNat0]; grind
      · simp only [h15, ↓reduceIte]; grind
    · simp only [Rcpt.gp, Rcpt.ovf, dD, evR_mul3, evR_c, evR_smul, evR_sum_cons, evR_sum_nil, gp_one, gp_fe,
        gp_surE G, gp_dlS (show 0 < 4 by decide), gp_dlS (show 1 < 4 by decide), gp_dlS (show 2 < 4 by decide)]
      by_cases h15 : i = 15
      · subst h15
        simp only [↓reduceIte, show 0 < 15 by decide, show 1 < 15 by decide, show 2 < 15 by decide,
          surB_hi G (show 12 ≤ 15 by decide) (by decide), surB_hi G (show 12 ≤ 15 - 1 - 0 by decide) (by decide),
          surB_hi G (show 12 ≤ 15 - 1 - 1 by decide) (by decide),
          surB_hi G (show 12 ≤ 15 - 1 - 2 by decide) (by decide), ofNat0]
        grind
      · simp only [h15, ↓reduceIte]; grind
  · simp only [gD, List.mem_cons, List.not_mem_nil, or_false] at hD'
    rcases hD' with rfl | rfl | rfl | rfl
    · simp only [Rcpt.gp, evR_mul, evR_sub, evR_add, evR_c, evR_smul, evR_sum_cons, evR_sum_nil, gp_one, hT, h39,
        gp_tok0, if_pos hi, gp_burnt, gp_c4]
      have E := fp_eq (Nat.mod_add_div (Seg.tt (Df c.1 e r) (BG c.1) i) 256)
      simp only [Seg.tt, Seg.x4, ofNat_add_e, ofNat_mul_e] at E
      simp only [Seg.tt, Seg.x4] at ⊢
      simp only [natCast_eq]; grind
    · simp only [Rcpt.gp, evR_mul, evR_c, gp_one, cF_fs, gp_c4]
      by_cases h0 : i = 0
      · subst h0; simp only [↓reduceIte, chain, ofNat0]; grind
      · simp only [h0, ↓reduceIte]; grind
    · simp only [Rcpt.gp, evR_mul3, evR_not, evR_sub, evR_c, evR_n, gp_one, gp_fe, h39]
      by_cases h15 : i = 15
      · simp only [h15, ↓reduceIte]; grind
      · simp only [h15, ↓reduceIte, hn (by omega), gp_c4, tt_div G]; grind
    · simp only [Rcpt.gp, evR_mul3, evR_c, gp_one, gp_fe, h39]
      by_cases h15 : i = 15
      · subst h15; simp only [↓reduceIte, tt_div G, c4_final G, ofNat0]; grind
      · simp only [h15, ↓reduceIte]; grind

end

set_option maxRecDepth 100000 in
theorem gas_zr : Rcpt.cGas.all (Zr (fun x => x == Rcpt.sGP) (fun _ => false) false) = true := by decide

/-- **`cGas` on the honest rows.** -/
theorem gasFam : FamOk Rcpt.cGas := by
  intro c e hg _
  have zr : ∀ x ∈ Rcpt.cGas, Zr (fun x => x == Rcpt.sGP) (fun _ => false) false x = true :=
    fun x hx => List.all_eq_true.1 gas_zr x hx
  have zrP : ∀ x ∈ Rcpt.cGas, Zr (fun _ => true) (fun _ => false) true x = true :=
    fun x hx => Zr_mono (fun _ _ => rfl) (fun _ h => h) (fun h => by cases h) (zr x hx)
  have nonGP : ∀ ρ : RRec, Cc c.1 e ρ Rcpt.sGP = 0 → ∀ {nx : Nat → Fp} {fst : Bool}, ∀ x ∈ Rcpt.cGas,
      evR (cF c.1 e ρ) nx fst false (publicOf c) x = 0 := by
    intro ρ h0 nx fst x hx
    exact Zr_sound (z := fun x => x == Rcpt.sGP) (zn := fun _ => false) (f0 := false)
      (fun y hy => by simp only [beq_iff_eq] at hy; subst hy; simp only [cF, h0]; rfl)
      (fun _ h => by cases h) (fun h => by cases h) x (zr x hx)
  have gpRow : ∀ r i, r < NN e → i < 16 → ∀ {nx : Nat → Fp}, (i < 15 → nx = cF c.1 e (.seg r 15 (i + 1))) →
      ∀ x ∈ Rcpt.cGas, evR (cF c.1 e (.seg r 15 i)) nx false false (publicOf c) x = 0 := by
    intro r i hr hi nx hn x hx
    rw [cGas_eq] at hx
    simp only [List.mem_append] at hx
    rcases hx with ((((h | h) | h) | h) | h) | h
    · exact gp_AEF hg hr hi hn x (by simp [h])
    · exact gp_BCD hg hr hi hn x (by simp [h])
    · exact gp_BCD hg hr hi hn x (by simp [h])
    · exact gp_BCD hg hr hi hn x (by simp [h])
    · exact gp_AEF hg hr hi hn x (by simp [h])
    · exact gp_AEF hg hr hi hn x (by simp [h])
  have seg0 : ∀ r s i, s ≠ 15 → Cc c.1 e (.seg r s i) Rcpt.sGP = 0 := by
    intro r s i h; rw [S_sGP]; simp [Ne.symm h]
  apply fam_of hg
  · intro i hi; exact nonGP _ (L_sGP _ _ _)
  · intro r s i hr hs hin
    by_cases h15 : s = 15
    · subst h15
      have : fLen (Df c.1 e r) 15 = 16 := rfl
      exact gpRow r i hr (by omega) (fun _ => rfl)
    · exact nonGP _ (seg0 r s i h15)
  · intro r s i hr hs hfe _
    by_cases h15 : s = 15
    · subst h15
      have : fLen (Df c.1 e r) 15 = 16 := rfl
      exact gpRow r i hr (by omega) (fun h => by omega)
    · exact nonGP _ (seg0 r s i h15)
  · intro r s i hr hs hfe hrl
    have : s ≠ 15 := by intro h; subst h; simp [isRl] at hrl
    exact nonGP _ (seg0 r s i this)
  · obtain ⟨r, s, i, he, -, -, -, -, h2326⟩ := lastRec_facts hg
    rw [he]; exact nonGP _ (seg0 r s i (by omega))
  · exact fun x hx => zr_pad (zn := fun _ => false) (fun _ h => by cases h) (zrP x hx)
  · exact fun x hx => zr_pad (zn := fun _ => false) (fun _ h => by cases h) (zrP x hx)

end RcptP

end ZkFormal.Near.Render
