import ZkFormal.Near.Render.Proof.RcptDep2

/-!
# ZkFormal.Near.Render.Proof.RcptDep3 — `cDep`: storage bound, `tprev`, delay line; `depFam : FamOk cDep`
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false

namespace RcptP

open RcptGen

section
variable {c : WfClaim} {e : Ext} {r i : Nat}

/-- **`pE`, `pF` on a `DEP` row.** -/
theorem dp_EF (hg : Good c.1 e) (hr : r < NN e) (hi : i < 16) {nx : Nat → Fp}
    (hn : i < 15 → nx = cF c.1 e (.seg r 17 (i + 1))) :
    ∀ x ∈ pE ++ pF, evR (cF c.1 e (.seg r 17 i)) nx false false (publicOf c) x = 0 := by
  have D := depOk hg hr
  intro x hx
  simp only [List.mem_append] at hx
  rcases hx with hE | hF
  · simp only [pE, List.mem_cons, List.not_mem_nil, or_false] at hE
    rcases hE with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Rcpt.dp, evR_mul, evR_not, evR_c, dp_one]; grind
    · simp only [Rcpt.dp, evR_mul3, evR_c, dp_one, cF_fs, dp_r1]
      by_cases h0 : i = 0
      · subst h0; simp only [↓reduceIte, Nat.zero_ne_one]; grind
      · simp only [h0, ↓reduceIte]; grind
    · simp only [Rcpt.dp, evR_mul3, evR_not, evR_sub, evR_c, evR_n, dp_one, dp_fe, cF_fs]
      by_cases h15 : i = 15
      · simp only [h15, ↓reduceIte]; grind
      · rw [hn (by omega), dp_r1]
        by_cases h0 : i = 0
        · subst h0; simp only [↓reduceIte, Nat.zero_add]; grind
        · simp only [h0, h15, ↓reduceIte, show i + 1 ≠ 1 by omega]; grind
    · simp only [evR_mul3, evR_not, evR_sub, evR_k, evR_c, evR_sum_cons, evR_sum_nil, evR_smul, dp_r1, cF_big]
      by_cases h1 : i = 1
      · subst h1
        cases hb : (Df c.1 e r).big
        · rw [bitsX_seg (X := 770 - (Seg.stB (Df c.1 e r) 0 + 256 * Seg.stB (Df c.1 e r) 1)) (by decide)
            (fun j hj => by rw [dx_F hj, if_pos ⟨rfl, hb⟩])
            (by have := stor_small D hb; have := D.stake hb; omega)]
          rw [dp_dl (show 0 < 7 by decide), dp_st]
          have := stor_small D hb; have := D.stake hb
          simp only [show 0 < 1 by decide, ↓reduceIte, Nat.sub_zero, b2n_false, ofNat0,
            ofNat_sub (show Seg.stB (Df c.1 e r) 0 + 256 * Seg.stB (Df c.1 e r) 1 ≤ 770 by omega), ofNat_add_e,
            ofNat_mul_e, natCast_eq]
          grind
        · simp only [b2n_true, ofNat1]; grind
      · simp only [h1, ↓reduceIte]; grind
    · simp only [Rcpt.dp, evR_mul3, evR_not, evR_sub, evR_c, dp_one, cF_fs, dp_r1, cF_big, dp_st]
      cases hb : (Df c.1 e r).big
      · by_cases h0 : i = 0
        · subst h0; simp only [↓reduceIte]; grind
        · by_cases h1 : i = 1
          · subst h1; simp only [↓reduceIte, Nat.one_ne_zero]; grind
          · rw [stB_small D hb (by omega)]; simp only [ofNat0]; grind
      · simp only [b2n_true, ofNat1]; grind
    · simp only [Rcpt.dp, evR_mul3, evR_sub, evR_c, dp_one, cF_fs]
      by_cases h0 : i = 0
      · subst h0
        rw [bitsX_seg (X := (Df c.1 e r).r - (Df c.1 e r).tprev) (by decide)
          (fun j hj => by rw [dx_G hj, if_pos rfl]) (by have := D.r_lt; omega)]
        simp only [cF, S_r, S_tprev, ↓reduceIte, ofNat_sub D.tprev_le]; grind
      · simp only [h0, ↓reduceIte]; grind
  · simp only [pF, List.mem_append, List.mem_map, List.mem_range] at hF
    rcases hF with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · simp only [Rcpt.dp, dD, evR_mul3, evR_c, dp_one, cF_fs, dp_dl (show j < 7 by omega)]
      by_cases h0 : i = 0
      · subst h0; simp only [↓reduceIte, Nat.not_lt_zero, ofNat0]; grind
      · simp only [h0, ↓reduceIte]; grind
    · simp only [Rcpt.dp, dD, evR_mul3, evR_not, evR_sub, evR_c, evR_n, dp_one, dp_fe]
      by_cases h15 : i = 15
      · simp only [h15, ↓reduceIte]; grind
      · rw [hn (by omega), dp_dl (show j + 1 < 7 by omega), dp_dl (show j < 7 by omega)]
        have : (if j + 1 < i + 1 then Seg.stB (Df c.1 e r) (i + 1 - 1 - (j + 1)) else 0) =
            (if j < i then Seg.stB (Df c.1 e r) (i - 1 - j) else 0) := by
          by_cases hj' : j < i
          · rw [if_pos (by omega), if_pos hj', show i + 1 - 1 - (j + 1) = i - 1 - j by omega]
          · rw [if_neg (by omega), if_neg hj']
        rw [this]; simp only [h15, ↓reduceIte]; grind

end

set_option maxRecDepth 100000 in
theorem dep_zr : Rcpt.cDep.all (Zr (fun x => x == Rcpt.sDEP || x == Rcpt.r1 || x == Rcpt.st) (fun _ => false) false) = true := by
  decide

/-- **`cDep` on the honest rows.** -/
theorem depFam : FamOk Rcpt.cDep := by
  intro c e hg _
  have zr : ∀ x ∈ Rcpt.cDep, Zr (fun x => x == Rcpt.sDEP || x == Rcpt.r1 || x == Rcpt.st) (fun _ => false) false x = true :=
    fun x hx => List.all_eq_true.1 dep_zr x hx
  have zrP : ∀ x ∈ Rcpt.cDep, Zr (fun _ => true) (fun _ => false) true x = true :=
    fun x hx => Zr_mono (fun _ _ => rfl) (fun _ h => h) (fun h => by cases h) (zr x hx)
  have nonDEP : ∀ ρ : RRec, Cc c.1 e ρ Rcpt.sDEP = 0 → Cc c.1 e ρ Rcpt.r1 = 0 → Cc c.1 e ρ Rcpt.st = 0 →
      ∀ {nx : Nat → Fp} {fst : Bool}, ∀ x ∈ Rcpt.cDep, evR (cF c.1 e ρ) nx fst false (publicOf c) x = 0 := by
    intro ρ h0 h1 h2 nx fst x hx
    exact Zr_sound (z := fun x => x == Rcpt.sDEP || x == Rcpt.r1 || x == Rcpt.st) (zn := fun _ => false) (f0 := false)
      (fun y hy => by
        simp only [Bool.or_eq_true, beq_iff_eq] at hy
        rcases hy with (rfl | rfl) | rfl <;> simp only [cF, h0, h1, h2] <;> rfl)
      (fun _ h => by cases h) (fun h => by cases h) x (zr x hx)
  have depRow : ∀ r i, r < NN e → i < 16 → ∀ {nx : Nat → Fp}, (i < 15 → nx = cF c.1 e (.seg r 17 (i + 1))) →
      ∀ x ∈ Rcpt.cDep, evR (cF c.1 e (.seg r 17 i)) nx false false (publicOf c) x = 0 := by
    intro r i hr hi nx hn x hx
    rw [cDep_eq] at hx
    simp only [List.mem_append] at hx
    rcases hx with ((((h | h) | h) | h) | h) | h
    · exact dp_ABCD hg hr hi hn x (by simp [h])
    · exact dp_ABCD hg hr hi hn x (by simp [h])
    · exact dp_ABCD hg hr hi hn x (by simp [h])
    · exact dp_ABCD hg hr hi hn x (by simp [h])
    · exact dp_EF hg hr hi hn x (by simp [h])
    · exact dp_EF hg hr hi hn x (by simp [h])
  have seg0 : ∀ r s i, s ≠ 17 → ∀ {nx : Nat → Fp} {fst : Bool}, ∀ x ∈ Rcpt.cDep,
      evR (cF c.1 e (.seg r s i)) nx fst false (publicOf c) x = 0 := by
    intro r s i h
    refine nonDEP _ ?_ ?_ ?_
    · rw [S_sDEP]; simp [Ne.symm h]
    · rw [S_r1]; simp [h, b2n]
    · rw [S_st]; by_cases h15 : s = 15 <;> simp [h, h15]
  apply fam_of hg
  · intro i hi; exact nonDEP _ (L_sDEP _ _ _) (L_r1 _ _ _) (L_st _ _ _)
  · intro r s i hr hs hin
    by_cases h17 : s = 17
    · subst h17
      have : fLen (Df c.1 e r) 17 = 16 := rfl
      exact depRow r i hr (by omega) (fun _ => rfl)
    · exact seg0 r s i h17
  · intro r s i hr hs hfe _
    by_cases h17 : s = 17
    · subst h17
      have : fLen (Df c.1 e r) 17 = 16 := rfl
      exact depRow r i hr (by omega) (fun h => by omega)
    · exact seg0 r s i h17
  · intro r s i hr hs hfe hrl
    have : s ≠ 17 := by intro h; subst h; simp [isRl] at hrl
    exact seg0 r s i this
  · obtain ⟨r, s, i, he, -, -, -, -, h2326⟩ := lastRec_facts hg
    rw [he]; exact seg0 r s i (by omega)
  · exact fun x hx => zr_pad (zn := fun _ => false) (fun _ h => by cases h) (zrP x hx)
  · exact fun x hx => zr_pad (zn := fun _ => false) (fun _ h => by cases h) (zrP x hx)

end RcptP

end ZkFormal.Near.Render
