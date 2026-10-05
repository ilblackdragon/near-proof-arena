import ZkFormal.Near.Render.Proof.RcptCol

/-!
# ZkFormal.Near.Render.Proof.RcptKey — the key-symbol constraints (`cKey`) on the honest rows
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

/-- The key columns. -/
def keyZ (x : Nat) : Bool := x ∈ [7, 8, 9, 43, 44, 45, 46, 47]

theorem key_zr : Rcpt.cKey.all (Zr keyZ (fun _ => false) false) = true := by decide
theorem key_zrP : Rcpt.cKey.all (Zr (fun _ => true) (fun _ => false) true) = true := by decide

section
variable {c : Claim} {e : Ext}

theorem key_cl (i : Nat) : ∀ x, keyZ x = true → Cc c e (.cl i) x = 0 := by
  intro x hx
  simp only [keyZ, List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [Cc_cl, clCell]

theorem key_seg {r s i : Nat} (h7 : s ≠ 7) (h8 : s ≠ 8) (h9 : s ≠ 9) :
    ∀ x, keyZ x = true → Cc c e (.seg r s i) x = 0 := by
  intro x hx
  simp only [keyZ, List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [Cc_seg, segCell, h7, h8, h9, Ne.symm h7, Ne.symm h8, Ne.symm h9, b2n]

theorem key_rows {pub : List Fp} {r s i : Nat} (hs : s = 7 ∨ s = 8 ∨ s = 9) {ρ' : RRec}
    (hn : ρ' = nextOf (Df c e) (.seg r s i)) (hi : i < fLen (Df c e r) s)
    (hV : s = 8 → (Df c e r).recv.getD i 0 < 256 ∧ vch ((Df c e r).recv.getD i 0) = true) :
    ∀ x ∈ Rcpt.cKey, evR (cF c e (.seg r s i)) (cF c e ρ') false false pub x = 0 := by
  intro x hx
  subst hn
  simp only [Rcpt.cKey, List.mem_cons, List.not_mem_nil, or_false] at hx
  have hb : s = 8 → segByte (Df c e r) (PA c e) s i / 16 = 2 * charCell (segByte (Df c e r) (PA c e) s i) 111 +
      3 * charCell (segByte (Df c e r) (PA c e) s i) 112 + 5 * charCell (segByte (Df c e r) (PA c e) s i) 113 +
      6 * charCell (segByte (Df c e r) (PA c e) s i) 114 + 7 * charCell (segByte (Df c e r) (PA c e) s i) 115 := by
    rintro rfl
    have := hV rfl
    simp only [segByte, isStr, strOf, List.contains, List.elem, Nat.reduceBEq, Nat.reduceEqDiff, ↓reduceIte,
      Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or, Bool.false_eq_true]
    exact hi_char _ this.1 this.2
  rcases (show i + 1 < fLen (Df c e r) s ∨ i + 1 = fLen (Df c e r) s by omega) with hfe | hfe
  · rw [nextOf_in hfe]
    rcases hs with rfl | rfl | rfl <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [evR_sub, evR_c, evR_n, evR_sum_cons, evR_sum_nil, evR_mul, evR_mul3, evR_add, evR_k,
      evR_smul, evR_not, cF, ZkFormal.Near.Render.RcptP.b2n_true, ZkFormal.Near.Render.RcptP.b2n_false, ZkFormal.Near.Render.RcptP.S_act, ZkFormal.Near.Render.RcptP.S_rf, ZkFormal.Near.Render.RcptP.S_rl, ZkFormal.Near.Render.RcptP.S_lastR, ZkFormal.Near.Render.RcptP.S_sCL, ZkFormal.Near.Render.RcptP.S_sPL, ZkFormal.Near.Render.RcptP.S_sP, ZkFormal.Near.Render.RcptP.S_sVL, ZkFormal.Near.Render.RcptP.S_sV, ZkFormal.Near.Render.RcptP.S_sRID, ZkFormal.Near.Render.RcptP.S_sT0, ZkFormal.Near.Render.RcptP.S_sSL, ZkFormal.Near.Render.RcptP.S_sS, ZkFormal.Near.Render.RcptP.S_sKT, ZkFormal.Near.Render.RcptP.S_sPK, ZkFormal.Near.Render.RcptP.S_sGP, ZkFormal.Near.Render.RcptP.S_sTL, ZkFormal.Near.Render.RcptP.S_sDEP, ZkFormal.Near.Render.RcptP.S_sXP0, ZkFormal.Near.Render.RcptP.S_sXRI, ZkFormal.Near.Render.RcptP.S_sXG, ZkFormal.Near.Render.RcptP.S_sXST, ZkFormal.Near.Render.RcptP.S_sXL0, ZkFormal.Near.Render.RcptP.S_sXLH, ZkFormal.Near.Render.RcptP.S_sXRH, ZkFormal.Near.Render.RcptP.S_sXRF, ZkFormal.Near.Render.RcptP.S_sXRZ, ZkFormal.Near.Render.RcptP.S_idx, ZkFormal.Near.Render.RcptP.S_fs, ZkFormal.Near.Render.RcptP.S_fe, ZkFormal.Near.Render.RcptP.S_b, ZkFormal.Near.Render.RcptP.S_tA, ZkFormal.Near.Render.RcptP.S_symA, ZkFormal.Near.Render.RcptP.S_lastA, ZkFormal.Near.Render.RcptP.S_gKA, ZkFormal.Near.Render.RcptP.S_kz, ZkFormal.Near.Render.RcptP.S_r, ZkFormal.Near.Render.RcptP.S_o, ZkFormal.Near.Render.RcptP.S_o2, ZkFormal.Near.Render.RcptP.S_Lp, ZkFormal.Near.Render.RcptP.S_Lv, ZkFormal.Near.Render.RcptP.S_Ls, ZkFormal.Near.Render.RcptP.S_kt, ZkFormal.Near.Render.RcptP.S_hr, ZkFormal.Near.Render.RcptP.S_kslot, ZkFormal.Near.Render.RcptP.S_tprev, ZkFormal.Near.Render.RcptP.S_rcnt, ZkFormal.Near.Render.RcptP.S_ge, ZkFormal.Near.Render.RcptP.S_big, ZkFormal.Near.Render.RcptP.S_oEnd, ZkFormal.Near.Render.RcptP.S_o2End, ZkFormal.Near.Render.RcptP.S_h2, ZkFormal.Near.Render.RcptP.S_h3, ZkFormal.Near.Render.RcptP.S_h5, ZkFormal.Near.Render.RcptP.S_h6, ZkFormal.Near.Render.RcptP.S_h7, ZkFormal.Near.Render.RcptP.S_z, ZkFormal.Near.Render.RcptP.S_linv, ZkFormal.Near.Render.RcptP.S_l210, ZkFormal.Near.Render.RcptP.S_hx6, ZkFormal.Near.Render.RcptP.S_acc, ZkFormal.Near.Render.RcptP.S_vc0, ZkFormal.Near.Render.RcptP.S_vc1, ZkFormal.Near.Render.RcptP.S_h01, ZkFormal.Near.Render.RcptP.S_p1, ZkFormal.Near.Render.RcptP.S_p2, ZkFormal.Near.Render.RcptP.S_p3, ZkFormal.Near.Render.RcptP.S_i1, ZkFormal.Near.Render.RcptP.S_i2, ZkFormal.Near.Render.RcptP.S_i3, ZkFormal.Near.Render.RcptP.S_isys, ZkFormal.Near.Render.RcptP.S_r1, ZkFormal.Near.Render.RcptP.S_lo8, ZkFormal.Near.Render.RcptP.S_lo4, ZkFormal.Near.Render.RcptP.S_c1, ZkFormal.Near.Render.RcptP.S_c2, ZkFormal.Near.Render.RcptP.S_c3, ZkFormal.Near.Render.RcptP.S_c4, ZkFormal.Near.Render.RcptP.S_burnt, ZkFormal.Near.Render.RcptP.S_ramt, ZkFormal.Near.Render.RcptP.S_sumD, ZkFormal.Near.Render.RcptP.S_invA, ZkFormal.Near.Render.RcptP.S_bef, ZkFormal.Near.Render.RcptP.S_lk, ZkFormal.Near.Render.RcptP.S_st, ZkFormal.Near.Render.RcptP.S_dsum, ZkFormal.Near.Render.RcptP.S_invB, ZkFormal.Near.Render.RcptP.S_dI, ZkFormal.Near.Render.RcptP.S_dL, ZkFormal.Near.Render.RcptP.S_gDg, ZkFormal.Near.Render.RcptP.S_reg, ZkFormal.Near.Render.RcptP.S_tok, ZkFormal.Near.Render.RcptP.S_xb, ZkFormal.Near.Render.RcptP.S_lb, ZkFormal.Near.Render.RcptP.S_dl, Rcpt.hiE, Nat.reduceEqDiff, ↓reduceIte, decide_true, decide_false, true_and,
      false_and, and_true, and_false, true_or, false_or, or_true, or_false, ofNat0, ofNat1, isStr, Nat.reduceBEq,
      Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or, Bool.false_eq_true] <;>
    (try rw [hb rfl]) <;> rfin
  · rcases hs with rfl | rfl | rfl <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [evR_sub, evR_c, evR_n, evR_sum_cons, evR_sum_nil, evR_mul, evR_mul3, evR_add, evR_k,
      evR_smul, evR_not, cF, ZkFormal.Near.Render.RcptP.b2n_true, ZkFormal.Near.Render.RcptP.b2n_false, ZkFormal.Near.Render.RcptP.S_act, ZkFormal.Near.Render.RcptP.S_rf, ZkFormal.Near.Render.RcptP.S_rl, ZkFormal.Near.Render.RcptP.S_lastR, ZkFormal.Near.Render.RcptP.S_sCL, ZkFormal.Near.Render.RcptP.S_sPL, ZkFormal.Near.Render.RcptP.S_sP, ZkFormal.Near.Render.RcptP.S_sVL, ZkFormal.Near.Render.RcptP.S_sV, ZkFormal.Near.Render.RcptP.S_sRID, ZkFormal.Near.Render.RcptP.S_sT0, ZkFormal.Near.Render.RcptP.S_sSL, ZkFormal.Near.Render.RcptP.S_sS, ZkFormal.Near.Render.RcptP.S_sKT, ZkFormal.Near.Render.RcptP.S_sPK, ZkFormal.Near.Render.RcptP.S_sGP, ZkFormal.Near.Render.RcptP.S_sTL, ZkFormal.Near.Render.RcptP.S_sDEP, ZkFormal.Near.Render.RcptP.S_sXP0, ZkFormal.Near.Render.RcptP.S_sXRI, ZkFormal.Near.Render.RcptP.S_sXG, ZkFormal.Near.Render.RcptP.S_sXST, ZkFormal.Near.Render.RcptP.S_sXL0, ZkFormal.Near.Render.RcptP.S_sXLH, ZkFormal.Near.Render.RcptP.S_sXRH, ZkFormal.Near.Render.RcptP.S_sXRF, ZkFormal.Near.Render.RcptP.S_sXRZ, ZkFormal.Near.Render.RcptP.S_idx, ZkFormal.Near.Render.RcptP.S_fs, ZkFormal.Near.Render.RcptP.S_fe, ZkFormal.Near.Render.RcptP.S_b, ZkFormal.Near.Render.RcptP.S_tA, ZkFormal.Near.Render.RcptP.S_symA, ZkFormal.Near.Render.RcptP.S_lastA, ZkFormal.Near.Render.RcptP.S_gKA, ZkFormal.Near.Render.RcptP.S_kz, ZkFormal.Near.Render.RcptP.S_r, ZkFormal.Near.Render.RcptP.S_o, ZkFormal.Near.Render.RcptP.S_o2, ZkFormal.Near.Render.RcptP.S_Lp, ZkFormal.Near.Render.RcptP.S_Lv, ZkFormal.Near.Render.RcptP.S_Ls, ZkFormal.Near.Render.RcptP.S_kt, ZkFormal.Near.Render.RcptP.S_hr, ZkFormal.Near.Render.RcptP.S_kslot, ZkFormal.Near.Render.RcptP.S_tprev, ZkFormal.Near.Render.RcptP.S_rcnt, ZkFormal.Near.Render.RcptP.S_ge, ZkFormal.Near.Render.RcptP.S_big, ZkFormal.Near.Render.RcptP.S_oEnd, ZkFormal.Near.Render.RcptP.S_o2End, ZkFormal.Near.Render.RcptP.S_h2, ZkFormal.Near.Render.RcptP.S_h3, ZkFormal.Near.Render.RcptP.S_h5, ZkFormal.Near.Render.RcptP.S_h6, ZkFormal.Near.Render.RcptP.S_h7, ZkFormal.Near.Render.RcptP.S_z, ZkFormal.Near.Render.RcptP.S_linv, ZkFormal.Near.Render.RcptP.S_l210, ZkFormal.Near.Render.RcptP.S_hx6, ZkFormal.Near.Render.RcptP.S_acc, ZkFormal.Near.Render.RcptP.S_vc0, ZkFormal.Near.Render.RcptP.S_vc1, ZkFormal.Near.Render.RcptP.S_h01, ZkFormal.Near.Render.RcptP.S_p1, ZkFormal.Near.Render.RcptP.S_p2, ZkFormal.Near.Render.RcptP.S_p3, ZkFormal.Near.Render.RcptP.S_i1, ZkFormal.Near.Render.RcptP.S_i2, ZkFormal.Near.Render.RcptP.S_i3, ZkFormal.Near.Render.RcptP.S_isys, ZkFormal.Near.Render.RcptP.S_r1, ZkFormal.Near.Render.RcptP.S_lo8, ZkFormal.Near.Render.RcptP.S_lo4, ZkFormal.Near.Render.RcptP.S_c1, ZkFormal.Near.Render.RcptP.S_c2, ZkFormal.Near.Render.RcptP.S_c3, ZkFormal.Near.Render.RcptP.S_c4, ZkFormal.Near.Render.RcptP.S_burnt, ZkFormal.Near.Render.RcptP.S_ramt, ZkFormal.Near.Render.RcptP.S_sumD, ZkFormal.Near.Render.RcptP.S_invA, ZkFormal.Near.Render.RcptP.S_bef, ZkFormal.Near.Render.RcptP.S_lk, ZkFormal.Near.Render.RcptP.S_st, ZkFormal.Near.Render.RcptP.S_dsum, ZkFormal.Near.Render.RcptP.S_invB, ZkFormal.Near.Render.RcptP.S_dI, ZkFormal.Near.Render.RcptP.S_dL, ZkFormal.Near.Render.RcptP.S_gDg, ZkFormal.Near.Render.RcptP.S_reg, ZkFormal.Near.Render.RcptP.S_tok, ZkFormal.Near.Render.RcptP.S_xb, ZkFormal.Near.Render.RcptP.S_lb, ZkFormal.Near.Render.RcptP.S_dl, Rcpt.hiE, Nat.reduceEqDiff, ↓reduceIte, decide_true, decide_false, true_and,
      false_and, and_true, and_false, true_or, false_or, or_true, or_false, ofNat0, ofNat1, isStr, Nat.reduceBEq,
      Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or, Bool.false_eq_true, hfe] <;>
    (try rw [hb rfl]) <;> rfin

/-- **`cKey` on the honest rows.** -/
theorem key_ok (hg : Good c e) (hV : ∀ r, r < NN e → ∀ i, i < (Df c e r).recv.length →
      (Df c e r).recv.getD i 0 < 256 ∧ vch ((Df c e r).recv.getD i 0) = true) {pub : List Fp} :
    ∀ x ∈ Rcpt.cKey, ∀ q, q < (render c e).height T_RCPT → x.eval (render c e) T_RCPT q pub = 0 := by
  intro x hx
  apply allRows_of hg
  · intro ρ hρ _ _
    have hok := RL_ok hg ρ hρ
    cases ρ with
    | cl i =>
      have hz := List.all_eq_true.1 key_zr x hx
      exact zr_rec (f0 := false) (key_cl i) (zn := fun _ => false) (fun _ h => by cases h) (fun h => by cases h) hz
    | seg r s i =>
      obtain ⟨hr, -, hi⟩ := hok
      by_cases h : s = 7 ∨ s = 8 ∨ s = 9
      · rw [seg_ne_cl]
        exact key_rows h rfl hi (fun h8 => by subst h8; exact hV r hr i (by simpa [fLen] using hi)) x hx
      · exact zr_rec (f0 := false) (key_seg (fun h' => h (.inl h')) (fun h' => h (.inr (.inl h'))) (fun h' => h (.inr (.inr h'))))
          (zn := fun _ => false) (fun _ h => by cases h) (fun h => by cases h) (List.all_eq_true.1 key_zr x hx)
  · obtain ⟨r, s, i, he, hs⟩ := lastRec_eq c e
    rw [he]
    exact zr_last (f0 := false) (key_seg (by omega) (by omega) (by omega)) (fun h => by cases h)
      (Zr_mono_n (fun _ _ => rfl) (List.all_eq_true.1 key_zr x hx))
  · exact zr_pad (zn := fun _ => false) (fun _ h => by cases h) (List.all_eq_true.1 key_zrP x hx)
  · exact zr_pad (zn := fun _ => false) (fun _ h => by cases h) (List.all_eq_true.1 key_zrP x hx)

end

end RcptP

end ZkFormal.Near.Render
