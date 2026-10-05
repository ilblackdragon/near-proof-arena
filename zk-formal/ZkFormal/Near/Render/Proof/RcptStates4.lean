import ZkFormal.Near.Render.Proof.RcptStates3

/-!
# ZkFormal.Near.Render.Proof.RcptStates4 — boundary constraints (`sG`) at a field's last row
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

macro "sgsimp" : tactic => `(tactic| (try simp only [evR_mul, evR_mul3, evR_sub, evR_add, evR_not, evR_c, evR_n, evR_k,
    evR_smul, evR_sum_cons, evR_sum_nil, evR_isFirst, evR_isLast, evR_isTransition, Rcpt.rowE, Rcpt.varE, cF, ZkFormal.Near.Render.RcptP.b2n_true, ZkFormal.Near.Render.RcptP.b2n_false, ZkFormal.Near.Render.RcptP.S_act, ZkFormal.Near.Render.RcptP.S_rf, ZkFormal.Near.Render.RcptP.S_rl, ZkFormal.Near.Render.RcptP.S_lastR, ZkFormal.Near.Render.RcptP.S_sCL, ZkFormal.Near.Render.RcptP.S_sPL, ZkFormal.Near.Render.RcptP.S_sP, ZkFormal.Near.Render.RcptP.S_sVL, ZkFormal.Near.Render.RcptP.S_sV, ZkFormal.Near.Render.RcptP.S_sRID, ZkFormal.Near.Render.RcptP.S_sT0, ZkFormal.Near.Render.RcptP.S_sSL, ZkFormal.Near.Render.RcptP.S_sS, ZkFormal.Near.Render.RcptP.S_sKT, ZkFormal.Near.Render.RcptP.S_sPK, ZkFormal.Near.Render.RcptP.S_sGP, ZkFormal.Near.Render.RcptP.S_sTL, ZkFormal.Near.Render.RcptP.S_sDEP, ZkFormal.Near.Render.RcptP.S_sXP0, ZkFormal.Near.Render.RcptP.S_sXRI, ZkFormal.Near.Render.RcptP.S_sXG, ZkFormal.Near.Render.RcptP.S_sXST, ZkFormal.Near.Render.RcptP.S_sXL0, ZkFormal.Near.Render.RcptP.S_sXLH, ZkFormal.Near.Render.RcptP.S_sXRH, ZkFormal.Near.Render.RcptP.S_sXRF, ZkFormal.Near.Render.RcptP.S_sXRZ, ZkFormal.Near.Render.RcptP.S_idx, ZkFormal.Near.Render.RcptP.S_fs, ZkFormal.Near.Render.RcptP.S_fe, ZkFormal.Near.Render.RcptP.S_b, ZkFormal.Near.Render.RcptP.S_tA, ZkFormal.Near.Render.RcptP.S_symA, ZkFormal.Near.Render.RcptP.S_lastA, ZkFormal.Near.Render.RcptP.S_gKA, ZkFormal.Near.Render.RcptP.S_kz, ZkFormal.Near.Render.RcptP.S_r, ZkFormal.Near.Render.RcptP.S_o, ZkFormal.Near.Render.RcptP.S_o2, ZkFormal.Near.Render.RcptP.S_Lp, ZkFormal.Near.Render.RcptP.S_Lv, ZkFormal.Near.Render.RcptP.S_Ls, ZkFormal.Near.Render.RcptP.S_kt, ZkFormal.Near.Render.RcptP.S_hr, ZkFormal.Near.Render.RcptP.S_kslot, ZkFormal.Near.Render.RcptP.S_tprev, ZkFormal.Near.Render.RcptP.S_rcnt, ZkFormal.Near.Render.RcptP.S_ge, ZkFormal.Near.Render.RcptP.S_big, ZkFormal.Near.Render.RcptP.S_oEnd, ZkFormal.Near.Render.RcptP.S_o2End, ZkFormal.Near.Render.RcptP.S_h2, ZkFormal.Near.Render.RcptP.S_h3, ZkFormal.Near.Render.RcptP.S_h5, ZkFormal.Near.Render.RcptP.S_h6, ZkFormal.Near.Render.RcptP.S_h7, ZkFormal.Near.Render.RcptP.S_z, ZkFormal.Near.Render.RcptP.S_linv, ZkFormal.Near.Render.RcptP.S_l210, ZkFormal.Near.Render.RcptP.S_hx6, ZkFormal.Near.Render.RcptP.S_acc, ZkFormal.Near.Render.RcptP.S_vc0, ZkFormal.Near.Render.RcptP.S_vc1, ZkFormal.Near.Render.RcptP.S_h01, ZkFormal.Near.Render.RcptP.S_p1, ZkFormal.Near.Render.RcptP.S_p2, ZkFormal.Near.Render.RcptP.S_p3, ZkFormal.Near.Render.RcptP.S_i1, ZkFormal.Near.Render.RcptP.S_i2, ZkFormal.Near.Render.RcptP.S_i3, ZkFormal.Near.Render.RcptP.S_isys, ZkFormal.Near.Render.RcptP.S_r1, ZkFormal.Near.Render.RcptP.S_lo8, ZkFormal.Near.Render.RcptP.S_lo4, ZkFormal.Near.Render.RcptP.S_c1, ZkFormal.Near.Render.RcptP.S_c2, ZkFormal.Near.Render.RcptP.S_c3, ZkFormal.Near.Render.RcptP.S_c4, ZkFormal.Near.Render.RcptP.S_burnt, ZkFormal.Near.Render.RcptP.S_ramt, ZkFormal.Near.Render.RcptP.S_sumD, ZkFormal.Near.Render.RcptP.S_invA, ZkFormal.Near.Render.RcptP.S_bef, ZkFormal.Near.Render.RcptP.S_lk, ZkFormal.Near.Render.RcptP.S_st, ZkFormal.Near.Render.RcptP.S_dsum, ZkFormal.Near.Render.RcptP.S_invB, ZkFormal.Near.Render.RcptP.S_dI, ZkFormal.Near.Render.RcptP.S_dL, ZkFormal.Near.Render.RcptP.S_gDg, ZkFormal.Near.Render.RcptP.S_reg, ZkFormal.Near.Render.RcptP.S_tok, ZkFormal.Near.Render.RcptP.S_xb, ZkFormal.Near.Render.RcptP.S_lb, ZkFormal.Near.Render.RcptP.S_dl,
    Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, b2n_false, b2n_true, Bool.false_eq_true,
    ↓reduceIte, ofNat0, ofNat1, decide_true, decide_false]))

/-- `sG` on a field's last row, not the receipt's last. -/
theorem sG_fe {c : Claim} {e : Ext} {r s i : Nat} (hfe : i + 1 = fLen (Df c e r) s)
    (hrl : isRl (Df c e r) s i = false) (hge : (Df c e r).hr = true → (Df c e r).ge = true) {nx : Nat → Fp}
    {pub : List Fp} (hnx : nx Rcpt.act = 1) :
    ∀ x ∈ sG, evR (cF c e (.seg r s i)) nx false false pub x = 0 := by
  have h2 : s ≠ 26 ∧ (s = 23 → (Df c e r).hr = true) := by
    unfold isRl at hrl
    cases hh : (Df c e r).hr <;> simp [hh, hfe] at hrl ⊢ <;> omega
  have hfe' : decide (i + 1 = fLen (Df c e r) s) = true := by simp [hfe]
  simp only [sG, List.forall_mem_cons, List.forall_mem_nil, and_true]
  and_intros
  all_goals sgsimp
  all_goals (try simp only [hrl, hfe', hnx, b2n_false, b2n_true, ofNat0, ofNat1])
  all_goals first
    | grind
    | (simp only [oEnd_eq, o2End_eq]; grind)
    | (cases h : (Df c e r).hr
       · simp only [b2n_false, ofNat0]; grind
       · simp only [hge h, b2n_true, ofNat1]; grind)
    | (split
       · rename_i h; exact absurd h.symm h2.1
       · split
         · rename_i h h'; have := h2.2 h'.symm; simp only [this, b2n_true, ofNat1]; grind
         · grind)
    | rfin

/-- `sG` on a receipt's last row, followed by the next receipt (`rnx` its cells). -/
theorem sG_rl {c : Claim} {e : Ext} (hg : Good c e) {r s i : Nat} (hfe : i + 1 = fLen (Df c e r) s)
    (hrl : isRl (Df c e r) s i = true) (hr : r + 1 < NN e) {pub : List Fp} :
    ∀ x ∈ sG, evR (cF c e (.seg r s i)) (cF c e (.seg (r + 1) 5 0)) false false pub x = 0 := by
  have h2 : s = 26 ∨ (s = 23 ∧ (Df c e r).hr = false) := by
    unfold isRl at hrl
    cases hh : (Df c e r).hr <;> simp [hh] at hrl ⊢ <;> omega
  have hge := d_ge hg (show r < NN e by omega)
  obtain ⟨so, so2, srcnt, -⟩ := d_succ hg hr
  have hr1 := Df_r (c := c) hr
  have hr0 := Df_r (c := c) (show r < NN e by omega)
  have hlast : ((Df c e r).r + 1 == NN e) = false := by simp [hr0]; omega
  have hfe' : decide (i + 1 = fLen (Df c e r) s) = true := by simp [hfe]
  simp only [sG, List.forall_mem_cons, List.forall_mem_nil, and_true]
  and_intros
  all_goals sgsimp
  all_goals (try simp only [hrl, hfe', hlast, hr1, hr0, so, so2, srcnt, Bool.true_and, b2n_false, b2n_true,
    ofNat0, ofNat1])
  all_goals first
    | grind
    | (simp only [oEnd_eq, o2End_eq]; grind)
    | (simp only [ofNat_add_e, ofNat1, natCast_eq]; grind)
    | (cases h : (Df c e r).hr
       · simp only [b2n_false, ofNat0]; grind
       · simp only [hge h, b2n_true, ofNat1]; grind)
    | (rcases h2 with rfl | ⟨rfl, h3⟩ <;> simp only [Nat.reduceEqDiff, ↓reduceIte, ofNat0, ofNat1] <;>
        (try simp only [h3, b2n_false, ofNat0]) <;> grind)
    | rfin

/-- `sG` on the last record row (a padding row next). -/
theorem sG_last {c : Claim} {e : Ext} {r s i : Nat} (hfe : i + 1 = fLen (Df c e r) s)
    (hrl : isRl (Df c e r) s i = true) (hr : r + 1 = NN e) (hr0 : (Df c e r).r = r)
    (hge : (Df c e r).hr = true → (Df c e r).ge = true) {pub : List Fp} :
    ∀ x ∈ sG, evR (cF c e (.seg r s i)) (fun _ => 0) false false pub x = 0 := by
  have h2 : s = 26 ∨ (s = 23 ∧ (Df c e r).hr = false) := by
    unfold isRl at hrl
    cases hh : (Df c e r).hr <;> simp [hh] at hrl ⊢ <;> omega
  have hlast : ((Df c e r).r + 1 == NN e) = true := by simp [hr0, hr]
  have hfe' : decide (i + 1 = fLen (Df c e r) s) = true := by simp [hfe]
  simp only [sG, List.forall_mem_cons, List.forall_mem_nil, and_true]
  and_intros
  all_goals sgsimp
  all_goals (try simp only [hrl, hfe', hlast, Bool.true_and, b2n_false, b2n_true, ofNat0, ofNat1])
  all_goals first
    | grind
    | (simp only [oEnd_eq, o2End_eq]; grind)
    | (cases h : (Df c e r).hr
       · simp only [b2n_false, ofNat0]; grind
       · simp only [hge h, b2n_true, ofNat1]; grind)
    | (rcases h2 with rfl | ⟨rfl, h3⟩ <;> simp only [Nat.reduceEqDiff, ↓reduceIte, ofNat0, ofNat1] <;>
        (try simp only [h3, b2n_false, ofNat0]) <;> grind)
    | rfin

end RcptP

end ZkFormal.Near.Render
