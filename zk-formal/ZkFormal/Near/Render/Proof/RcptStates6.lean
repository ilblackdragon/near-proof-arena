import ZkFormal.Near.Render.Proof.RcptStates5

/-!
# ZkFormal.Near.Render.Proof.RcptStates6 — `cStates` on the claim rows, padding; `states_ok`
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

theorem Cc_cl_st {c : Claim} {e : Ext} {i st : Nat} (hi : i < 12) (h1 : 4 ≤ st) (h2 : st ≤ 26) :
    Cc c e (.cl i) st = if st = 4 then 1 else 0 := by
  obtain ⟨st1, st0, -, -⟩ := state_cells (c := c) (e := e) (ρ := .cl i) hi
  split
  · subst_vars; exact st1
  · exact st0 st h1 h2 (by simpa [stateOf, Rcpt.sCL])

/-- **`cStates` (without bits) on a claim row.** -/
theorem cl_rows {c : Claim} {e : Ext} (hg : Good c e) {i : Nat} (hi : i < 12) {pub : List Fp} :
    ∀ x ∈ sB ++ sC ++ sD ++ sE ++ sF ++ sG ++ sH,
      evR (cF c e (.cl i)) (cF c e (nextOf (Df c e) (.cl i))) (decide (i = 0)) false pub x = 0 := by
  have hN := NN_pos hg
  obtain ⟨d0o, d0o2, d0rc, -, d0r⟩ := d_zero (c := c) (e := e) (by omega)
  have hst : ∀ i', i' < 12 → ∀ st, 4 ≤ st → st ≤ 26 → cF c e (.cl i') st = if st = 4 then 1 else 0 := by
    intro i' hi' st h1 h2; simp only [cF, Cc_cl_st hi' h1 h2]; split <;> rfl
  have hst' : ∀ st, 4 ≤ st → st ≤ 26 → cF c e (.seg 0 5 0) st = if st = 5 then 1 else 0 := by
    intro st h1 h2
    by_cases h4 : st = 4
    · subst h4; simp only [cF, Cc_four]; rfl
    · simp only [cF, Cc_state (by omega) h2]; split <;> rfl
  rcases (show i < 11 ∨ i = 11 by omega) with h11 | rfl
  · have hn : nextOf (Df c e) (.cl i) = .cl (i + 1) := by simp [nextOf, h11]
    rw [hn]
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with (((((hB | hC) | hD) | hE) | hF) | hG) | hH
    · simp only [sB, List.mem_cons, List.not_mem_nil, or_false] at hB
      rcases hB with rfl | rfl | rfl
      · simp only [evR_sub, onehot_rec (show RecOk (NN e) (Df c e) (.cl i) from hi), evR_c, cF, L_act, ofNat1]; grind
      all_goals simp only [evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, evR_k, cF, ZkFormal.Near.Render.RcptP.b2n_true, ZkFormal.Near.Render.RcptP.b2n_false, ZkFormal.Near.Render.RcptP.L_act, ZkFormal.Near.Render.RcptP.L_sCL, ZkFormal.Near.Render.RcptP.L_sPL, ZkFormal.Near.Render.RcptP.L_sP, ZkFormal.Near.Render.RcptP.L_sVL, ZkFormal.Near.Render.RcptP.L_sV, ZkFormal.Near.Render.RcptP.L_sRID, ZkFormal.Near.Render.RcptP.L_sT0, ZkFormal.Near.Render.RcptP.L_sSL, ZkFormal.Near.Render.RcptP.L_sS, ZkFormal.Near.Render.RcptP.L_sKT, ZkFormal.Near.Render.RcptP.L_sPK, ZkFormal.Near.Render.RcptP.L_sGP, ZkFormal.Near.Render.RcptP.L_sTL, ZkFormal.Near.Render.RcptP.L_sDEP, ZkFormal.Near.Render.RcptP.L_sXP0, ZkFormal.Near.Render.RcptP.L_sXRI, ZkFormal.Near.Render.RcptP.L_sXG, ZkFormal.Near.Render.RcptP.L_sXST, ZkFormal.Near.Render.RcptP.L_sXL0, ZkFormal.Near.Render.RcptP.L_sXLH, ZkFormal.Near.Render.RcptP.L_sXRH, ZkFormal.Near.Render.RcptP.L_sXRF, ZkFormal.Near.Render.RcptP.L_sXRZ, ZkFormal.Near.Render.RcptP.L_rf, ZkFormal.Near.Render.RcptP.L_rl, ZkFormal.Near.Render.RcptP.L_lastR, ZkFormal.Near.Render.RcptP.L_idx, ZkFormal.Near.Render.RcptP.L_fs, ZkFormal.Near.Render.RcptP.L_fe, ZkFormal.Near.Render.RcptP.L_b, ZkFormal.Near.Render.RcptP.L_tA, ZkFormal.Near.Render.RcptP.L_symA, ZkFormal.Near.Render.RcptP.L_lastA, ZkFormal.Near.Render.RcptP.L_gKA, ZkFormal.Near.Render.RcptP.L_kz, ZkFormal.Near.Render.RcptP.L_r, ZkFormal.Near.Render.RcptP.L_o, ZkFormal.Near.Render.RcptP.L_o2, ZkFormal.Near.Render.RcptP.L_Lp, ZkFormal.Near.Render.RcptP.L_Lv, ZkFormal.Near.Render.RcptP.L_Ls, ZkFormal.Near.Render.RcptP.L_kt, ZkFormal.Near.Render.RcptP.L_hr, ZkFormal.Near.Render.RcptP.L_kslot, ZkFormal.Near.Render.RcptP.L_tprev, ZkFormal.Near.Render.RcptP.L_rcnt, ZkFormal.Near.Render.RcptP.L_ge, ZkFormal.Near.Render.RcptP.L_big, ZkFormal.Near.Render.RcptP.L_oEnd, ZkFormal.Near.Render.RcptP.L_o2End, ZkFormal.Near.Render.RcptP.L_h2, ZkFormal.Near.Render.RcptP.L_h3, ZkFormal.Near.Render.RcptP.L_h5, ZkFormal.Near.Render.RcptP.L_h6, ZkFormal.Near.Render.RcptP.L_h7, ZkFormal.Near.Render.RcptP.L_z, ZkFormal.Near.Render.RcptP.L_linv, ZkFormal.Near.Render.RcptP.L_l210, ZkFormal.Near.Render.RcptP.L_hx6, ZkFormal.Near.Render.RcptP.L_acc, ZkFormal.Near.Render.RcptP.L_vc0, ZkFormal.Near.Render.RcptP.L_vc1, ZkFormal.Near.Render.RcptP.L_h01, ZkFormal.Near.Render.RcptP.L_p1, ZkFormal.Near.Render.RcptP.L_p2, ZkFormal.Near.Render.RcptP.L_p3, ZkFormal.Near.Render.RcptP.L_i1, ZkFormal.Near.Render.RcptP.L_i2, ZkFormal.Near.Render.RcptP.L_i3, ZkFormal.Near.Render.RcptP.L_isys, ZkFormal.Near.Render.RcptP.L_r1, ZkFormal.Near.Render.RcptP.L_c4, ZkFormal.Near.Render.RcptP.L_burnt, ZkFormal.Near.Render.RcptP.L_ramt, ZkFormal.Near.Render.RcptP.L_sumD, ZkFormal.Near.Render.RcptP.L_bef, ZkFormal.Near.Render.RcptP.L_lk, ZkFormal.Near.Render.RcptP.L_st, ZkFormal.Near.Render.RcptP.L_dsum, ZkFormal.Near.Render.RcptP.L_invB, ZkFormal.Near.Render.RcptP.L_dI, ZkFormal.Near.Render.RcptP.L_dL, ZkFormal.Near.Render.RcptP.L_gDg, ZkFormal.Near.Render.RcptP.L_lo8, ZkFormal.Near.Render.RcptP.L_lo4, ZkFormal.Near.Render.RcptP.L_invA, ZkFormal.Near.Render.RcptP.L_c1, ZkFormal.Near.Render.RcptP.L_c2, ZkFormal.Near.Render.RcptP.L_c3,
        show ¬ (i = 11) by omega, show ¬ (i + 1 = 0) by omega, decide_false, b2n_false, ofNat0, ofNat1,
        ofNat_add_e, natCast_eq]
      all_goals grind
    · simp only [sC, List.mem_map] at hC
      obtain ⟨st, hs, rfl⟩ := hC
      have := states_range hs
      simp only [evR_mul3, evR_not, evR_sub, evR_c, evR_n, hst i hi st this.1 this.2,
        hst (i + 1) (by omega) st this.1 this.2]; grind
    · simp only [sD, List.mem_cons, List.not_mem_nil, or_false] at hD
      rcases hD with rfl | rfl <;>
        simp only [evR_mul3, evR_c, cF, L_fe, show ¬ (i = 11) by omega, decide_false, b2n_false, ofNat0] <;> grind
    · simp only [sE, List.mem_map] at hE
      obtain ⟨⟨st, ex⟩, -, rfl⟩ := hE
      simp only [evR_mul3, evR_c, cF, L_fe, show ¬ (i = 11) by omega, decide_false, b2n_false, ofNat0]; grind
    · simp only [sF, List.mem_map] at hF
      obtain ⟨⟨st, st', g⟩, -, rfl⟩ := hF
      simp only [evR_mul, evR_mul3, evR_c, cF, L_fe, show ¬ (i = 11) by omega, decide_false, b2n_false, ofNat0]
      grind
    · simp only [sG, List.mem_cons, List.not_mem_nil, or_false] at hG
      rcases hG with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      all_goals subst h
      all_goals simp only [evR_mul, evR_mul3, evR_sub, evR_add, evR_not, evR_c, evR_n, evR_k, evR_smul,
        evR_sum_cons, evR_sum_nil, evR_isFirst, evR_isLast, evR_isTransition, Rcpt.rowE, Rcpt.varE, cF, ZkFormal.Near.Render.RcptP.b2n_true, ZkFormal.Near.Render.RcptP.b2n_false, ZkFormal.Near.Render.RcptP.L_act, ZkFormal.Near.Render.RcptP.L_sCL, ZkFormal.Near.Render.RcptP.L_sPL, ZkFormal.Near.Render.RcptP.L_sP, ZkFormal.Near.Render.RcptP.L_sVL, ZkFormal.Near.Render.RcptP.L_sV, ZkFormal.Near.Render.RcptP.L_sRID, ZkFormal.Near.Render.RcptP.L_sT0, ZkFormal.Near.Render.RcptP.L_sSL, ZkFormal.Near.Render.RcptP.L_sS, ZkFormal.Near.Render.RcptP.L_sKT, ZkFormal.Near.Render.RcptP.L_sPK, ZkFormal.Near.Render.RcptP.L_sGP, ZkFormal.Near.Render.RcptP.L_sTL, ZkFormal.Near.Render.RcptP.L_sDEP, ZkFormal.Near.Render.RcptP.L_sXP0, ZkFormal.Near.Render.RcptP.L_sXRI, ZkFormal.Near.Render.RcptP.L_sXG, ZkFormal.Near.Render.RcptP.L_sXST, ZkFormal.Near.Render.RcptP.L_sXL0, ZkFormal.Near.Render.RcptP.L_sXLH, ZkFormal.Near.Render.RcptP.L_sXRH, ZkFormal.Near.Render.RcptP.L_sXRF, ZkFormal.Near.Render.RcptP.L_sXRZ, ZkFormal.Near.Render.RcptP.L_rf, ZkFormal.Near.Render.RcptP.L_rl, ZkFormal.Near.Render.RcptP.L_lastR, ZkFormal.Near.Render.RcptP.L_idx, ZkFormal.Near.Render.RcptP.L_fs, ZkFormal.Near.Render.RcptP.L_fe, ZkFormal.Near.Render.RcptP.L_b, ZkFormal.Near.Render.RcptP.L_tA, ZkFormal.Near.Render.RcptP.L_symA, ZkFormal.Near.Render.RcptP.L_lastA, ZkFormal.Near.Render.RcptP.L_gKA, ZkFormal.Near.Render.RcptP.L_kz, ZkFormal.Near.Render.RcptP.L_r, ZkFormal.Near.Render.RcptP.L_o, ZkFormal.Near.Render.RcptP.L_o2, ZkFormal.Near.Render.RcptP.L_Lp, ZkFormal.Near.Render.RcptP.L_Lv, ZkFormal.Near.Render.RcptP.L_Ls, ZkFormal.Near.Render.RcptP.L_kt, ZkFormal.Near.Render.RcptP.L_hr, ZkFormal.Near.Render.RcptP.L_kslot, ZkFormal.Near.Render.RcptP.L_tprev, ZkFormal.Near.Render.RcptP.L_rcnt, ZkFormal.Near.Render.RcptP.L_ge, ZkFormal.Near.Render.RcptP.L_big, ZkFormal.Near.Render.RcptP.L_oEnd, ZkFormal.Near.Render.RcptP.L_o2End, ZkFormal.Near.Render.RcptP.L_h2, ZkFormal.Near.Render.RcptP.L_h3, ZkFormal.Near.Render.RcptP.L_h5, ZkFormal.Near.Render.RcptP.L_h6, ZkFormal.Near.Render.RcptP.L_h7, ZkFormal.Near.Render.RcptP.L_z, ZkFormal.Near.Render.RcptP.L_linv, ZkFormal.Near.Render.RcptP.L_l210, ZkFormal.Near.Render.RcptP.L_hx6, ZkFormal.Near.Render.RcptP.L_acc, ZkFormal.Near.Render.RcptP.L_vc0, ZkFormal.Near.Render.RcptP.L_vc1, ZkFormal.Near.Render.RcptP.L_h01, ZkFormal.Near.Render.RcptP.L_p1, ZkFormal.Near.Render.RcptP.L_p2, ZkFormal.Near.Render.RcptP.L_p3, ZkFormal.Near.Render.RcptP.L_i1, ZkFormal.Near.Render.RcptP.L_i2, ZkFormal.Near.Render.RcptP.L_i3, ZkFormal.Near.Render.RcptP.L_isys, ZkFormal.Near.Render.RcptP.L_r1, ZkFormal.Near.Render.RcptP.L_c4, ZkFormal.Near.Render.RcptP.L_burnt, ZkFormal.Near.Render.RcptP.L_ramt, ZkFormal.Near.Render.RcptP.L_sumD, ZkFormal.Near.Render.RcptP.L_bef, ZkFormal.Near.Render.RcptP.L_lk, ZkFormal.Near.Render.RcptP.L_st, ZkFormal.Near.Render.RcptP.L_dsum, ZkFormal.Near.Render.RcptP.L_invB, ZkFormal.Near.Render.RcptP.L_dI, ZkFormal.Near.Render.RcptP.L_dL, ZkFormal.Near.Render.RcptP.L_gDg, ZkFormal.Near.Render.RcptP.L_lo8, ZkFormal.Near.Render.RcptP.L_lo4, ZkFormal.Near.Render.RcptP.L_invA, ZkFormal.Near.Render.RcptP.L_c1, ZkFormal.Near.Render.RcptP.L_c2, ZkFormal.Near.Render.RcptP.L_c3,
        Bool.false_eq_true, ↓reduceIte, ofNat0, ofNat1, show ¬ (i = 11) by omega, decide_false, b2n_false]
      all_goals rfin
    · simp only [sH, List.mem_map] at hH
      obtain ⟨y, -, rfl⟩ := hH
      simp only [evR_mul3, Rcpt.rowE, evR_sub, evR_c, cF, L_act, L_sCL]; grind
  · have hn : nextOf (Df c e) (.cl 11) = .seg 0 5 0 := by simp [nextOf]
    rw [hn]
    have hfe : cF c e (.cl 11) Rcpt.fe = 1 := by simp only [cF, L_fe, decide_true, b2n_true]; rfl
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with (((((hB | hC) | hD) | hE) | hF) | hG) | hH
    · simp only [sB, List.mem_cons, List.not_mem_nil, or_false] at hB
      rcases hB with rfl | rfl | rfl
      · simp only [evR_sub, onehot_rec (show RecOk (NN e) (Df c e) (.cl 11) from hi), evR_c, cF, L_act, ofNat1]
        grind
      all_goals simp only [evR_mul3, evR_not, evR_c, hfe]; grind
    · simp only [sC, List.mem_map] at hC
      obtain ⟨st, -, rfl⟩ := hC
      simp only [evR_mul3, evR_not, evR_c, hfe]; grind
    · simp only [sD, List.mem_cons, List.not_mem_nil, or_false] at hD
      rcases hD with rfl | rfl <;>
        simp only [evR_mul3, evR_c, evR_n, evR_not, hfe, cF, L_rl, S_idx, S_fs, decide_true, b2n_true, ofNat0,
          ofNat1] <;> grind
    · simp only [sE, List.mem_map] at hE
      obtain ⟨⟨st, ex⟩, hm, rfl⟩ := hE
      simp only [evR_mul3, evR_c, evR_sub, hfe]
      simp only [Rcpt.lastIdx, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | hm
      · simp only [evR_k, cF, L_sCL, L_idx, natCast_eq, ofNat1]; grind
      · have : 5 ≤ st ∧ st ≤ 26 := by
          simp only [Rcpt.act, Rcpt.rf, Rcpt.rl, Rcpt.lastR, Rcpt.sCL, Rcpt.sPL, Rcpt.sP, Rcpt.sVL, Rcpt.sV, Rcpt.sRID, Rcpt.sT0, Rcpt.sSL, Rcpt.sS, Rcpt.sKT, Rcpt.sPK, Rcpt.sGP, Rcpt.sTL, Rcpt.sDEP, Rcpt.sXP0, Rcpt.sXRI, Rcpt.sXG, Rcpt.sXST, Rcpt.sXL0, Rcpt.sXLH, Rcpt.sXRH, Rcpt.sXRF, Rcpt.sXRZ, Rcpt.idx, Rcpt.fs, Rcpt.fe, Rcpt.b, Rcpt.e1Id, Rcpt.e1Pos, Rcpt.e1V, Rcpt.e1G, Rcpt.e2Id, Rcpt.e2Pos, Rcpt.e2V, Rcpt.e2G, Rcpt.e3Id, Rcpt.e3Pos, Rcpt.e3V, Rcpt.e3G, Rcpt.tA, Rcpt.symA, Rcpt.lastA, Rcpt.gKA, Rcpt.kz, Rcpt.r, Rcpt.o, Rcpt.o2, Rcpt.Lp, Rcpt.Lv, Rcpt.Ls, Rcpt.kt, Rcpt.hr, Rcpt.kslot, Rcpt.tprev, Rcpt.rcnt, Rcpt.ge, Rcpt.big, Rcpt.oEnd, Rcpt.o2End, Rcpt.reg, Rcpt.tok, Rcpt.h2, Rcpt.h3, Rcpt.h5, Rcpt.h6, Rcpt.h7, Rcpt.lb, Rcpt.z, Rcpt.linv, Rcpt.l210, Rcpt.hx6, Rcpt.acc, Rcpt.vc0, Rcpt.vc1, Rcpt.h01, Rcpt.p1, Rcpt.p2, Rcpt.p3, Rcpt.i1, Rcpt.i2, Rcpt.i3, Rcpt.isys, Rcpt.r1, Rcpt.lo8, Rcpt.lo4, Rcpt.xb, Rcpt.c1, Rcpt.c2, Rcpt.c3, Rcpt.c4, Rcpt.dl, Rcpt.burnt, Rcpt.ramt, Rcpt.sumD, Rcpt.invA, Rcpt.bef, Rcpt.lk, Rcpt.st, Rcpt.dsum, Rcpt.invB, Rcpt.dI, Rcpt.dL, Rcpt.gDg, Rcpt.width] at hm; rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
            h | h | h | h | h <;> omega
        rw [hst 11 hi st (by omega) this.2, if_neg (by omega)]; grind
    · simp only [sF, List.mem_map] at hF
      obtain ⟨⟨st, st', g⟩, hm, rfl⟩ := hF
      simp only [evR_mul, evR_mul3, evR_c, evR_not, evR_n, hfe]
      simp only [Rcpt.succ, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl, rfl⟩ | hm
      · simp only [evR_k, cF, L_sCL, S_sPL, ↓reduceIte, natCast_eq, ofNat1]; grind
      · have : 5 ≤ st ∧ st ≤ 26 := by
          simp only [Rcpt.act, Rcpt.rf, Rcpt.rl, Rcpt.lastR, Rcpt.sCL, Rcpt.sPL, Rcpt.sP, Rcpt.sVL, Rcpt.sV, Rcpt.sRID, Rcpt.sT0, Rcpt.sSL, Rcpt.sS, Rcpt.sKT, Rcpt.sPK, Rcpt.sGP, Rcpt.sTL, Rcpt.sDEP, Rcpt.sXP0, Rcpt.sXRI, Rcpt.sXG, Rcpt.sXST, Rcpt.sXL0, Rcpt.sXLH, Rcpt.sXRH, Rcpt.sXRF, Rcpt.sXRZ, Rcpt.idx, Rcpt.fs, Rcpt.fe, Rcpt.b, Rcpt.e1Id, Rcpt.e1Pos, Rcpt.e1V, Rcpt.e1G, Rcpt.e2Id, Rcpt.e2Pos, Rcpt.e2V, Rcpt.e2G, Rcpt.e3Id, Rcpt.e3Pos, Rcpt.e3V, Rcpt.e3G, Rcpt.tA, Rcpt.symA, Rcpt.lastA, Rcpt.gKA, Rcpt.kz, Rcpt.r, Rcpt.o, Rcpt.o2, Rcpt.Lp, Rcpt.Lv, Rcpt.Ls, Rcpt.kt, Rcpt.hr, Rcpt.kslot, Rcpt.tprev, Rcpt.rcnt, Rcpt.ge, Rcpt.big, Rcpt.oEnd, Rcpt.o2End, Rcpt.reg, Rcpt.tok, Rcpt.h2, Rcpt.h3, Rcpt.h5, Rcpt.h6, Rcpt.h7, Rcpt.lb, Rcpt.z, Rcpt.linv, Rcpt.l210, Rcpt.hx6, Rcpt.acc, Rcpt.vc0, Rcpt.vc1, Rcpt.h01, Rcpt.p1, Rcpt.p2, Rcpt.p3, Rcpt.i1, Rcpt.i2, Rcpt.i3, Rcpt.isys, Rcpt.r1, Rcpt.lo8, Rcpt.lo4, Rcpt.xb, Rcpt.c1, Rcpt.c2, Rcpt.c3, Rcpt.c4, Rcpt.dl, Rcpt.burnt, Rcpt.ramt, Rcpt.sumD, Rcpt.invA, Rcpt.bef, Rcpt.lk, Rcpt.st, Rcpt.dsum, Rcpt.invB, Rcpt.dI, Rcpt.dL, Rcpt.gDg, Rcpt.width] at hm; rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
            h | h | h | h | h <;> omega
        rw [hst 11 hi st (by omega) this.2, if_neg (by omega)]; grind
    · have hr0 : (Df c e 0).r = 0 := d0r
      simp only [sG, List.mem_cons, List.not_mem_nil, or_false] at hG
      rcases hG with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      all_goals subst h
      all_goals simp only [evR_mul, evR_mul3, evR_sub, evR_add, evR_not, evR_c, evR_n, evR_k, evR_smul,
        evR_sum_cons, evR_sum_nil, evR_isFirst, evR_isLast, evR_isTransition, Rcpt.rowE, Rcpt.varE, cF, ZkFormal.Near.Render.RcptP.b2n_true, ZkFormal.Near.Render.RcptP.b2n_false, ZkFormal.Near.Render.RcptP.L_act, ZkFormal.Near.Render.RcptP.L_sCL, ZkFormal.Near.Render.RcptP.L_sPL, ZkFormal.Near.Render.RcptP.L_sP, ZkFormal.Near.Render.RcptP.L_sVL, ZkFormal.Near.Render.RcptP.L_sV, ZkFormal.Near.Render.RcptP.L_sRID, ZkFormal.Near.Render.RcptP.L_sT0, ZkFormal.Near.Render.RcptP.L_sSL, ZkFormal.Near.Render.RcptP.L_sS, ZkFormal.Near.Render.RcptP.L_sKT, ZkFormal.Near.Render.RcptP.L_sPK, ZkFormal.Near.Render.RcptP.L_sGP, ZkFormal.Near.Render.RcptP.L_sTL, ZkFormal.Near.Render.RcptP.L_sDEP, ZkFormal.Near.Render.RcptP.L_sXP0, ZkFormal.Near.Render.RcptP.L_sXRI, ZkFormal.Near.Render.RcptP.L_sXG, ZkFormal.Near.Render.RcptP.L_sXST, ZkFormal.Near.Render.RcptP.L_sXL0, ZkFormal.Near.Render.RcptP.L_sXLH, ZkFormal.Near.Render.RcptP.L_sXRH, ZkFormal.Near.Render.RcptP.L_sXRF, ZkFormal.Near.Render.RcptP.L_sXRZ, ZkFormal.Near.Render.RcptP.L_rf, ZkFormal.Near.Render.RcptP.L_rl, ZkFormal.Near.Render.RcptP.L_lastR, ZkFormal.Near.Render.RcptP.L_idx, ZkFormal.Near.Render.RcptP.L_fs, ZkFormal.Near.Render.RcptP.L_fe, ZkFormal.Near.Render.RcptP.L_b, ZkFormal.Near.Render.RcptP.L_tA, ZkFormal.Near.Render.RcptP.L_symA, ZkFormal.Near.Render.RcptP.L_lastA, ZkFormal.Near.Render.RcptP.L_gKA, ZkFormal.Near.Render.RcptP.L_kz, ZkFormal.Near.Render.RcptP.L_r, ZkFormal.Near.Render.RcptP.L_o, ZkFormal.Near.Render.RcptP.L_o2, ZkFormal.Near.Render.RcptP.L_Lp, ZkFormal.Near.Render.RcptP.L_Lv, ZkFormal.Near.Render.RcptP.L_Ls, ZkFormal.Near.Render.RcptP.L_kt, ZkFormal.Near.Render.RcptP.L_hr, ZkFormal.Near.Render.RcptP.L_kslot, ZkFormal.Near.Render.RcptP.L_tprev, ZkFormal.Near.Render.RcptP.L_rcnt, ZkFormal.Near.Render.RcptP.L_ge, ZkFormal.Near.Render.RcptP.L_big, ZkFormal.Near.Render.RcptP.L_oEnd, ZkFormal.Near.Render.RcptP.L_o2End, ZkFormal.Near.Render.RcptP.L_h2, ZkFormal.Near.Render.RcptP.L_h3, ZkFormal.Near.Render.RcptP.L_h5, ZkFormal.Near.Render.RcptP.L_h6, ZkFormal.Near.Render.RcptP.L_h7, ZkFormal.Near.Render.RcptP.L_z, ZkFormal.Near.Render.RcptP.L_linv, ZkFormal.Near.Render.RcptP.L_l210, ZkFormal.Near.Render.RcptP.L_hx6, ZkFormal.Near.Render.RcptP.L_acc, ZkFormal.Near.Render.RcptP.L_vc0, ZkFormal.Near.Render.RcptP.L_vc1, ZkFormal.Near.Render.RcptP.L_h01, ZkFormal.Near.Render.RcptP.L_p1, ZkFormal.Near.Render.RcptP.L_p2, ZkFormal.Near.Render.RcptP.L_p3, ZkFormal.Near.Render.RcptP.L_i1, ZkFormal.Near.Render.RcptP.L_i2, ZkFormal.Near.Render.RcptP.L_i3, ZkFormal.Near.Render.RcptP.L_isys, ZkFormal.Near.Render.RcptP.L_r1, ZkFormal.Near.Render.RcptP.L_c4, ZkFormal.Near.Render.RcptP.L_burnt, ZkFormal.Near.Render.RcptP.L_ramt, ZkFormal.Near.Render.RcptP.L_sumD, ZkFormal.Near.Render.RcptP.L_bef, ZkFormal.Near.Render.RcptP.L_lk, ZkFormal.Near.Render.RcptP.L_st, ZkFormal.Near.Render.RcptP.L_dsum, ZkFormal.Near.Render.RcptP.L_invB, ZkFormal.Near.Render.RcptP.L_dI, ZkFormal.Near.Render.RcptP.L_dL, ZkFormal.Near.Render.RcptP.L_gDg, ZkFormal.Near.Render.RcptP.L_lo8, ZkFormal.Near.Render.RcptP.L_lo4, ZkFormal.Near.Render.RcptP.L_invA, ZkFormal.Near.Render.RcptP.L_c1, ZkFormal.Near.Render.RcptP.L_c2, ZkFormal.Near.Render.RcptP.L_c3, ZkFormal.Near.Render.RcptP.b2n_true, ZkFormal.Near.Render.RcptP.b2n_false, ZkFormal.Near.Render.RcptP.S_act, ZkFormal.Near.Render.RcptP.S_rf, ZkFormal.Near.Render.RcptP.S_rl, ZkFormal.Near.Render.RcptP.S_lastR, ZkFormal.Near.Render.RcptP.S_sCL, ZkFormal.Near.Render.RcptP.S_sPL, ZkFormal.Near.Render.RcptP.S_sP, ZkFormal.Near.Render.RcptP.S_sVL, ZkFormal.Near.Render.RcptP.S_sV, ZkFormal.Near.Render.RcptP.S_sRID, ZkFormal.Near.Render.RcptP.S_sT0, ZkFormal.Near.Render.RcptP.S_sSL, ZkFormal.Near.Render.RcptP.S_sS, ZkFormal.Near.Render.RcptP.S_sKT, ZkFormal.Near.Render.RcptP.S_sPK, ZkFormal.Near.Render.RcptP.S_sGP, ZkFormal.Near.Render.RcptP.S_sTL, ZkFormal.Near.Render.RcptP.S_sDEP, ZkFormal.Near.Render.RcptP.S_sXP0, ZkFormal.Near.Render.RcptP.S_sXRI, ZkFormal.Near.Render.RcptP.S_sXG, ZkFormal.Near.Render.RcptP.S_sXST, ZkFormal.Near.Render.RcptP.S_sXL0, ZkFormal.Near.Render.RcptP.S_sXLH, ZkFormal.Near.Render.RcptP.S_sXRH, ZkFormal.Near.Render.RcptP.S_sXRF, ZkFormal.Near.Render.RcptP.S_sXRZ, ZkFormal.Near.Render.RcptP.S_idx, ZkFormal.Near.Render.RcptP.S_fs, ZkFormal.Near.Render.RcptP.S_fe, ZkFormal.Near.Render.RcptP.S_b, ZkFormal.Near.Render.RcptP.S_tA, ZkFormal.Near.Render.RcptP.S_symA, ZkFormal.Near.Render.RcptP.S_lastA, ZkFormal.Near.Render.RcptP.S_gKA, ZkFormal.Near.Render.RcptP.S_kz, ZkFormal.Near.Render.RcptP.S_r, ZkFormal.Near.Render.RcptP.S_o, ZkFormal.Near.Render.RcptP.S_o2, ZkFormal.Near.Render.RcptP.S_Lp, ZkFormal.Near.Render.RcptP.S_Lv, ZkFormal.Near.Render.RcptP.S_Ls, ZkFormal.Near.Render.RcptP.S_kt, ZkFormal.Near.Render.RcptP.S_hr, ZkFormal.Near.Render.RcptP.S_kslot, ZkFormal.Near.Render.RcptP.S_tprev, ZkFormal.Near.Render.RcptP.S_rcnt, ZkFormal.Near.Render.RcptP.S_ge, ZkFormal.Near.Render.RcptP.S_big, ZkFormal.Near.Render.RcptP.S_oEnd, ZkFormal.Near.Render.RcptP.S_o2End, ZkFormal.Near.Render.RcptP.S_h2, ZkFormal.Near.Render.RcptP.S_h3, ZkFormal.Near.Render.RcptP.S_h5, ZkFormal.Near.Render.RcptP.S_h6, ZkFormal.Near.Render.RcptP.S_h7, ZkFormal.Near.Render.RcptP.S_z, ZkFormal.Near.Render.RcptP.S_linv, ZkFormal.Near.Render.RcptP.S_l210, ZkFormal.Near.Render.RcptP.S_hx6, ZkFormal.Near.Render.RcptP.S_acc, ZkFormal.Near.Render.RcptP.S_vc0, ZkFormal.Near.Render.RcptP.S_vc1, ZkFormal.Near.Render.RcptP.S_h01, ZkFormal.Near.Render.RcptP.S_p1, ZkFormal.Near.Render.RcptP.S_p2, ZkFormal.Near.Render.RcptP.S_p3, ZkFormal.Near.Render.RcptP.S_i1, ZkFormal.Near.Render.RcptP.S_i2, ZkFormal.Near.Render.RcptP.S_i3, ZkFormal.Near.Render.RcptP.S_isys, ZkFormal.Near.Render.RcptP.S_r1, ZkFormal.Near.Render.RcptP.S_lo8, ZkFormal.Near.Render.RcptP.S_lo4, ZkFormal.Near.Render.RcptP.S_c1, ZkFormal.Near.Render.RcptP.S_c2, ZkFormal.Near.Render.RcptP.S_c3, ZkFormal.Near.Render.RcptP.S_c4, ZkFormal.Near.Render.RcptP.S_burnt, ZkFormal.Near.Render.RcptP.S_ramt, ZkFormal.Near.Render.RcptP.S_sumD, ZkFormal.Near.Render.RcptP.S_invA, ZkFormal.Near.Render.RcptP.S_bef, ZkFormal.Near.Render.RcptP.S_lk, ZkFormal.Near.Render.RcptP.S_st, ZkFormal.Near.Render.RcptP.S_dsum, ZkFormal.Near.Render.RcptP.S_invB, ZkFormal.Near.Render.RcptP.S_dI, ZkFormal.Near.Render.RcptP.S_dL, ZkFormal.Near.Render.RcptP.S_gDg, ZkFormal.Near.Render.RcptP.S_reg, ZkFormal.Near.Render.RcptP.S_tok, ZkFormal.Near.Render.RcptP.S_xb, ZkFormal.Near.Render.RcptP.S_lb, ZkFormal.Near.Render.RcptP.S_dl,
        Bool.false_eq_true, ↓reduceIte, ofNat0, ofNat1, decide_true, b2n_true, d0o, d0o2, d0rc, d0r]
      all_goals rfin
    · simp only [sH, List.mem_map] at hH
      obtain ⟨y, -, rfl⟩ := hH
      simp only [evR_mul3, Rcpt.rowE, evR_sub, evR_c, cF, L_act, L_sCL]; grind

end RcptP

end ZkFormal.Near.Render
