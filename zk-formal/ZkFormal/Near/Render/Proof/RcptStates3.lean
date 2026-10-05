import ZkFormal.Near.Render.Proof.RcptStates2

/-!
# ZkFormal.Near.Render.Proof.RcptStates3 — `cStates` at a field's last row

Last indices (`sE`), successions (`sF`), boundaries (`sG`) on a field's last
row: next field, next receipt, or (last receipt) a padding row.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

theorem fe1 {c : Claim} {e : Ext} {r s i : Nat} (hfe : i + 1 = fLen (Df c e r) s) :
    cF c e (.seg r s i) Rcpt.fe = 1 := by
  simp only [cF, S_fe, hfe, decide_true, b2n_true]; rfl

/-- Last indices. -/
theorem sE_end {c : Claim} {e : Ext} {r s i : Nat} (hfe : i + 1 = fLen (Df c e r) s) {nx : Nat → Fp}
    {fst lst : Bool} {pub : List Fp} : ∀ x ∈ sE, evR (cF c e (.seg r s i)) nx fst lst pub x = 0 := by
  intro x hx
  simp only [sE, List.mem_map] at hx
  obtain ⟨⟨st, ex⟩, hmem, rfl⟩ := hx
  simp only [evR_mul3, evR_c, evR_sub, fe1 hfe]
  simp only [Rcpt.lastIdx, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp only [cF, ZkFormal.Near.Render.RcptP.b2n_true, ZkFormal.Near.Render.RcptP.b2n_false, ZkFormal.Near.Render.RcptP.S_act, ZkFormal.Near.Render.RcptP.S_rf, ZkFormal.Near.Render.RcptP.S_rl, ZkFormal.Near.Render.RcptP.S_lastR, ZkFormal.Near.Render.RcptP.S_sCL, ZkFormal.Near.Render.RcptP.S_sPL, ZkFormal.Near.Render.RcptP.S_sP, ZkFormal.Near.Render.RcptP.S_sVL, ZkFormal.Near.Render.RcptP.S_sV, ZkFormal.Near.Render.RcptP.S_sRID, ZkFormal.Near.Render.RcptP.S_sT0, ZkFormal.Near.Render.RcptP.S_sSL, ZkFormal.Near.Render.RcptP.S_sS, ZkFormal.Near.Render.RcptP.S_sKT, ZkFormal.Near.Render.RcptP.S_sPK, ZkFormal.Near.Render.RcptP.S_sGP, ZkFormal.Near.Render.RcptP.S_sTL, ZkFormal.Near.Render.RcptP.S_sDEP, ZkFormal.Near.Render.RcptP.S_sXP0, ZkFormal.Near.Render.RcptP.S_sXRI, ZkFormal.Near.Render.RcptP.S_sXG, ZkFormal.Near.Render.RcptP.S_sXST, ZkFormal.Near.Render.RcptP.S_sXL0, ZkFormal.Near.Render.RcptP.S_sXLH, ZkFormal.Near.Render.RcptP.S_sXRH, ZkFormal.Near.Render.RcptP.S_sXRF, ZkFormal.Near.Render.RcptP.S_sXRZ, ZkFormal.Near.Render.RcptP.S_idx, ZkFormal.Near.Render.RcptP.S_fs, ZkFormal.Near.Render.RcptP.S_fe, ZkFormal.Near.Render.RcptP.S_b, ZkFormal.Near.Render.RcptP.S_tA, ZkFormal.Near.Render.RcptP.S_symA, ZkFormal.Near.Render.RcptP.S_lastA, ZkFormal.Near.Render.RcptP.S_gKA, ZkFormal.Near.Render.RcptP.S_kz, ZkFormal.Near.Render.RcptP.S_r, ZkFormal.Near.Render.RcptP.S_o, ZkFormal.Near.Render.RcptP.S_o2, ZkFormal.Near.Render.RcptP.S_Lp, ZkFormal.Near.Render.RcptP.S_Lv, ZkFormal.Near.Render.RcptP.S_Ls, ZkFormal.Near.Render.RcptP.S_kt, ZkFormal.Near.Render.RcptP.S_hr, ZkFormal.Near.Render.RcptP.S_kslot, ZkFormal.Near.Render.RcptP.S_tprev, ZkFormal.Near.Render.RcptP.S_rcnt, ZkFormal.Near.Render.RcptP.S_ge, ZkFormal.Near.Render.RcptP.S_big, ZkFormal.Near.Render.RcptP.S_oEnd, ZkFormal.Near.Render.RcptP.S_o2End, ZkFormal.Near.Render.RcptP.S_h2, ZkFormal.Near.Render.RcptP.S_h3, ZkFormal.Near.Render.RcptP.S_h5, ZkFormal.Near.Render.RcptP.S_h6, ZkFormal.Near.Render.RcptP.S_h7, ZkFormal.Near.Render.RcptP.S_z, ZkFormal.Near.Render.RcptP.S_linv, ZkFormal.Near.Render.RcptP.S_l210, ZkFormal.Near.Render.RcptP.S_hx6, ZkFormal.Near.Render.RcptP.S_acc, ZkFormal.Near.Render.RcptP.S_vc0, ZkFormal.Near.Render.RcptP.S_vc1, ZkFormal.Near.Render.RcptP.S_h01, ZkFormal.Near.Render.RcptP.S_p1, ZkFormal.Near.Render.RcptP.S_p2, ZkFormal.Near.Render.RcptP.S_p3, ZkFormal.Near.Render.RcptP.S_i1, ZkFormal.Near.Render.RcptP.S_i2, ZkFormal.Near.Render.RcptP.S_i3, ZkFormal.Near.Render.RcptP.S_isys, ZkFormal.Near.Render.RcptP.S_r1, ZkFormal.Near.Render.RcptP.S_lo8, ZkFormal.Near.Render.RcptP.S_lo4, ZkFormal.Near.Render.RcptP.S_c1, ZkFormal.Near.Render.RcptP.S_c2, ZkFormal.Near.Render.RcptP.S_c3, ZkFormal.Near.Render.RcptP.S_c4, ZkFormal.Near.Render.RcptP.S_burnt, ZkFormal.Near.Render.RcptP.S_ramt, ZkFormal.Near.Render.RcptP.S_sumD, ZkFormal.Near.Render.RcptP.S_invA, ZkFormal.Near.Render.RcptP.S_bef, ZkFormal.Near.Render.RcptP.S_lk, ZkFormal.Near.Render.RcptP.S_st, ZkFormal.Near.Render.RcptP.S_dsum, ZkFormal.Near.Render.RcptP.S_invB, ZkFormal.Near.Render.RcptP.S_dI, ZkFormal.Near.Render.RcptP.S_dL, ZkFormal.Near.Render.RcptP.S_gDg, ZkFormal.Near.Render.RcptP.S_reg, ZkFormal.Near.Render.RcptP.S_tok, ZkFormal.Near.Render.RcptP.S_xb, ZkFormal.Near.Render.RcptP.S_lb, ZkFormal.Near.Render.RcptP.S_dl, evR_c, evR_k, evR_sub, evR_add, evR_smul]
  all_goals (try split)
  all_goals first
    | (simp only [ofNat0]; grind)
    | (rename_i h; subst h; simp only [fLen, ↓reduceIte, Nat.reduceEqDiff] at hfe
       first
       | (rw [show i = 0 by omega]; simp only [ofNat0, ofNat1, natCast_eq]; grind)
       | (rw [← hfe]; simp only [ofNat_add_e, ofNat1, natCast_eq]; grind)
       | (obtain ⟨k, hk⟩ : ∃ k, i = k := ⟨i, rfl⟩
          rw [show i = 31 + 32 * (Df c e r).kt by omega]
          simp only [ofNat_add_e, ofNat_mul_e, natCast_eq]; grind)
       | (rw [show i = fLen (Df c e r) _ - 1 by simp only [fLen, ↓reduceIte, Nat.reduceEqDiff]; omega]
          simp only [fLen, ↓reduceIte, Nat.reduceEqDiff, natCast_eq]; grind))

theorem Cc_four {c : Claim} {e : Ext} {r s i : Nat} : Cc c e (.seg r s i) 4 = 0 := S_sCL c e r s i

theorem Cc_hr55 {c : Claim} {e : Ext} {r s i : Nat} : Cc c e (.seg r s i) 55 = b2n (Df c e r).hr := S_hr c e r s i

/-- Successions on a field's last row, next row the next field's first row. -/
theorem sF_fe {c : Claim} {e : Ext} {r s i : Nat} (hfe : i + 1 = fLen (Df c e r) s) {nx : Nat → Fp}
    (hn : ∀ st, 5 ≤ st → st ≤ 26 → nx st = if st = nextF (Df c e r).hr s then 1 else 0)
    {fst lst : Bool} {pub : List Fp} : ∀ x ∈ sF, evR (cF c e (.seg r s i)) nx fst lst pub x = 0 := by
  intro x hx
  simp only [sF, List.mem_map] at hx
  obtain ⟨⟨st, st', g⟩, hmem, rfl⟩ := hx
  simp only [evR_mul, evR_mul3, evR_c, evR_not, evR_n, fe1 hfe]
  simp only [Rcpt.succ, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals simp only [Rcpt.act, Rcpt.rf, Rcpt.rl, Rcpt.lastR, Rcpt.sCL, Rcpt.sPL, Rcpt.sP, Rcpt.sVL, Rcpt.sV, Rcpt.sRID, Rcpt.sT0, Rcpt.sSL, Rcpt.sS, Rcpt.sKT, Rcpt.sPK, Rcpt.sGP, Rcpt.sTL, Rcpt.sDEP, Rcpt.sXP0, Rcpt.sXRI, Rcpt.sXG, Rcpt.sXST, Rcpt.sXL0, Rcpt.sXLH, Rcpt.sXRH, Rcpt.sXRF, Rcpt.sXRZ, Rcpt.idx, Rcpt.fs, Rcpt.fe, Rcpt.b, Rcpt.e1Id, Rcpt.e1Pos, Rcpt.e1V, Rcpt.e1G, Rcpt.e2Id, Rcpt.e2Pos, Rcpt.e2V, Rcpt.e2G, Rcpt.e3Id, Rcpt.e3Pos, Rcpt.e3V, Rcpt.e3G, Rcpt.tA, Rcpt.symA, Rcpt.lastA, Rcpt.gKA, Rcpt.kz, Rcpt.r, Rcpt.o, Rcpt.o2, Rcpt.Lp, Rcpt.Lv, Rcpt.Ls, Rcpt.kt, Rcpt.hr, Rcpt.kslot, Rcpt.tprev, Rcpt.rcnt, Rcpt.ge, Rcpt.big, Rcpt.oEnd, Rcpt.o2End, Rcpt.reg, Rcpt.tok, Rcpt.h2, Rcpt.h3, Rcpt.h5, Rcpt.h6, Rcpt.h7, Rcpt.lb, Rcpt.z, Rcpt.linv, Rcpt.l210, Rcpt.hx6, Rcpt.acc, Rcpt.vc0, Rcpt.vc1, Rcpt.h01, Rcpt.p1, Rcpt.p2, Rcpt.p3, Rcpt.i1, Rcpt.i2, Rcpt.i3, Rcpt.isys, Rcpt.r1, Rcpt.lo8, Rcpt.lo4, Rcpt.xb, Rcpt.c1, Rcpt.c2, Rcpt.c3, Rcpt.c4, Rcpt.dl, Rcpt.burnt, Rcpt.ramt, Rcpt.sumD, Rcpt.invA, Rcpt.bef, Rcpt.lk, Rcpt.st, Rcpt.dsum, Rcpt.invB, Rcpt.dI, Rcpt.dL, Rcpt.gDg, Rcpt.width]
  all_goals rw [hn _ (by decide) (by decide)]
  all_goals simp (disch := decide) only [cF, Cc_state, Cc_four, Cc_hr55, evR_c, evR_k, evR_not, ofNat0]
  all_goals first
    | grind
    | (split
       · rename_i h; subst h
         cases (Df c e r).hr <;> simp [nextF, b2n, ofNat0, ofNat1] <;> grind
       · simp only [ofNat0]; grind)

/-- Successions on a receipt's last row. -/
theorem sF_rl {c : Claim} {e : Ext} {r s i : Nat} (hfe : i + 1 = fLen (Df c e r) s)
    (hrl : isRl (Df c e r) s i = true) {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} :
    ∀ x ∈ sF, evR (cF c e (.seg r s i)) nx fst lst pub x = 0 := by
  have h2 : s = 26 ∨ (s = 23 ∧ (Df c e r).hr = false) := by
    unfold isRl at hrl
    cases hh : (Df c e r).hr <;> simp [hh] at hrl ⊢ <;> omega
  intro x hx
  simp only [sF, List.mem_map] at hx
  obtain ⟨⟨st, st', g⟩, hmem, rfl⟩ := hx
  simp only [evR_mul, evR_mul3, evR_c, evR_not, evR_n, fe1 hfe]
  simp only [Rcpt.succ, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals simp only [cF, ZkFormal.Near.Render.RcptP.b2n_true, ZkFormal.Near.Render.RcptP.b2n_false, ZkFormal.Near.Render.RcptP.S_act, ZkFormal.Near.Render.RcptP.S_rf, ZkFormal.Near.Render.RcptP.S_rl, ZkFormal.Near.Render.RcptP.S_lastR, ZkFormal.Near.Render.RcptP.S_sCL, ZkFormal.Near.Render.RcptP.S_sPL, ZkFormal.Near.Render.RcptP.S_sP, ZkFormal.Near.Render.RcptP.S_sVL, ZkFormal.Near.Render.RcptP.S_sV, ZkFormal.Near.Render.RcptP.S_sRID, ZkFormal.Near.Render.RcptP.S_sT0, ZkFormal.Near.Render.RcptP.S_sSL, ZkFormal.Near.Render.RcptP.S_sS, ZkFormal.Near.Render.RcptP.S_sKT, ZkFormal.Near.Render.RcptP.S_sPK, ZkFormal.Near.Render.RcptP.S_sGP, ZkFormal.Near.Render.RcptP.S_sTL, ZkFormal.Near.Render.RcptP.S_sDEP, ZkFormal.Near.Render.RcptP.S_sXP0, ZkFormal.Near.Render.RcptP.S_sXRI, ZkFormal.Near.Render.RcptP.S_sXG, ZkFormal.Near.Render.RcptP.S_sXST, ZkFormal.Near.Render.RcptP.S_sXL0, ZkFormal.Near.Render.RcptP.S_sXLH, ZkFormal.Near.Render.RcptP.S_sXRH, ZkFormal.Near.Render.RcptP.S_sXRF, ZkFormal.Near.Render.RcptP.S_sXRZ, ZkFormal.Near.Render.RcptP.S_idx, ZkFormal.Near.Render.RcptP.S_fs, ZkFormal.Near.Render.RcptP.S_fe, ZkFormal.Near.Render.RcptP.S_b, ZkFormal.Near.Render.RcptP.S_tA, ZkFormal.Near.Render.RcptP.S_symA, ZkFormal.Near.Render.RcptP.S_lastA, ZkFormal.Near.Render.RcptP.S_gKA, ZkFormal.Near.Render.RcptP.S_kz, ZkFormal.Near.Render.RcptP.S_r, ZkFormal.Near.Render.RcptP.S_o, ZkFormal.Near.Render.RcptP.S_o2, ZkFormal.Near.Render.RcptP.S_Lp, ZkFormal.Near.Render.RcptP.S_Lv, ZkFormal.Near.Render.RcptP.S_Ls, ZkFormal.Near.Render.RcptP.S_kt, ZkFormal.Near.Render.RcptP.S_hr, ZkFormal.Near.Render.RcptP.S_kslot, ZkFormal.Near.Render.RcptP.S_tprev, ZkFormal.Near.Render.RcptP.S_rcnt, ZkFormal.Near.Render.RcptP.S_ge, ZkFormal.Near.Render.RcptP.S_big, ZkFormal.Near.Render.RcptP.S_oEnd, ZkFormal.Near.Render.RcptP.S_o2End, ZkFormal.Near.Render.RcptP.S_h2, ZkFormal.Near.Render.RcptP.S_h3, ZkFormal.Near.Render.RcptP.S_h5, ZkFormal.Near.Render.RcptP.S_h6, ZkFormal.Near.Render.RcptP.S_h7, ZkFormal.Near.Render.RcptP.S_z, ZkFormal.Near.Render.RcptP.S_linv, ZkFormal.Near.Render.RcptP.S_l210, ZkFormal.Near.Render.RcptP.S_hx6, ZkFormal.Near.Render.RcptP.S_acc, ZkFormal.Near.Render.RcptP.S_vc0, ZkFormal.Near.Render.RcptP.S_vc1, ZkFormal.Near.Render.RcptP.S_h01, ZkFormal.Near.Render.RcptP.S_p1, ZkFormal.Near.Render.RcptP.S_p2, ZkFormal.Near.Render.RcptP.S_p3, ZkFormal.Near.Render.RcptP.S_i1, ZkFormal.Near.Render.RcptP.S_i2, ZkFormal.Near.Render.RcptP.S_i3, ZkFormal.Near.Render.RcptP.S_isys, ZkFormal.Near.Render.RcptP.S_r1, ZkFormal.Near.Render.RcptP.S_lo8, ZkFormal.Near.Render.RcptP.S_lo4, ZkFormal.Near.Render.RcptP.S_c1, ZkFormal.Near.Render.RcptP.S_c2, ZkFormal.Near.Render.RcptP.S_c3, ZkFormal.Near.Render.RcptP.S_c4, ZkFormal.Near.Render.RcptP.S_burnt, ZkFormal.Near.Render.RcptP.S_ramt, ZkFormal.Near.Render.RcptP.S_sumD, ZkFormal.Near.Render.RcptP.S_invA, ZkFormal.Near.Render.RcptP.S_bef, ZkFormal.Near.Render.RcptP.S_lk, ZkFormal.Near.Render.RcptP.S_st, ZkFormal.Near.Render.RcptP.S_dsum, ZkFormal.Near.Render.RcptP.S_invB, ZkFormal.Near.Render.RcptP.S_dI, ZkFormal.Near.Render.RcptP.S_dL, ZkFormal.Near.Render.RcptP.S_gDg, ZkFormal.Near.Render.RcptP.S_reg, ZkFormal.Near.Render.RcptP.S_tok, ZkFormal.Near.Render.RcptP.S_xb, ZkFormal.Near.Render.RcptP.S_lb, ZkFormal.Near.Render.RcptP.S_dl, evR_c, evR_k, evR_not]
  all_goals first
    | (split
       · rename_i h; rcases h2 with h2 | ⟨h2, h3⟩
         · omega
         · first | omega | (simp only [h3, b2n_false, ofNat0]; grind)
       · simp only [ofNat0]; grind)
    | (simp only [ofNat0]; grind)

end RcptP

end ZkFormal.Near.Render
