import ZkFormal.NearV3.Render.Ups.CompactExtract.MveBytes
import ZkFormal.NearV3.Extract.Ups.SpbRows
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {C D : URow} (ok : RowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

set_option maxHeartbeats 2000000 in
/-- **The part constants of a split branch**, by case. -/
theorem head_SPB {ci : Nat} (hpf : C pf = 1) (hk : ∀ m, m < 12 → C (kcol m) = if m = 10 then 1 else 0)
    (hcs : ∀ m, m < 11 → C (17 + m) = if m = ci then 1 else 0) (h4 : 4 ≤ ci) (h10 : ci ≤ 10) :
    C qtl = 0 ∧ C qte = 0 ∧ C qtb2 = spVN ci ∧ C nochild = 0 ∧
    C xcp = spXN ci ∧ C vcp = (if ci = 4 then 1 else 0) ∧ C useA = spXN ci ∧ C bN = spRN ci ∧ C bL = 0 ∧
    C cO = 0 ∧ C cS = 0 ∧ (spXN ci = 0 → C Cc = 0) ∧ (C phk < 2 ^ 23 → C Cc = spXN ci * (50 + 2 * C phk)) ∧ C eL = 1 ∧
    C eS = (if ci = 4 then 1 else 0) ∧ C Kc = spKc ci ∧ (spRN ci = 1 → C jm = 1) := by
  have k0 : C kRDB = 0 := hk 0 (by omega)
  have k1 : C kRDE = 0 := hk 1 (by omega)
  have k2 : C kRLP = 0 := hk 2 (by omega)
  have k3 : C kRBR = 0 := hk 3 (by omega)
  have k4 : C kRBV = 0 := hk 4 (by omega)
  have k5 : C kRBI = 0 := hk 5 (by omega)
  have k6 : C kMVL = 0 := hk 6 (by omega)
  have k7 : C kMVE = 0 := hk 7 (by omega)
  have k8 : C kNLF = 0 := hk 8 (by omega)
  have k9 : C kWEX = 0 := hk 9 (by omega)
  have k10 : C kSPB = 1 := hk 10 (by omega)
  have k11 : C kPT = 0 := hk 11 (by omega)
  have c4 : C cLSa = if 4 = ci then 1 else 0 := hcs 4 (by omega)
  have c5 : C cLSb = if 5 = ci then 1 else 0 := hcs 5 (by omega)
  have c6 : C cLSc = if 6 = ci then 1 else 0 := hcs 6 (by omega)
  have c7 : C cESl0 = if 7 = ci then 1 else 0 := hcs 7 (by omega)
  have c8 : C cESl1 = if 8 = ci then 1 else 0 := hcs 8 (by omega)
  have c9 : C cESn0 = if 9 = ci then 1 else 0 := hcs 9 (by omega)
  have c10 : C cESn1 = if 10 = ci then 1 else 0 := hcs 10 (by omega)
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a xcp; have := a vcp; have := a qtl; have := a qte; have := a qtb2; have := a nochild; have := a jm
  have := a useA; have := a bN; have := a bL; have := a cO; have := a cS; have := a Cc; have := a eL; have := a eS
  have := a Kc; have := a phk
  have bq1 := partBoolN ok hC hpf (x := qtl) (by decide)
  have bq2 := partBoolN ok hC hpf (x := qte) (by decide)
  have bx := partBoolN ok hC hpf (x := xcp) (by decide)
  have fx := factN ok hC hD (e := .mul (c pf) (sub (c xcp) (.mul (c kSPB) (.add (c cESl1) (c cESn1))))) (memPlan (by simp [cPlan]))
  have fv := factN ok hC hD (e := .mul (c pf) (sub (c vcp) (sum [c kRDB, c kRBI, c kMVL, .mul (c kSPB) (c cLSa)]))) (memPlan (by simp [cPlan]))
  have t1 := factN ok hC hD (e := .mul (c pf) (.mul (c kSPB) (.add (c qtl) (c qte)))) (memPlan (by simp [cPlan]))
  have t2 := factN ok hC hD (e := .mul (c pf) (.mul (c kSPB) (sub (c qtb2) spValE))) (memPlan (by simp [cPlan]))
  have t3 := factN ok hC hD (e := .mul (c pf) (.mul (c kSPB) (c nochild))) (memPlan (by simp [cPlan]))
  have t4 := factN ok hC hD (e := mul3 (c pf) (c kSPB) (.mul spRecvE (sub (c jm) (k 1)))) (memPlan (by simp [cPlan]))
  have m1 := factN ok hC hD (e := .mul (c pf) (sub (c useA) (sum [c kRDB, c kRDE, c kRBR, c kRBV, c kRBI, c kMVE, c xcp, c kPT]))) (memPlan (by simp [cPlan]))
  have m2 := factN ok hC hD (e := .mul (c pf) (sub (c bN) (sum [c kRDB, c kRDE, c kWEX, .mul (c kSPB) spRecvE, c kPT]))) (memPlan (by simp [cPlan]))
  have m3 := factN ok hC hD (e := .mul (c pf) (sub (c bL) (c kRBR))) (memPlan (by simp [cPlan]))
  have m4 := factN ok hC hD (e := .mul (c pf) (sub (c cO) (.add kRD (c kPT)))) (memPlan (by simp [cPlan]))
  have m5 := factN ok hC hD (e := .mul (c pf) (sub (c cS) (c kRBR))) (memPlan (by simp [cPlan]))
  have m6 := factN ok hC hD (e := .mul (c pf) (sub (c Cc) (.mul (.add (c kMVE) (c xcp)) (.add (k 50) (smul 2 (c phk)))))) (memPlan (by simp [cPlan]))
  have m7 := factN ok hC hD (e := .mul (c pf) (sub (c eL) (sum [c kRLP, c kRBV, c kRBI, c kNLF, c kSPB]))) (memPlan (by simp [cPlan]))
  have m8 := factN ok hC hD (e := .mul (c pf) (sub (c eS) (.add (c kMVL) (.mul (c kSPB) (c cLSa))))) (memPlan (by simp [cPlan]))
  have m9 := factN ok hC hD (e := .mul (c pf) (sub (c Kc) (sum [
      .mul (c kRLP) (.add (k 100) (smul 2 (c qhk))), smul 50 (c kRBV), smul 102 (c kRBI),
      .mul (c kMVL) (.add (k 100) (smul 2 (c qhk))), .mul (c kMVE) (.add (k 50) (smul 2 (c qhk))),
      smul 102 (c kNLF), .mul (c kWEX) (.add (k 50) (smul 2 (c qhk))),
      .mul (c kSPB) (sum [smul 202 (c cLSa), smul 100 (sumc [cLSb, cESl0, cESl1]),
        smul 152 (sumc [cLSc, cESn0, cESn1])])]))) (memPlan (by simp [cPlan]))
  simp only [sumc, List.map_cons, List.map_nil, kRD, spRecvE, spValE] at fx fv t1 t2 t3 t4 m1 m2 m3 m4 m5 m6 m7 m8 m9
  nev_simp at fx fv t1 t2 t3 t4 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp only [hpf, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, c4, c5, c6, c7, c8, c9, c10] at fx fv t1 t2 t3 t4 m1 m2 m3 m4 m5 m6 m7 m8 m9
  rcases (show ci = 4 ∨ ci = 5 ∨ ci = 6 ∨ ci = 7 ∨ ci = 8 ∨ ci = 9 ∨ ci = 10 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [spVN, spRN, spXN, spKc] at fx fv t1 t2 t3 t4 m1 m2 m3 m4 m5 m6 m7 m8 m9 ⊢ <;>
  rcases (show C xcp = 0 ∨ C xcp = 1 by omega) with hx | hx <;> simp [hx] at m6 ⊢ <;>
  omega

set_option maxHeartbeats 2000000 in
/-- **The split bitmap** (on `W0`). -/
theorem spbSeg {ci si : Nat} (hsf : C sf = 1) (hcs : ∀ m, m < 11 → C (17 + m) = if m = ci then 1 else 0)
    (hts : ∀ m, m < 3 → C (31 + m) = if m = si then 1 else 0) (h4 : 4 ≤ ci) (h10 : ci ≤ 10) (hsi : si < 3) :
    C tX < 16 ∧ C bmL = spBm ci (C tX) si % 256 ∧ C bmH = spBm ci (C tX) si / 256 ∧ (spYN ci = 1 → si ≤ 1) := by
  have c3 : C cBI = 0 := by have := hcs 3 (by omega); rw [if_neg (by omega)] at this; exact this
  have c4 : C cLSa = if 4 = ci then 1 else 0 := hcs 4 (by omega)
  have c6 : C cLSc = if 6 = ci then 1 else 0 := hcs 6 (by omega)
  have c9 : C cESn0 = if 9 = ci then 1 else 0 := hcs 9 (by omega)
  have c10 : C cESn1 = if 10 = ci then 1 else 0 := hcs 10 (by omega)
  have s1 : C ts1 = if 0 = si then 1 else 0 := hts 0 (by omega)
  have s3 : C ts3 = if 2 = si then 1 else 0 := hts 2 (by omega)
  have xb0 := segBool ok hC hsf (x := xb 0) (by decide)
  have xb1 := segBool ok hC hsf (x := xb 1) (by decide)
  have xb2 := segBool ok hC hsf (x := xb 2) (by decide)
  have xb3 := segBool ok hC hsf (x := xb 3) (by decide)
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a tX; have := a px; have := a bmL; have := a bmH
  have f1 := factN ok hC hD (e := .mul (c sf) (sub (c tX) (bits (fun i => c (xb i)) 0 4))) (memSeg (by simp [cSeg]))
  have f2 := factN ok hC hD (e := .mul (c sf) (sub (c px) (mul3 (.add (k 1) (c (xb 0))) (.add (k 1) (smul 3 (c (xb 1))))
      (.add (k 1) (smul 15 (c (xb 2))))))) (memSeg (by simp [cSeg]))
  have f3 := factN ok hC hD (e := .mul (c sf) (sub (c bmL) (.add (mul3 (not (c cLSa)) (not (c (xb 3))) (c px))
      (.mul spYE (c ts1))))) (memSeg (by simp [cSeg]))
  have f4 := factN ok hC hD (e := .mul (c sf) (sub (c bmH) (.add (mul3 (not (c cLSa)) (c (xb 3)) (c px))
      (smul 128 (.mul spYE (not (c ts1))))))) (memSeg (by simp [cSeg]))
  have f5 := factN ok hC hD (e := mul3 (c sf) (c ts3) (sumc [cBI, cLSa, cLSc, cESn0, cESn1])) (memSeg (by simp [cSeg]))
  simp only [sumc, spYE, List.map_cons, List.map_nil] at f3 f4 f5
  simp only [Dsl.bits, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.singleton_append] at f1
  nev_simp at f1 f2 f3 f4 f5
  simp only [hsf, c3, c4, c6, c9, c10, s1, s3] at f1 f2 f3 f4 f5
  -- the nibble and `px = 2^(x mod 8)`
  obtain ⟨hx, hp⟩ : C tX = C (xb 0) + 2 * C (xb 1) + 4 * C (xb 2) + 8 * C (xb 3) ∧
      C px = 2 ^ (C (xb 0) + 2 * C (xb 1) + 4 * C (xb 2)) := by
    rcases (show C (xb 0) = 0 ∨ C (xb 0) = 1 by omega) with h0 | h0 <;>
    rcases (show C (xb 1) = 0 ∨ C (xb 1) = 1 by omega) with h1 | h1 <;>
    rcases (show C (xb 2) = 0 ∨ C (xb 2) = 1 by omega) with h2 | h2 <;>
    rcases (show C (xb 3) = 0 ∨ C (xb 3) = 1 by omega) with h3 | h3 <;>
    simp [h0, h1, h2, h3] at f1 f2 ⊢ <;> omega
  have hp8 : C px ≤ 128 ∧ 1 ≤ C px := by
    rw [hp]
    rcases (show C (xb 0) = 0 ∨ C (xb 0) = 1 by omega) with h0 | h0 <;>
    rcases (show C (xb 1) = 0 ∨ C (xb 1) = 1 by omega) with h1 | h1 <;>
    rcases (show C (xb 2) = 0 ∨ C (xb 2) = 1 by omega) with h2 | h2 <;> simp [h0, h1, h2]
  have h2x : 2 ^ C tX = 2 ^ (8 * C (xb 3)) * C px := by
    rw [hx, hp, ← Nat.pow_add]; congr 1; omega
  refine ⟨by omega, ?_⟩
  have hy : ∀ si, si < 2 → UpsSpec.yOf si = if si = 0 then 0 else 15 := by decide
  rcases (show ci = 4 ∨ ci = 5 ∨ ci = 6 ∨ ci = 7 ∨ ci = 8 ∨ ci = 9 ∨ ci = 10 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases (show si = 0 ∨ si = 1 ∨ si = 2 by omega) with rfl | rfl | rfl <;>
  rcases (show C (xb 3) = 0 ∨ C (xb 3) = 1 by omega) with h3 | h3 <;>
  simp [h3, spBm, spYN, UpsSpec.yOf, UpsSpec.key] at f3 f4 f5 h2x ⊢ <;>
  omega

end

end ZkFormal.NearV3.Render.UpsRelay.Extract
