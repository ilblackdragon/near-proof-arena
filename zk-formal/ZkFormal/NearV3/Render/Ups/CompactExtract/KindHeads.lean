import ZkFormal.NearV3.Render.Ups.CompactExtract.PlanRows
import ZkFormal.NearV3.Extract.Ups.KindHeads
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {C D : URow} (ok : RowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

theorem head_RDB (hpf : C pf = 1) (hk : ∀ m, m < 12 → C (kcol m) = if m = 0 then 1 else 0) :
    C xcp = 0 ∧
    C vcp = 1 ∧
    C qtl = 0 ∧
    C qte = 0 ∧
    C useA = 1 ∧
    C bN = 1 ∧
    C bL = 0 ∧
    C cO = 1 ∧
    C cS = 0 ∧
    C Cc = 0 ∧
    C eL = 0 ∧
    C eS = 0 ∧
    C Kc = 0 := by
  have k0 : C kRDB = 1 := hk 0 (by omega)
  have k1 : C kRDE = 0 := hk 1 (by omega)
  have k2 : C kRLP = 0 := hk 2 (by omega)
  have k3 : C kRBR = 0 := hk 3 (by omega)
  have k4 : C kRBV = 0 := hk 4 (by omega)
  have k5 : C kRBI = 0 := hk 5 (by omega)
  have k6 : C kMVL = 0 := hk 6 (by omega)
  have k7 : C kMVE = 0 := hk 7 (by omega)
  have k8 : C kNLF = 0 := hk 8 (by omega)
  have k9 : C kWEX = 0 := hk 9 (by omega)
  have k10 : C kSPB = 0 := hk 10 (by omega)
  have k11 : C kPT = 0 := hk 11 (by omega)
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a xcp; have := a vcp; have := a qtl; have := a qte; have := a qtb2; have := a nokey; have := a qodd; have := a qhk; have := a useA; have := a bN; have := a bL; have := a cO; have := a cS; have := a Cc; have := a eL; have := a eS; have := a Kc; have := a phk; have := a cESl1; have := a cESn1; have := a cLSa
  have := partBoolN ok hC hpf (x := qtl) (by decide); have := partBoolN ok hC hpf (x := qte) (by decide)
  have := partBoolN ok hC hpf (x := nokey) (by decide)
  have hx0 : C xcp = 0 := by
    have fx := factN ok hC hD (e := .mul (c pf) (sub (c xcp) (.mul (c kSPB) (.add (c cESl1) (c cESn1))))) (memPlan (by simp [cPlan]))
    nev_simp at fx; simp only [hpf, k10] at fx; simp at fx; omega
  have fv := factN ok hC hD (e := .mul (c pf) (sub (c vcp) (sum [c kRDB, c kRBI, c kMVL, .mul (c kSPB) (c cLSa)]))) (memPlan (by simp [cPlan]))
  have t1 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDB, kRBR, kRBI]) (.add (c qtl) (c qte)))) (memPlan (by simp [cPlan]))
  have t2 := factN ok hC hD (e := .mul (c pf) (.mul (.add (c kRBR) (c kRBV)) (not (c qtb2)))) (memPlan (by simp [cPlan]))
  have t3 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDE, kMVE, kWEX, kPT]) (not (c qte)))) (memPlan (by simp [cPlan]))
  have t4 := factN ok hC hD (e := mul3 (c pf) (c kPT) (not (c nokey))) (memPlan (by simp [cPlan]))
  have t5 := factN ok hC hD (e := mul3 (c pf) (c kPT) (c qodd)) (memPlan (by simp [cPlan]))
  have t6 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRLP, kMVL, kNLF]) (not (c qtl)))) (memPlan (by simp [cPlan]))
  have t7 := factN ok hC hD (e := .mul (c pf) (.mul (c nokey) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
  have t8 := factN ok hC hD (e := .mul (c pf) (.mul (c kNLF) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
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
  simp only [sumc, List.map_cons, List.map_nil, kRD, spRecvE] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  nev_simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp only [hpf, hx0, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  refine ⟨hx0, ?_⟩
  omega

theorem head_RDE (hpf : C pf = 1) (hk : ∀ m, m < 12 → C (kcol m) = if m = 1 then 1 else 0) :
    C xcp = 0 ∧
    C vcp = 0 ∧
    C qte = 1 ∧
    C useA = 1 ∧
    C bN = 1 ∧
    C bL = 0 ∧
    C cO = 1 ∧
    C cS = 0 ∧
    C Cc = 0 ∧
    C eL = 0 ∧
    C eS = 0 ∧
    C Kc = 0 := by
  have k0 : C kRDB = 0 := hk 0 (by omega)
  have k1 : C kRDE = 1 := hk 1 (by omega)
  have k2 : C kRLP = 0 := hk 2 (by omega)
  have k3 : C kRBR = 0 := hk 3 (by omega)
  have k4 : C kRBV = 0 := hk 4 (by omega)
  have k5 : C kRBI = 0 := hk 5 (by omega)
  have k6 : C kMVL = 0 := hk 6 (by omega)
  have k7 : C kMVE = 0 := hk 7 (by omega)
  have k8 : C kNLF = 0 := hk 8 (by omega)
  have k9 : C kWEX = 0 := hk 9 (by omega)
  have k10 : C kSPB = 0 := hk 10 (by omega)
  have k11 : C kPT = 0 := hk 11 (by omega)
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a xcp; have := a vcp; have := a qtl; have := a qte; have := a qtb2; have := a nokey; have := a qodd; have := a qhk; have := a useA; have := a bN; have := a bL; have := a cO; have := a cS; have := a Cc; have := a eL; have := a eS; have := a Kc; have := a phk; have := a cESl1; have := a cESn1; have := a cLSa
  have := partBoolN ok hC hpf (x := qtl) (by decide); have := partBoolN ok hC hpf (x := qte) (by decide)
  have := partBoolN ok hC hpf (x := nokey) (by decide)
  have hx0 : C xcp = 0 := by
    have fx := factN ok hC hD (e := .mul (c pf) (sub (c xcp) (.mul (c kSPB) (.add (c cESl1) (c cESn1))))) (memPlan (by simp [cPlan]))
    nev_simp at fx; simp only [hpf, k10] at fx; simp at fx; omega
  have fv := factN ok hC hD (e := .mul (c pf) (sub (c vcp) (sum [c kRDB, c kRBI, c kMVL, .mul (c kSPB) (c cLSa)]))) (memPlan (by simp [cPlan]))
  have t1 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDB, kRBR, kRBI]) (.add (c qtl) (c qte)))) (memPlan (by simp [cPlan]))
  have t2 := factN ok hC hD (e := .mul (c pf) (.mul (.add (c kRBR) (c kRBV)) (not (c qtb2)))) (memPlan (by simp [cPlan]))
  have t3 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDE, kMVE, kWEX, kPT]) (not (c qte)))) (memPlan (by simp [cPlan]))
  have t4 := factN ok hC hD (e := mul3 (c pf) (c kPT) (not (c nokey))) (memPlan (by simp [cPlan]))
  have t5 := factN ok hC hD (e := mul3 (c pf) (c kPT) (c qodd)) (memPlan (by simp [cPlan]))
  have t6 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRLP, kMVL, kNLF]) (not (c qtl)))) (memPlan (by simp [cPlan]))
  have t7 := factN ok hC hD (e := .mul (c pf) (.mul (c nokey) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
  have t8 := factN ok hC hD (e := .mul (c pf) (.mul (c kNLF) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
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
  simp only [sumc, List.map_cons, List.map_nil, kRD, spRecvE] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  nev_simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp only [hpf, hx0, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  refine ⟨hx0, ?_⟩
  omega

theorem head_RLP (hpf : C pf = 1) (hk : ∀ m, m < 12 → C (kcol m) = if m = 2 then 1 else 0) :
    C xcp = 0 ∧
    C vcp = 0 ∧
    C qtl = 1 ∧
    C useA = 0 ∧
    C bN = 0 ∧
    C bL = 0 ∧
    C cO = 0 ∧
    C cS = 0 ∧
    C Cc = 0 ∧
    C eL = 1 ∧
    C eS = 0 ∧
    (C qhk < 2 ^ 23 → C Kc = 100 + 2 * C qhk) := by
  have k0 : C kRDB = 0 := hk 0 (by omega)
  have k1 : C kRDE = 0 := hk 1 (by omega)
  have k2 : C kRLP = 1 := hk 2 (by omega)
  have k3 : C kRBR = 0 := hk 3 (by omega)
  have k4 : C kRBV = 0 := hk 4 (by omega)
  have k5 : C kRBI = 0 := hk 5 (by omega)
  have k6 : C kMVL = 0 := hk 6 (by omega)
  have k7 : C kMVE = 0 := hk 7 (by omega)
  have k8 : C kNLF = 0 := hk 8 (by omega)
  have k9 : C kWEX = 0 := hk 9 (by omega)
  have k10 : C kSPB = 0 := hk 10 (by omega)
  have k11 : C kPT = 0 := hk 11 (by omega)
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a xcp; have := a vcp; have := a qtl; have := a qte; have := a qtb2; have := a nokey; have := a qodd; have := a qhk; have := a useA; have := a bN; have := a bL; have := a cO; have := a cS; have := a Cc; have := a eL; have := a eS; have := a Kc; have := a phk; have := a cESl1; have := a cESn1; have := a cLSa
  have := partBoolN ok hC hpf (x := qtl) (by decide); have := partBoolN ok hC hpf (x := qte) (by decide)
  have := partBoolN ok hC hpf (x := nokey) (by decide)
  have hx0 : C xcp = 0 := by
    have fx := factN ok hC hD (e := .mul (c pf) (sub (c xcp) (.mul (c kSPB) (.add (c cESl1) (c cESn1))))) (memPlan (by simp [cPlan]))
    nev_simp at fx; simp only [hpf, k10] at fx; simp at fx; omega
  have fv := factN ok hC hD (e := .mul (c pf) (sub (c vcp) (sum [c kRDB, c kRBI, c kMVL, .mul (c kSPB) (c cLSa)]))) (memPlan (by simp [cPlan]))
  have t1 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDB, kRBR, kRBI]) (.add (c qtl) (c qte)))) (memPlan (by simp [cPlan]))
  have t2 := factN ok hC hD (e := .mul (c pf) (.mul (.add (c kRBR) (c kRBV)) (not (c qtb2)))) (memPlan (by simp [cPlan]))
  have t3 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDE, kMVE, kWEX, kPT]) (not (c qte)))) (memPlan (by simp [cPlan]))
  have t4 := factN ok hC hD (e := mul3 (c pf) (c kPT) (not (c nokey))) (memPlan (by simp [cPlan]))
  have t5 := factN ok hC hD (e := mul3 (c pf) (c kPT) (c qodd)) (memPlan (by simp [cPlan]))
  have t6 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRLP, kMVL, kNLF]) (not (c qtl)))) (memPlan (by simp [cPlan]))
  have t7 := factN ok hC hD (e := .mul (c pf) (.mul (c nokey) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
  have t8 := factN ok hC hD (e := .mul (c pf) (.mul (c kNLF) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
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
  simp only [sumc, List.map_cons, List.map_nil, kRD, spRecvE] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  nev_simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp only [hpf, hx0, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  refine ⟨hx0, ?_⟩
  omega

theorem head_RBR (hpf : C pf = 1) (hk : ∀ m, m < 12 → C (kcol m) = if m = 3 then 1 else 0) :
    C xcp = 0 ∧
    C vcp = 0 ∧
    C qtl = 0 ∧
    C qte = 0 ∧
    C qtb2 = 1 ∧
    C useA = 1 ∧
    C bN = 0 ∧
    C bL = 1 ∧
    C cO = 0 ∧
    C cS = 1 ∧
    C Cc = 0 ∧
    C eL = 0 ∧
    C eS = 0 ∧
    C Kc = 0 := by
  have k0 : C kRDB = 0 := hk 0 (by omega)
  have k1 : C kRDE = 0 := hk 1 (by omega)
  have k2 : C kRLP = 0 := hk 2 (by omega)
  have k3 : C kRBR = 1 := hk 3 (by omega)
  have k4 : C kRBV = 0 := hk 4 (by omega)
  have k5 : C kRBI = 0 := hk 5 (by omega)
  have k6 : C kMVL = 0 := hk 6 (by omega)
  have k7 : C kMVE = 0 := hk 7 (by omega)
  have k8 : C kNLF = 0 := hk 8 (by omega)
  have k9 : C kWEX = 0 := hk 9 (by omega)
  have k10 : C kSPB = 0 := hk 10 (by omega)
  have k11 : C kPT = 0 := hk 11 (by omega)
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a xcp; have := a vcp; have := a qtl; have := a qte; have := a qtb2; have := a nokey; have := a qodd; have := a qhk; have := a useA; have := a bN; have := a bL; have := a cO; have := a cS; have := a Cc; have := a eL; have := a eS; have := a Kc; have := a phk; have := a cESl1; have := a cESn1; have := a cLSa
  have := partBoolN ok hC hpf (x := qtl) (by decide); have := partBoolN ok hC hpf (x := qte) (by decide)
  have := partBoolN ok hC hpf (x := nokey) (by decide)
  have hx0 : C xcp = 0 := by
    have fx := factN ok hC hD (e := .mul (c pf) (sub (c xcp) (.mul (c kSPB) (.add (c cESl1) (c cESn1))))) (memPlan (by simp [cPlan]))
    nev_simp at fx; simp only [hpf, k10] at fx; simp at fx; omega
  have fv := factN ok hC hD (e := .mul (c pf) (sub (c vcp) (sum [c kRDB, c kRBI, c kMVL, .mul (c kSPB) (c cLSa)]))) (memPlan (by simp [cPlan]))
  have t1 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDB, kRBR, kRBI]) (.add (c qtl) (c qte)))) (memPlan (by simp [cPlan]))
  have t2 := factN ok hC hD (e := .mul (c pf) (.mul (.add (c kRBR) (c kRBV)) (not (c qtb2)))) (memPlan (by simp [cPlan]))
  have t3 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDE, kMVE, kWEX, kPT]) (not (c qte)))) (memPlan (by simp [cPlan]))
  have t4 := factN ok hC hD (e := mul3 (c pf) (c kPT) (not (c nokey))) (memPlan (by simp [cPlan]))
  have t5 := factN ok hC hD (e := mul3 (c pf) (c kPT) (c qodd)) (memPlan (by simp [cPlan]))
  have t6 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRLP, kMVL, kNLF]) (not (c qtl)))) (memPlan (by simp [cPlan]))
  have t7 := factN ok hC hD (e := .mul (c pf) (.mul (c nokey) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
  have t8 := factN ok hC hD (e := .mul (c pf) (.mul (c kNLF) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
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
  simp only [sumc, List.map_cons, List.map_nil, kRD, spRecvE] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  nev_simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp only [hpf, hx0, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  refine ⟨hx0, ?_⟩
  omega

theorem head_RBV (hpf : C pf = 1) (hk : ∀ m, m < 12 → C (kcol m) = if m = 4 then 1 else 0) :
    C xcp = 0 ∧
    C vcp = 0 ∧
    C qtb2 = 1 ∧
    C useA = 1 ∧
    C bN = 0 ∧
    C bL = 0 ∧
    C cO = 0 ∧
    C cS = 0 ∧
    C Cc = 0 ∧
    C eL = 1 ∧
    C eS = 0 ∧
    C Kc = 50 := by
  have k0 : C kRDB = 0 := hk 0 (by omega)
  have k1 : C kRDE = 0 := hk 1 (by omega)
  have k2 : C kRLP = 0 := hk 2 (by omega)
  have k3 : C kRBR = 0 := hk 3 (by omega)
  have k4 : C kRBV = 1 := hk 4 (by omega)
  have k5 : C kRBI = 0 := hk 5 (by omega)
  have k6 : C kMVL = 0 := hk 6 (by omega)
  have k7 : C kMVE = 0 := hk 7 (by omega)
  have k8 : C kNLF = 0 := hk 8 (by omega)
  have k9 : C kWEX = 0 := hk 9 (by omega)
  have k10 : C kSPB = 0 := hk 10 (by omega)
  have k11 : C kPT = 0 := hk 11 (by omega)
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a xcp; have := a vcp; have := a qtl; have := a qte; have := a qtb2; have := a nokey; have := a qodd; have := a qhk; have := a useA; have := a bN; have := a bL; have := a cO; have := a cS; have := a Cc; have := a eL; have := a eS; have := a Kc; have := a phk; have := a cESl1; have := a cESn1; have := a cLSa
  have := partBoolN ok hC hpf (x := qtl) (by decide); have := partBoolN ok hC hpf (x := qte) (by decide)
  have := partBoolN ok hC hpf (x := nokey) (by decide)
  have hx0 : C xcp = 0 := by
    have fx := factN ok hC hD (e := .mul (c pf) (sub (c xcp) (.mul (c kSPB) (.add (c cESl1) (c cESn1))))) (memPlan (by simp [cPlan]))
    nev_simp at fx; simp only [hpf, k10] at fx; simp at fx; omega
  have fv := factN ok hC hD (e := .mul (c pf) (sub (c vcp) (sum [c kRDB, c kRBI, c kMVL, .mul (c kSPB) (c cLSa)]))) (memPlan (by simp [cPlan]))
  have t1 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDB, kRBR, kRBI]) (.add (c qtl) (c qte)))) (memPlan (by simp [cPlan]))
  have t2 := factN ok hC hD (e := .mul (c pf) (.mul (.add (c kRBR) (c kRBV)) (not (c qtb2)))) (memPlan (by simp [cPlan]))
  have t3 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDE, kMVE, kWEX, kPT]) (not (c qte)))) (memPlan (by simp [cPlan]))
  have t4 := factN ok hC hD (e := mul3 (c pf) (c kPT) (not (c nokey))) (memPlan (by simp [cPlan]))
  have t5 := factN ok hC hD (e := mul3 (c pf) (c kPT) (c qodd)) (memPlan (by simp [cPlan]))
  have t6 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRLP, kMVL, kNLF]) (not (c qtl)))) (memPlan (by simp [cPlan]))
  have t7 := factN ok hC hD (e := .mul (c pf) (.mul (c nokey) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
  have t8 := factN ok hC hD (e := .mul (c pf) (.mul (c kNLF) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
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
  simp only [sumc, List.map_cons, List.map_nil, kRD, spRecvE] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  nev_simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp only [hpf, hx0, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  refine ⟨hx0, ?_⟩
  omega

theorem head_RBI (hpf : C pf = 1) (hk : ∀ m, m < 12 → C (kcol m) = if m = 5 then 1 else 0) :
    C xcp = 0 ∧
    C vcp = 1 ∧
    C qtl = 0 ∧
    C qte = 0 ∧
    C useA = 1 ∧
    C bN = 0 ∧
    C bL = 0 ∧
    C cO = 0 ∧
    C cS = 0 ∧
    C Cc = 0 ∧
    C eL = 1 ∧
    C eS = 0 ∧
    C Kc = 102 := by
  have k0 : C kRDB = 0 := hk 0 (by omega)
  have k1 : C kRDE = 0 := hk 1 (by omega)
  have k2 : C kRLP = 0 := hk 2 (by omega)
  have k3 : C kRBR = 0 := hk 3 (by omega)
  have k4 : C kRBV = 0 := hk 4 (by omega)
  have k5 : C kRBI = 1 := hk 5 (by omega)
  have k6 : C kMVL = 0 := hk 6 (by omega)
  have k7 : C kMVE = 0 := hk 7 (by omega)
  have k8 : C kNLF = 0 := hk 8 (by omega)
  have k9 : C kWEX = 0 := hk 9 (by omega)
  have k10 : C kSPB = 0 := hk 10 (by omega)
  have k11 : C kPT = 0 := hk 11 (by omega)
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a xcp; have := a vcp; have := a qtl; have := a qte; have := a qtb2; have := a nokey; have := a qodd; have := a qhk; have := a useA; have := a bN; have := a bL; have := a cO; have := a cS; have := a Cc; have := a eL; have := a eS; have := a Kc; have := a phk; have := a cESl1; have := a cESn1; have := a cLSa
  have := partBoolN ok hC hpf (x := qtl) (by decide); have := partBoolN ok hC hpf (x := qte) (by decide)
  have := partBoolN ok hC hpf (x := nokey) (by decide)
  have hx0 : C xcp = 0 := by
    have fx := factN ok hC hD (e := .mul (c pf) (sub (c xcp) (.mul (c kSPB) (.add (c cESl1) (c cESn1))))) (memPlan (by simp [cPlan]))
    nev_simp at fx; simp only [hpf, k10] at fx; simp at fx; omega
  have fv := factN ok hC hD (e := .mul (c pf) (sub (c vcp) (sum [c kRDB, c kRBI, c kMVL, .mul (c kSPB) (c cLSa)]))) (memPlan (by simp [cPlan]))
  have t1 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDB, kRBR, kRBI]) (.add (c qtl) (c qte)))) (memPlan (by simp [cPlan]))
  have t2 := factN ok hC hD (e := .mul (c pf) (.mul (.add (c kRBR) (c kRBV)) (not (c qtb2)))) (memPlan (by simp [cPlan]))
  have t3 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDE, kMVE, kWEX, kPT]) (not (c qte)))) (memPlan (by simp [cPlan]))
  have t4 := factN ok hC hD (e := mul3 (c pf) (c kPT) (not (c nokey))) (memPlan (by simp [cPlan]))
  have t5 := factN ok hC hD (e := mul3 (c pf) (c kPT) (c qodd)) (memPlan (by simp [cPlan]))
  have t6 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRLP, kMVL, kNLF]) (not (c qtl)))) (memPlan (by simp [cPlan]))
  have t7 := factN ok hC hD (e := .mul (c pf) (.mul (c nokey) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
  have t8 := factN ok hC hD (e := .mul (c pf) (.mul (c kNLF) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
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
  simp only [sumc, List.map_cons, List.map_nil, kRD, spRecvE] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  nev_simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp only [hpf, hx0, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  refine ⟨hx0, ?_⟩
  omega

theorem head_MVL (hpf : C pf = 1) (hk : ∀ m, m < 12 → C (kcol m) = if m = 6 then 1 else 0) :
    C xcp = 0 ∧
    C vcp = 1 ∧
    C qtl = 1 ∧
    C useA = 0 ∧
    C bN = 0 ∧
    C bL = 0 ∧
    C cO = 0 ∧
    C cS = 0 ∧
    C Cc = 0 ∧
    C eL = 0 ∧
    C eS = 1 ∧
    (C qhk < 2 ^ 23 → C Kc = 100 + 2 * C qhk) := by
  have k0 : C kRDB = 0 := hk 0 (by omega)
  have k1 : C kRDE = 0 := hk 1 (by omega)
  have k2 : C kRLP = 0 := hk 2 (by omega)
  have k3 : C kRBR = 0 := hk 3 (by omega)
  have k4 : C kRBV = 0 := hk 4 (by omega)
  have k5 : C kRBI = 0 := hk 5 (by omega)
  have k6 : C kMVL = 1 := hk 6 (by omega)
  have k7 : C kMVE = 0 := hk 7 (by omega)
  have k8 : C kNLF = 0 := hk 8 (by omega)
  have k9 : C kWEX = 0 := hk 9 (by omega)
  have k10 : C kSPB = 0 := hk 10 (by omega)
  have k11 : C kPT = 0 := hk 11 (by omega)
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a xcp; have := a vcp; have := a qtl; have := a qte; have := a qtb2; have := a nokey; have := a qodd; have := a qhk; have := a useA; have := a bN; have := a bL; have := a cO; have := a cS; have := a Cc; have := a eL; have := a eS; have := a Kc; have := a phk; have := a cESl1; have := a cESn1; have := a cLSa
  have := partBoolN ok hC hpf (x := qtl) (by decide); have := partBoolN ok hC hpf (x := qte) (by decide)
  have := partBoolN ok hC hpf (x := nokey) (by decide)
  have hx0 : C xcp = 0 := by
    have fx := factN ok hC hD (e := .mul (c pf) (sub (c xcp) (.mul (c kSPB) (.add (c cESl1) (c cESn1))))) (memPlan (by simp [cPlan]))
    nev_simp at fx; simp only [hpf, k10] at fx; simp at fx; omega
  have fv := factN ok hC hD (e := .mul (c pf) (sub (c vcp) (sum [c kRDB, c kRBI, c kMVL, .mul (c kSPB) (c cLSa)]))) (memPlan (by simp [cPlan]))
  have t1 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDB, kRBR, kRBI]) (.add (c qtl) (c qte)))) (memPlan (by simp [cPlan]))
  have t2 := factN ok hC hD (e := .mul (c pf) (.mul (.add (c kRBR) (c kRBV)) (not (c qtb2)))) (memPlan (by simp [cPlan]))
  have t3 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDE, kMVE, kWEX, kPT]) (not (c qte)))) (memPlan (by simp [cPlan]))
  have t4 := factN ok hC hD (e := mul3 (c pf) (c kPT) (not (c nokey))) (memPlan (by simp [cPlan]))
  have t5 := factN ok hC hD (e := mul3 (c pf) (c kPT) (c qodd)) (memPlan (by simp [cPlan]))
  have t6 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRLP, kMVL, kNLF]) (not (c qtl)))) (memPlan (by simp [cPlan]))
  have t7 := factN ok hC hD (e := .mul (c pf) (.mul (c nokey) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
  have t8 := factN ok hC hD (e := .mul (c pf) (.mul (c kNLF) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
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
  simp only [sumc, List.map_cons, List.map_nil, kRD, spRecvE] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  nev_simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp only [hpf, hx0, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  refine ⟨hx0, ?_⟩
  omega

theorem head_MVE (hpf : C pf = 1) (hk : ∀ m, m < 12 → C (kcol m) = if m = 7 then 1 else 0) :
    C xcp = 0 ∧
    C vcp = 0 ∧
    C qte = 1 ∧
    C useA = 1 ∧
    C bN = 0 ∧
    C bL = 0 ∧
    C cO = 0 ∧
    C cS = 0 ∧
    (C phk < 2 ^ 23 → C Cc = 50 + 2 * C phk) ∧
    C eL = 0 ∧
    C eS = 0 ∧
    (C qhk < 2 ^ 23 → C Kc = 50 + 2 * C qhk) := by
  have k0 : C kRDB = 0 := hk 0 (by omega)
  have k1 : C kRDE = 0 := hk 1 (by omega)
  have k2 : C kRLP = 0 := hk 2 (by omega)
  have k3 : C kRBR = 0 := hk 3 (by omega)
  have k4 : C kRBV = 0 := hk 4 (by omega)
  have k5 : C kRBI = 0 := hk 5 (by omega)
  have k6 : C kMVL = 0 := hk 6 (by omega)
  have k7 : C kMVE = 1 := hk 7 (by omega)
  have k8 : C kNLF = 0 := hk 8 (by omega)
  have k9 : C kWEX = 0 := hk 9 (by omega)
  have k10 : C kSPB = 0 := hk 10 (by omega)
  have k11 : C kPT = 0 := hk 11 (by omega)
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a xcp; have := a vcp; have := a qtl; have := a qte; have := a qtb2; have := a nokey; have := a qodd; have := a qhk; have := a useA; have := a bN; have := a bL; have := a cO; have := a cS; have := a Cc; have := a eL; have := a eS; have := a Kc; have := a phk; have := a cESl1; have := a cESn1; have := a cLSa
  have := partBoolN ok hC hpf (x := qtl) (by decide); have := partBoolN ok hC hpf (x := qte) (by decide)
  have := partBoolN ok hC hpf (x := nokey) (by decide)
  have hx0 : C xcp = 0 := by
    have fx := factN ok hC hD (e := .mul (c pf) (sub (c xcp) (.mul (c kSPB) (.add (c cESl1) (c cESn1))))) (memPlan (by simp [cPlan]))
    nev_simp at fx; simp only [hpf, k10] at fx; simp at fx; omega
  have fv := factN ok hC hD (e := .mul (c pf) (sub (c vcp) (sum [c kRDB, c kRBI, c kMVL, .mul (c kSPB) (c cLSa)]))) (memPlan (by simp [cPlan]))
  have t1 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDB, kRBR, kRBI]) (.add (c qtl) (c qte)))) (memPlan (by simp [cPlan]))
  have t2 := factN ok hC hD (e := .mul (c pf) (.mul (.add (c kRBR) (c kRBV)) (not (c qtb2)))) (memPlan (by simp [cPlan]))
  have t3 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDE, kMVE, kWEX, kPT]) (not (c qte)))) (memPlan (by simp [cPlan]))
  have t4 := factN ok hC hD (e := mul3 (c pf) (c kPT) (not (c nokey))) (memPlan (by simp [cPlan]))
  have t5 := factN ok hC hD (e := mul3 (c pf) (c kPT) (c qodd)) (memPlan (by simp [cPlan]))
  have t6 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRLP, kMVL, kNLF]) (not (c qtl)))) (memPlan (by simp [cPlan]))
  have t7 := factN ok hC hD (e := .mul (c pf) (.mul (c nokey) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
  have t8 := factN ok hC hD (e := .mul (c pf) (.mul (c kNLF) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
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
  simp only [sumc, List.map_cons, List.map_nil, kRD, spRecvE] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  nev_simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp only [hpf, hx0, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  refine ⟨hx0, ?_⟩
  omega

theorem head_NLF (hpf : C pf = 1) (hk : ∀ m, m < 12 → C (kcol m) = if m = 8 then 1 else 0) :
    C xcp = 0 ∧
    C vcp = 0 ∧
    C qtl = 1 ∧
    C qhk = 1 ∧
    C useA = 0 ∧
    C bN = 0 ∧
    C bL = 0 ∧
    C cO = 0 ∧
    C cS = 0 ∧
    C Cc = 0 ∧
    C eL = 1 ∧
    C eS = 0 ∧
    C Kc = 102 := by
  have k0 : C kRDB = 0 := hk 0 (by omega)
  have k1 : C kRDE = 0 := hk 1 (by omega)
  have k2 : C kRLP = 0 := hk 2 (by omega)
  have k3 : C kRBR = 0 := hk 3 (by omega)
  have k4 : C kRBV = 0 := hk 4 (by omega)
  have k5 : C kRBI = 0 := hk 5 (by omega)
  have k6 : C kMVL = 0 := hk 6 (by omega)
  have k7 : C kMVE = 0 := hk 7 (by omega)
  have k8 : C kNLF = 1 := hk 8 (by omega)
  have k9 : C kWEX = 0 := hk 9 (by omega)
  have k10 : C kSPB = 0 := hk 10 (by omega)
  have k11 : C kPT = 0 := hk 11 (by omega)
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a xcp; have := a vcp; have := a qtl; have := a qte; have := a qtb2; have := a nokey; have := a qodd; have := a qhk; have := a useA; have := a bN; have := a bL; have := a cO; have := a cS; have := a Cc; have := a eL; have := a eS; have := a Kc; have := a phk; have := a cESl1; have := a cESn1; have := a cLSa
  have := partBoolN ok hC hpf (x := qtl) (by decide); have := partBoolN ok hC hpf (x := qte) (by decide)
  have := partBoolN ok hC hpf (x := nokey) (by decide)
  have hx0 : C xcp = 0 := by
    have fx := factN ok hC hD (e := .mul (c pf) (sub (c xcp) (.mul (c kSPB) (.add (c cESl1) (c cESn1))))) (memPlan (by simp [cPlan]))
    nev_simp at fx; simp only [hpf, k10] at fx; simp at fx; omega
  have fv := factN ok hC hD (e := .mul (c pf) (sub (c vcp) (sum [c kRDB, c kRBI, c kMVL, .mul (c kSPB) (c cLSa)]))) (memPlan (by simp [cPlan]))
  have t1 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDB, kRBR, kRBI]) (.add (c qtl) (c qte)))) (memPlan (by simp [cPlan]))
  have t2 := factN ok hC hD (e := .mul (c pf) (.mul (.add (c kRBR) (c kRBV)) (not (c qtb2)))) (memPlan (by simp [cPlan]))
  have t3 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDE, kMVE, kWEX, kPT]) (not (c qte)))) (memPlan (by simp [cPlan]))
  have t4 := factN ok hC hD (e := mul3 (c pf) (c kPT) (not (c nokey))) (memPlan (by simp [cPlan]))
  have t5 := factN ok hC hD (e := mul3 (c pf) (c kPT) (c qodd)) (memPlan (by simp [cPlan]))
  have t6 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRLP, kMVL, kNLF]) (not (c qtl)))) (memPlan (by simp [cPlan]))
  have t7 := factN ok hC hD (e := .mul (c pf) (.mul (c nokey) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
  have t8 := factN ok hC hD (e := .mul (c pf) (.mul (c kNLF) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
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
  simp only [sumc, List.map_cons, List.map_nil, kRD, spRecvE] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  nev_simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp only [hpf, hx0, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  refine ⟨hx0, ?_⟩
  omega

theorem head_WEX (hpf : C pf = 1) (hk : ∀ m, m < 12 → C (kcol m) = if m = 9 then 1 else 0) :
    C xcp = 0 ∧
    C vcp = 0 ∧
    C qte = 1 ∧
    C useA = 0 ∧
    C bN = 1 ∧
    C bL = 0 ∧
    C cO = 0 ∧
    C cS = 0 ∧
    C Cc = 0 ∧
    C eL = 0 ∧
    C eS = 0 ∧
    (C qhk < 2 ^ 23 → C Kc = 50 + 2 * C qhk) := by
  have k0 : C kRDB = 0 := hk 0 (by omega)
  have k1 : C kRDE = 0 := hk 1 (by omega)
  have k2 : C kRLP = 0 := hk 2 (by omega)
  have k3 : C kRBR = 0 := hk 3 (by omega)
  have k4 : C kRBV = 0 := hk 4 (by omega)
  have k5 : C kRBI = 0 := hk 5 (by omega)
  have k6 : C kMVL = 0 := hk 6 (by omega)
  have k7 : C kMVE = 0 := hk 7 (by omega)
  have k8 : C kNLF = 0 := hk 8 (by omega)
  have k9 : C kWEX = 1 := hk 9 (by omega)
  have k10 : C kSPB = 0 := hk 10 (by omega)
  have k11 : C kPT = 0 := hk 11 (by omega)
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a xcp; have := a vcp; have := a qtl; have := a qte; have := a qtb2; have := a nokey; have := a qodd; have := a qhk; have := a useA; have := a bN; have := a bL; have := a cO; have := a cS; have := a Cc; have := a eL; have := a eS; have := a Kc; have := a phk; have := a cESl1; have := a cESn1; have := a cLSa
  have := partBoolN ok hC hpf (x := qtl) (by decide); have := partBoolN ok hC hpf (x := qte) (by decide)
  have := partBoolN ok hC hpf (x := nokey) (by decide)
  have hx0 : C xcp = 0 := by
    have fx := factN ok hC hD (e := .mul (c pf) (sub (c xcp) (.mul (c kSPB) (.add (c cESl1) (c cESn1))))) (memPlan (by simp [cPlan]))
    nev_simp at fx; simp only [hpf, k10] at fx; simp at fx; omega
  have fv := factN ok hC hD (e := .mul (c pf) (sub (c vcp) (sum [c kRDB, c kRBI, c kMVL, .mul (c kSPB) (c cLSa)]))) (memPlan (by simp [cPlan]))
  have t1 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDB, kRBR, kRBI]) (.add (c qtl) (c qte)))) (memPlan (by simp [cPlan]))
  have t2 := factN ok hC hD (e := .mul (c pf) (.mul (.add (c kRBR) (c kRBV)) (not (c qtb2)))) (memPlan (by simp [cPlan]))
  have t3 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDE, kMVE, kWEX, kPT]) (not (c qte)))) (memPlan (by simp [cPlan]))
  have t4 := factN ok hC hD (e := mul3 (c pf) (c kPT) (not (c nokey))) (memPlan (by simp [cPlan]))
  have t5 := factN ok hC hD (e := mul3 (c pf) (c kPT) (c qodd)) (memPlan (by simp [cPlan]))
  have t6 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRLP, kMVL, kNLF]) (not (c qtl)))) (memPlan (by simp [cPlan]))
  have t7 := factN ok hC hD (e := .mul (c pf) (.mul (c nokey) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
  have t8 := factN ok hC hD (e := .mul (c pf) (.mul (c kNLF) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
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
  simp only [sumc, List.map_cons, List.map_nil, kRD, spRecvE] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  nev_simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp only [hpf, hx0, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  refine ⟨hx0, ?_⟩
  omega

theorem head_PT (hpf : C pf = 1) (hk : ∀ m, m < 12 → C (kcol m) = if m = 11 then 1 else 0) :
    C xcp = 0 ∧
    C vcp = 0 ∧
    C qte = 1 ∧
    C nokey = 1 ∧
    C qodd = 0 ∧
    C qhk = 1 ∧
    C useA = 1 ∧
    C bN = 1 ∧
    C bL = 0 ∧
    C cO = 1 ∧
    C cS = 0 ∧
    C Cc = 0 ∧
    C eL = 0 ∧
    C eS = 0 ∧
    C Kc = 0 := by
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
  have k10 : C kSPB = 0 := hk 10 (by omega)
  have k11 : C kPT = 1 := hk 11 (by omega)
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a xcp; have := a vcp; have := a qtl; have := a qte; have := a qtb2; have := a nokey; have := a qodd; have := a qhk; have := a useA; have := a bN; have := a bL; have := a cO; have := a cS; have := a Cc; have := a eL; have := a eS; have := a Kc; have := a phk; have := a cESl1; have := a cESn1; have := a cLSa
  have := partBoolN ok hC hpf (x := qtl) (by decide); have := partBoolN ok hC hpf (x := qte) (by decide)
  have := partBoolN ok hC hpf (x := nokey) (by decide)
  have hx0 : C xcp = 0 := by
    have fx := factN ok hC hD (e := .mul (c pf) (sub (c xcp) (.mul (c kSPB) (.add (c cESl1) (c cESn1))))) (memPlan (by simp [cPlan]))
    nev_simp at fx; simp only [hpf, k10] at fx; simp at fx; omega
  have fv := factN ok hC hD (e := .mul (c pf) (sub (c vcp) (sum [c kRDB, c kRBI, c kMVL, .mul (c kSPB) (c cLSa)]))) (memPlan (by simp [cPlan]))
  have t1 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDB, kRBR, kRBI]) (.add (c qtl) (c qte)))) (memPlan (by simp [cPlan]))
  have t2 := factN ok hC hD (e := .mul (c pf) (.mul (.add (c kRBR) (c kRBV)) (not (c qtb2)))) (memPlan (by simp [cPlan]))
  have t3 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDE, kMVE, kWEX, kPT]) (not (c qte)))) (memPlan (by simp [cPlan]))
  have t4 := factN ok hC hD (e := mul3 (c pf) (c kPT) (not (c nokey))) (memPlan (by simp [cPlan]))
  have t5 := factN ok hC hD (e := mul3 (c pf) (c kPT) (c qodd)) (memPlan (by simp [cPlan]))
  have t6 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRLP, kMVL, kNLF]) (not (c qtl)))) (memPlan (by simp [cPlan]))
  have t7 := factN ok hC hD (e := .mul (c pf) (.mul (c nokey) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
  have t8 := factN ok hC hD (e := .mul (c pf) (.mul (c kNLF) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
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
  simp only [sumc, List.map_cons, List.map_nil, kRD, spRecvE] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  nev_simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp only [hpf, hx0, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11] at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp at fv t1 t2 t3 t4 t5 t6 t7 t8 m1 m2 m3 m4 m5 m6 m7 m8 m9
  have hnk : C nokey = 1 := by omega
  rw [hnk] at t7; simp at t7
  refine ⟨hx0, ?_⟩
  omega

end

end ZkFormal.NearV3.Render.UpsRelay.Extract
