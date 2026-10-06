import ZkFormal.NearV3.Extract.Ups.FieldBytes
import ZkFormal.NearV3.Extract.Ups.MemRows

/-!
# ZkFormal.NearV3.Extract.Ups.NlfRows — the new-leaf part (`NLF`), row facts

On the first row of an `NLF` part (kind index 8): a leaf with `hplen 1`, the `memory_usage`
formula `R = 102 + L` (`useA = bN = bL = cO = cS = eS = 0`, `Cc = 0`, `eL = 1`, `Kc = 102`)
(`nlfHead`).  On `MEM` rows the `L` register holds `L0 L1 L2` and shifts (`memLR`).  The
fresh hex-prefix flag byte of a new leaf (`nlfHpf`).
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

theorem nlfHead (hpf : C pf = 1) (hk : ∀ m, m < 12 → C (kcol m) = if m = 8 then 1 else 0) (hx : C xcp = 0) :
    C qtl = 1 ∧ C qhk = 1 ∧ C useA = 0 ∧ C bN = 0 ∧ C bL = 0 ∧ C cO = 0 ∧ C cS = 0 ∧ C Cc = 0 ∧
    C eL = 1 ∧ C eS = 0 ∧ C Kc = 102 := by
  have k0 : C kRDB = 0 := hk 0 (by omega); have k1 : C kRDE = 0 := hk 1 (by omega)
  have k2 : C kRLP = 0 := hk 2 (by omega); have k3 : C kRBR = 0 := hk 3 (by omega)
  have k4 : C kRBV = 0 := hk 4 (by omega); have k5 : C kRBI = 0 := hk 5 (by omega)
  have k6 : C kMVL = 0 := hk 6 (by omega); have k7 : C kMVE = 0 := hk 7 (by omega)
  have k8 : C kNLF = 1 := hk 8 (by omega); have k9 : C kWEX = 0 := hk 9 (by omega)
  have k10 : C kSPB = 0 := hk 10 (by omega); have k11 : C kPT = 0 := hk 11 (by omega)
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a qtl; have := a qhk; have := a useA; have := a bN; have := a bL; have := a cO; have := a cS
  have := a Cc; have := a eL; have := a eS; have := a Kc
  have f1 := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRLP, kMVL, kNLF]) (not (c qtl)))) (memPlan (by simp [cPlan]))
  have f2 := factN ok hC hD (e := .mul (c pf) (.mul (c kNLF) (sub (c qhk) (k 1)))) (memPlan (by simp [cPlan]))
  have f3 := factN ok hC hD (e := .mul (c pf) (sub (c useA) (sum [c kRDB, c kRDE, c kRBR, c kRBV, c kRBI, c kMVE,
    c xcp, c kPT]))) (memPlan (by simp [cPlan]))
  have f4 := factN ok hC hD (e := .mul (c pf) (sub (c bN) (sum [c kRDB, c kRDE, c kWEX, .mul (c kSPB) spRecvE, c kPT])))
    (memPlan (by simp [cPlan]))
  have f5 := factN ok hC hD (e := .mul (c pf) (sub (c bL) (c kRBR))) (memPlan (by simp [cPlan]))
  have f6 := factN ok hC hD (e := .mul (c pf) (sub (c cO) (.add kRD (c kPT)))) (memPlan (by simp [cPlan]))
  have f7 := factN ok hC hD (e := .mul (c pf) (sub (c cS) (c kRBR))) (memPlan (by simp [cPlan]))
  have f8 := factN ok hC hD (e := .mul (c pf) (sub (c Cc) (.mul (.add (c kMVE) (c xcp)) (.add (k 50) (smul 2 (c phk))))))
    (memPlan (by simp [cPlan]))
  have f9 := factN ok hC hD (e := .mul (c pf) (sub (c eL) (sum [c kRLP, c kRBV, c kRBI, c kNLF, c kSPB])))
    (memPlan (by simp [cPlan]))
  have f10 := factN ok hC hD (e := .mul (c pf) (sub (c eS) (.add (c kMVL) (.mul (c kSPB) (c cLSa))))) (memPlan (by simp [cPlan]))
  have f11 := factN ok hC hD (e := .mul (c pf) (sub (c Kc) (sum [
      .mul (c kRLP) (.add (k 100) (smul 2 (c qhk))), smul 50 (c kRBV), smul 102 (c kRBI),
      .mul (c kMVL) (.add (k 100) (smul 2 (c qhk))), .mul (c kMVE) (.add (k 50) (smul 2 (c qhk))),
      smul 102 (c kNLF), .mul (c kWEX) (.add (k 50) (smul 2 (c qhk))),
      .mul (c kSPB) (sum [smul 202 (c cLSa), smul 100 (sumc [cLSb, cESl0, cESl1]),
        smul 152 (sumc [cLSc, cESn0, cESn1])])]))) (memPlan (by simp [cPlan]))
  simp only [sumc, List.map_cons, List.map_nil, kRD, spRecvE] at f1 f4 f6 f11
  nev_simp at f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
  simp only [hpf, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, hx] at f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
  simp at f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
  omega

/-- The `L` register on `MEM` rows. -/
theorem memLR (hm : C sMEM = 1) :
    (C fs = 1 → C (LR 0) = C L0 ∧ C (LR 1) = C L1 ∧ C (LR 2) = C L2) ∧
    (C fe = 0 → D (LR 0) = C (LR 1) ∧ D (LR 1) = C (LR 2) ∧ D (LR 2) = 0) := by
  have a := fun x => hC x
  have d := fun x => hD x
  simp only [P_lit] at a d
  have := a (LR 0); have := a (LR 1); have := a (LR 2); have := a L0; have := a L1; have := a L2
  have := d (LR 0); have := d (LR 1); have := d (LR 2)
  have hv : C sVLEN = 0 := by
    have := stSum ok hC
    have := le1 (stBool ok hC (x := sMEM) (by simp [states]))
    have := le1 (rowBool ok hC (x := qb) (by simp [rowBools]))
    omega
  refine ⟨fun hfs => ?_, fun hfe => ?_⟩
  · have g := fun i (hi : i < 3) => factN ok hC hD (e := Dsl.mul3 (.add (c sVLEN) (c sMEM)) (c fs) (sub (c (LR i)) (c (Lb i))))
      (memMem (by
        unfold cMem; simp only [List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩))))))))
    have g0 := g 0 (by omega); have g1 := g 1 (by omega); have g2 := g 2 (by omega)
    simp only [Lb, List.getD_cons_zero, List.getD_cons_succ] at g0 g1 g2
    nev_simp at g0 g1 g2
    simp [hv, hm, hfs] at g0 g1 g2
    omega
  · have g := fun i (hi : i < 2) => factN ok hC hD (e := Dsl.mul3 (.add (c sVLEN) (c sMEM)) (not (c fe))
        (sub (n (LR i)) (c (LR (i + 1))))) (memMem (by
        unfold cMem; simp only [List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩)))))))
    have g0 := g 0 (by omega); have g1 := g 1 (by omega)
    have g2 := factN ok hC hD (e := mul3 (.add (c sVLEN) (c sMEM)) (not (c fe)) (n (LR 2))) (memMem (by simp [cMem]))
    nev_simp at g0 g1 g2
    simp [hv, hm, hfe] at g0 g1 g2
    omega

/-- The new leaf's hex-prefix flag byte: `0x3f` (`ys = [15]`) or `0x20` (`ys = []`). -/
theorem nlfHpf (hh : C sHPF = 1) (hk : C kNLF = 1) (hts : C ts1 ≤ 1) : C b = 32 + 31 * C ts1 := by
  have f := factN ok hC hD (e := mul3 (c sHPF) (c kNLF) (sub (c b) (.add (k 32) (smul 31 (c ts1)))))
    (memBytes (by simp [cBytes]))
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a b; have := a ts1
  nev_simp at f
  simp only [hh, hk] at f
  rcases (show C ts1 = 0 ∨ C ts1 = 1 by omega) with h | h <;> rw [h] at f ⊢ <;> simp at f ⊢ <;> omega

end

end ZkFormal.NearV3.UpsRows
