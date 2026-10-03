import ReexecNpai.Spec.WalkAux3

/-!
# Helper lemmas for `Spec/Walk.lean`: the branch step
-/

set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1 WalkProof WalkAux

section
variable {pub cb pb : Bytes} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → Bytes} {m : M}

set_option maxHeartbeats 1000000 in
theorem walkBr_wp (h : TrieSt cb pb rs R A K vals m) {key : List Nat}
    (hkey : readMem m.mem S_KEY key.length = nibBytes key) (hk16 : ∀ x ∈ key, x < 16) (hkl : key.length ≤ 130)
    {y : M} (hc : Com key.length A.length m y) {j o : Nat} {e : Ent} (hj : A[j]? = some e)
    {v : Option (Option (Nat × Bytes))} {ks : List (Option (Option Bytes))} {mm : Nat} (hn : e.nf = .branch v ks mm)
    (h0 : y.regs 0 = j) (h1 : y.regs 1 = o) (h5 : y.regs 5 = e.pre) (ho : o ≤ key.length) :
    wp P (Inp pub cb pb) pWalkBranch y (fun y' => Com key.length A.length m y' ∧
      ((o = key.length ∧ y'.regs 2 = 0 ∧ y'.regs 0 = j) ∨
       (o < key.length ∧ y'.regs 2 = y.regs 2 ∧ ks[key.getD o 0]? = some (some none) ∧ y'.regs 1 = o + 1 ∧
        y'.regs 0 = (A.getD (childIdx K e.kid (nRev ks) (revBelow ks (key.getD o 0))) default).res))) := by
  obtain ⟨hc3, hc7, hc9, hc14, hc15, hcm⟩ := hc
  obtain ⟨-, hl16, hex, hpf, hpe⟩ := br_hdr h hj hn
  simp only [PF] at hpf
  have hjl := lt_of_get hj
  have hN := h.tok.wf.len_le
  simp only [NCAP] at hN
  have hexy : ArenaCore.Bytes.leToNat (readMem y.mem (e.pre - 2) 2) = bitsRev ks 0 := by
    rw [rd_m hcm (by simp only [S_HP]; omega)]; exact hex
  have hbl : bitsRev ks 0 < 65536 := by have := bitsRev_lt ks; rw [hl16] at this; simpa using this
  simp only [pWalkBranch]
  walk_vc [hc3, hc15, hc14, h1, h5, h0]
  refine ⟨fun hne => ?_, fun hoL => ?_⟩
  · have hoL : o < key.length := by omega
    have hnk : (y.mem (o + 512)).toNat = key.getD o 0 := by
      rw [hcm _ (by simp only [S_HP]; omega), Nat.add_comm]; exact mem_key hkey hk16 hoL
    have hn16 : key.getD o 0 < 16 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hoL]; exact hk16 _ (List.getElem_mem _)
    intro y1 _ e1; subst e1
    rw [wp_ld16 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, hc14])
      (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize, h5]; rw [evS _ _ (by omega) (by omega)]; omega)
      (by simp)]
    have hsh1 : BinOp.shr.eval (bitsRev ks 0) (key.getD o 0) = bitsRev ks 0 / 2 ^ (key.getD o 0) :=
      eval_shr _ _ (by omega) (by unfold wordMod; omega)
    have hsh2 : BinOp.shr.eval (bitsRev ks 0) (key.getD o 0 + 1) = bitsRev ks 0 / 2 ^ (key.getD o 0 + 1) :=
      eval_shr _ _ (by omega) (by unfold wordMod; omega)
    walk_vc [hc3, hc15, hc14, h1, h5, h0, hnk, hexy, hsh1, hsh2, evAnd1, bitsRev_bit]
    intro hbit
    have hks : ks[key.getD o 0]? = some (some none) := hbit
    simp only [hks, ↓reduceIte]
    have hpc := popc_above ks hl16 _ hks
    have hdl : bitsRev ks 0 / 2 ^ (key.getD o 0 + 1) < 18446744073709551616 := by
      have := Nat.div_le_self (bitsRev ks 0) (2 ^ (key.getD o 0 + 1)); omega
    refine wp_of_spec (popc16_spec (d := 6) (s := 8) (a := 4) (b := 11) (c := 12) (by decide) (by decide)
      ⟨by simp [setReg_apply, hc15, K1], by simp [setReg_apply, hc14, K8]⟩ (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hdl)) ?_
    rintro y2 c2 ⟨hp6, hm2, hF2, -⟩
    simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, hpc] at hp6
    have g := fun r (hr : r ∉ [6, 4, 11, 12]) => (hF2 r hr).trans (by simp only [setReg_apply]; rfl)
    have g0 : y2.regs 0 = j := by rw [g 0 (by simp)]; simp [setReg_apply, h0]
    have g1 : y2.regs 1 = o + 1 := by rw [g 1 (by simp)]; simp [setReg_apply]
    have g2 : y2.regs 2 = y.regs 2 := by rw [g 2 (by simp)]; simp [setReg_apply]
    have g3 : y2.regs 3 = key.length := by rw [g 3 (by simp)]; simp [setReg_apply, hc3]
    have g7 : y2.regs 7 = A.length := by rw [g 7 (by simp)]; simp [setReg_apply, hc7]
    have g9 : y2.regs 9 = m.regs 9 := by rw [g 9 (by simp)]; simp [setReg_apply, hc9]
    have g14 : y2.regs 14 = 8 := by rw [g 14 (by simp)]; simp [setReg_apply, hc14]
    have g15 : y2.regs 15 = 1 := by rw [g 15 (by simp)]; simp [setReg_apply, hc15]
    simp only at hm2
    have hcm2 : ∀ a, (a < S_HP ∨ S_HP + 128 ≤ a) → y2.mem a = m.mem a := by
      intro a ha; rw [hm2]; exact hcm a ha
    have hlt := revBelow_lt ks _ hks
    obtain ⟨hkid, hKl⟩ := kid_range h hj
    rw [hn] at hkid
    simp only [nKids] at hkid
    simp only [NCAP] at hKl
    obtain ⟨ec, hec, hclt, -, -⟩ := child_info h.tok.wf hj (q := revBelow ks (key.getD o 0)) (by rw [hn]; exact hlt)
    simp only [hn, nKids] at hec hclt
    have hcl := lt_of_get hec
    have hem := ent_mem h hj
    have hkidm : ArenaCore.Bytes.leToNat (readMem y2.mem (j * 24 + 117012) 4) = e.kid := by
      rw [rd_m hcm2 (by simp only [S_HP]; omega), show j * 24 + 117012 = AR + 24 * j + 12 by simp only [AR]; omega]
      exact hem.2.1
    have hkm : ArenaCore.Bytes.leToNat (readMem y2.mem ((e.kid + (nRev ks - 1 - revBelow ks (key.getD o 0))) * 4
        + 6662472) 4) = childIdx K e.kid (nRev ks) (revBelow ks (key.getD o 0)) := by
      rw [rd_m hcm2 (by simp only [S_HP]; omega), show (e.kid + (nRev ks - 1 - revBelow ks (key.getD o 0))) * 4
        + 6662472 = KL + 4 * (e.kid + (nRev ks - 1 - revBelow ks (key.getD o 0))) by simp only [KL]; omega]
      exact k_mem h (by omega)
    have hrm : ArenaCore.Bytes.leToNat (readMem y2.mem
        (childIdx K e.kid (nRev ks) (revBelow ks (key.getD o 0)) * 24 + 117016) 4) =
        (A.getD (childIdx K e.kid (nRev ks) (revBelow ks (key.getD o 0))) default).res := by
      rw [rd_m hcm2 (by simp only [S_HP]; omega), show childIdx K e.kid (nRev ks) (revBelow ks (key.getD o 0)) * 24
        + 117016 = AR + 24 * childIdx K e.kid (nRev ks) (revBelow ks (key.getD o 0)) + 16 by
        simp only [AR]; omega, getD_of hec]
      exact (ent_mem h hec).2.2
    walk_vc [g0, g14]
    rw [wp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, g14])
      (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega) (by simp)]
    walk_vc [g0, g14, hkidm, hp6]
    rw [wp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, g14])
      (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega) (by simp)]
    walk_vc [g0, g14, hkm]
    rw [wp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, g14])
      (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega) (by simp)]
    walk_vc [g0, g14, hrm]
    refine ⟨⟨by simp [setReg_apply, g3], by simp [setReg_apply, g7], by simp [setReg_apply, g9],
      by simp [setReg_apply, g14], by simp [setReg_apply, g15], hcm2⟩, ?_⟩
    simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, g1, g2]
    exact Or.inr ⟨hoL, trivial, trivial⟩
  · exact ⟨⟨by simp [setReg_apply, hc3], by simp [setReg_apply, hc7], by simp [setReg_apply, hc9],
      by simp [setReg_apply, hc14], by simp [setReg_apply, hc15], hcm⟩, Or.inl hoL⟩


set_option maxHeartbeats 1000000 in
theorem walkBrStop_twp (h : TrieSt cb pb rs R A K vals m) {key : List Nat}
    (hkey : readMem m.mem S_KEY key.length = nibBytes key) (hk16 : ∀ x ∈ key, x < 16) (hkl : key.length ≤ 130)
    {y : M} (hc : Com key.length A.length m y) {j o : Nat} {e : Ent} (hj : A[j]? = some e)
    {v : Option (Option (Nat × Bytes))} {ks : List (Option (Option Bytes))} {mm : Nat} (hn : e.nf = .branch v ks mm)
    (h0 : y.regs 0 = j) (h1 : y.regs 1 = o) (h5 : y.regs 5 = e.pre) (ho : o = key.length) :
    twp P (Inp pub cb pb) pWalkBranch y (fun y' c => Com key.length A.length m y' ∧ y'.regs 2 = 0 ∧
      y'.regs 0 = j ∧ c ≤ 10) := by
  obtain ⟨hc3, hc7, hc9, hc14, hc15, hcm⟩ := hc
  simp only [pWalkBranch]
  walk_vc [hc3, hc15, hc14, h1, h5, h0, ho]
  exact ⟨by decide, by simp [setReg_apply, hc3], by simp [setReg_apply, hc7], by simp [setReg_apply, hc9],
      by simp [setReg_apply, hc14], by simp [setReg_apply, hc15], hcm⟩

set_option maxHeartbeats 1000000 in
theorem walkBrStep_twp (h : TrieSt cb pb rs R A K vals m) {key : List Nat}
    (hkey : readMem m.mem S_KEY key.length = nibBytes key) (hk16 : ∀ x ∈ key, x < 16) (hkl : key.length ≤ 130)
    {y : M} (hc : Com key.length A.length m y) {j o : Nat} {e : Ent} (hj : A[j]? = some e)
    {v : Option (Option (Nat × Bytes))} {ks : List (Option (Option Bytes))} {mm : Nat} (hn : e.nf = .branch v ks mm)
    (h0 : y.regs 0 = j) (h1 : y.regs 1 = o) (h5 : y.regs 5 = e.pre) (hoL : o < key.length) (hks : ks[key.getD o 0]? = some (some none)) :
    twp P (Inp pub cb pb) pWalkBranch y (fun y' c => Com key.length A.length m y' ∧ y'.regs 2 = y.regs 2 ∧
      y'.regs 1 = o + 1 ∧
      y'.regs 0 = (A.getD (childIdx K e.kid (nRev ks) (revBelow ks (key.getD o 0))) default).res ∧ c ≤ 250) := by
  obtain ⟨hc3, hc7, hc9, hc14, hc15, hcm⟩ := hc
  obtain ⟨-, hl16, hex, hpf, hpe⟩ := br_hdr h hj hn
  simp only [PF] at hpf
  have hjl := lt_of_get hj
  have hN := h.tok.wf.len_le
  simp only [NCAP] at hN
  have hexy : ArenaCore.Bytes.leToNat (readMem y.mem (e.pre - 2) 2) = bitsRev ks 0 := by
    rw [rd_m hcm (by simp only [S_HP]; omega)]; exact hex
  have hbl : bitsRev ks 0 < 65536 := by have := bitsRev_lt ks; rw [hl16] at this; simpa using this
  simp only [pWalkBranch]
  walk_vc [hc3, hc15, hc14, h1, h5, h0]
  have hne : ¬ o = key.length := by omega
  have hnk : (y.mem (o + 512)).toNat = key.getD o 0 := by
    rw [hcm _ (by simp only [S_HP]; omega), Nat.add_comm]; exact mem_key hkey hk16 hoL
  have hn16 : key.getD o 0 < 16 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hoL]; exact hk16 _ (List.getElem_mem _)
  refine Or.inl ⟨by omega, ?_⟩
  rw [twp_ld16 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, hc14])
    (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize, h5]; omega)
    (by simp)]
  have hsh1 : BinOp.shr.eval (bitsRev ks 0) (key.getD o 0) = bitsRev ks 0 / 2 ^ (key.getD o 0) :=
    eval_shr _ _ (by omega) (by unfold wordMod; omega)
  have hsh2 : BinOp.shr.eval (bitsRev ks 0) (key.getD o 0 + 1) = bitsRev ks 0 / 2 ^ (key.getD o 0 + 1) :=
    eval_shr _ _ (by omega) (by unfold wordMod; omega)
  walk_vc [hc3, hc15, hc14, h1, h5, h0, hnk, hexy, hsh1, hsh2, evAnd1, bitsRev_bit, hks]
  have hpc := popc_above ks hl16 _ hks
  have hdl : bitsRev ks 0 / 2 ^ (key.getD o 0 + 1) < 18446744073709551616 := by
    have := Nat.div_le_self (bitsRev ks 0) (2 ^ (key.getD o 0 + 1)); omega
  refine ⟨by decide, twp_of_spec (popc16_spec (d := 6) (s := 8) (a := 4) (b := 11) (c := 12) (by decide) (by decide)
    ⟨by simp [setReg_apply, hc15, K1], by simp [setReg_apply, hc14, K8]⟩ (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hdl)) ?_⟩
  rintro y2 c2 ⟨hp6, hm2, hF2, hpcst⟩
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, hpc] at hp6
  have g := fun r (hr : r ∉ [6, 4, 11, 12]) => (hF2 r hr).trans (by simp only [setReg_apply]; rfl)
  have g0 : y2.regs 0 = j := by rw [g 0 (by simp)]; simp [setReg_apply, h0]
  have g1 : y2.regs 1 = o + 1 := by rw [g 1 (by simp)]; simp [setReg_apply]
  have g2 : y2.regs 2 = y.regs 2 := by rw [g 2 (by simp)]; simp [setReg_apply]
  have g3 : y2.regs 3 = key.length := by rw [g 3 (by simp)]; simp [setReg_apply, hc3]
  have g7 : y2.regs 7 = A.length := by rw [g 7 (by simp)]; simp [setReg_apply, hc7]
  have g9 : y2.regs 9 = m.regs 9 := by rw [g 9 (by simp)]; simp [setReg_apply, hc9]
  have g14 : y2.regs 14 = 8 := by rw [g 14 (by simp)]; simp [setReg_apply, hc14]
  have g15 : y2.regs 15 = 1 := by rw [g 15 (by simp)]; simp [setReg_apply, hc15]
  simp only at hm2
  have hcm2 : ∀ a, (a < S_HP ∨ S_HP + 128 ≤ a) → y2.mem a = m.mem a := by
    intro a ha; rw [hm2]; exact hcm a ha
  have hlt := revBelow_lt ks _ hks
  obtain ⟨hkid, hKl⟩ := kid_range h hj
  rw [hn] at hkid
  simp only [nKids] at hkid
  simp only [NCAP] at hKl
  obtain ⟨ec, hec, hclt, -, -⟩ := child_info h.tok.wf hj (q := revBelow ks (key.getD o 0)) (by rw [hn]; exact hlt)
  simp only [hn, nKids] at hec hclt
  have hcl := lt_of_get hec
  have hem := ent_mem h hj
  have hkidm : ArenaCore.Bytes.leToNat (readMem y2.mem (j * 24 + 117012) 4) = e.kid := by
    rw [rd_m hcm2 (by simp only [S_HP]; omega), show j * 24 + 117012 = AR + 24 * j + 12 by simp only [AR]; omega]
    exact hem.2.1
  have hkm : ArenaCore.Bytes.leToNat (readMem y2.mem ((e.kid + (nRev ks - 1 - revBelow ks (key.getD o 0))) * 4
      + 6662472) 4) = childIdx K e.kid (nRev ks) (revBelow ks (key.getD o 0)) := by
    rw [rd_m hcm2 (by simp only [S_HP]; omega), show (e.kid + (nRev ks - 1 - revBelow ks (key.getD o 0))) * 4
      + 6662472 = KL + 4 * (e.kid + (nRev ks - 1 - revBelow ks (key.getD o 0))) by simp only [KL]; omega]
    exact k_mem h (by omega)
  have hrm : ArenaCore.Bytes.leToNat (readMem y2.mem
      (childIdx K e.kid (nRev ks) (revBelow ks (key.getD o 0)) * 24 + 117016) 4) =
      (A.getD (childIdx K e.kid (nRev ks) (revBelow ks (key.getD o 0))) default).res := by
    rw [rd_m hcm2 (by simp only [S_HP]; omega), show childIdx K e.kid (nRev ks) (revBelow ks (key.getD o 0)) * 24
      + 117016 = AR + 24 * childIdx K e.kid (nRev ks) (revBelow ks (key.getD o 0)) + 16 by
      simp only [AR]; omega, getD_of hec]
    exact (ent_mem h hec).2.2
  walk_vc [g0, g14]
  rw [twp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, g14])
    (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega) (by simp)]
  walk_vc [g0, g14, hkidm, hp6]
  rw [twp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, g14])
    (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega) (by simp)]
  walk_vc [g0, g14, hkm]
  rw [twp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, g14])
    (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega) (by simp)]
  walk_vc [g0, g14, hrm]
  refine ⟨⟨by simp [setReg_apply, g3], by simp [setReg_apply, g7], by simp [setReg_apply, g9],
    by simp [setReg_apply, g14], by simp [setReg_apply, g15], hcm2⟩, ?_⟩
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, g1, g2, true_and]
  omega

end

end ReexecNpai
