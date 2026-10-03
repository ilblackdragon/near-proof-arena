import ReexecNpai.Spec.WalkAux2

/-!
# Helper lemmas for `Spec/Walk.lean`: one walk step per node kind
-/

set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1 WalkProof WalkAux

namespace WalkAux

/-- Loop-invariant registers and memory of the walk (memory changes only in `S_HP`). -/
def Com (L N : Nat) (m x : M) : Prop :=
  x.regs 3 = L ∧ x.regs 7 = N ∧ x.regs 9 = m.regs 9 ∧ x.regs 14 = 8 ∧ x.regs 15 = 1 ∧
  ∀ a, (a < S_HP ∨ S_HP + 128 ≤ a) → x.mem a = m.mem a

theorem rd_out {L N : Nat} {m x : M} (hc : Com L N m x) {a n : Nat} (h : a + n ≤ S_HP ∨ S_HP + 128 ≤ a) :
    readMem x.mem a n = readMem m.mem a n := by
  rw [readMem_ext]; intro i hi; exact hc.2.2.2.2.2 _ (by omega)

theorem hp_mem {m y y2 : M} {n : Nat} {HP : List UInt8} (hm : y2.mem = writeMem y.mem S_HP n HP) (hn : n ≤ 128)
    (hcm : ∀ a, (a < S_HP ∨ S_HP + 128 ≤ a) → y.mem a = m.mem a) :
    ∀ a, (a < S_HP ∨ S_HP + 128 ≤ a) → y2.mem a = m.mem a := by
  intro a ha; rw [hm, writeMem_apply_out' _ _ _ _ _ (by omega)]; exact hcm a ha

theorem hp_read {y y2 : M} {n : Nat} {HP : List UInt8} (hm : y2.mem = writeMem y.mem S_HP n HP)
    (hn : HP.length = n) : readMem y2.mem S_HP n = HP := by
  rw [hm, readMem_writeMem_sub _ _ _ _ _ _ (Nat.le_refl _) (Nat.le_refl _) (by omega)]
  simp [← hn]

theorem rd_m {m x : M} (hcm : ∀ a, (a < S_HP ∨ S_HP + 128 ≤ a) → x.mem a = m.mem a) {a n : Nat}
    (h : a + n ≤ S_HP ∨ S_HP + 128 ≤ a) : readMem x.mem a n = readMem m.mem a n := by
  rw [readMem_ext]; intro i hi; exact hcm _ (by omega)

theorem evXor1 (c : Prop) [Decidable c] : BinOp.xor.eval (if c then 1 else 0) 1 = if c then 0 else 1 := by
  by_cases h : c <;> simp [h] <;> rfl

section
variable {cb pb : Bytes} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → Bytes} {m : M}

theorem ent_mem (h : TrieSt cb pb rs R A K vals m) {j : Nat} {e : Ent} (hj : A[j]? = some e) :
    ArenaCore.Bytes.leToNat (readMem m.mem (AR + 24 * j) 4) = e.pre ∧
    ArenaCore.Bytes.leToNat (readMem m.mem (AR + 24 * j + 12) 4) = e.kid ∧
    ArenaCore.Bytes.leToNat (readMem m.mem (AR + 24 * j + 16) 4) = e.res := by
  have hl := lt_of_get hj
  obtain ⟨h1, -, -, h4, h5, -⟩ := h.tmem.amem j hl
  rw [getD_of' hj hl] at h1 h4 h5
  exact ⟨h1, h4, h5⟩

theorem k_mem (h : TrieSt cb pb rs R A K vals m) {i : Nat} (hi : i < K.length) :
    ArenaCore.Bytes.leToNat (readMem m.mem (KL + 4 * i) 4) = K.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact h.tmem.kmem i hi

theorem kid_range (h : TrieSt cb pb rs R A K vals m) {j : Nat} {e : Ent} (hj : A[j]? = some e) :
    e.kid + nKids e.nf ≤ K.length ∧ K.length ≤ NCAP := by
  have hl := lt_of_get hj
  have := h.tmem.krange j hl
  rw [getD_of' hj hl] at this
  exact ⟨this, h.tmem.klen⟩

end

end WalkAux

open WalkAux

section
variable {pub cb pb : Bytes} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → Bytes} {m : M}

theorem walkLeaf_wp (h : TrieSt cb pb rs R A K vals m) {key : List Nat}
    (hkey : readMem m.mem S_KEY key.length = nibBytes key) (hk16 : ∀ x ∈ key, x < 16) (hkl : key.length ≤ 130)
    {y : M} (hc : Com key.length A.length m y) {j o : Nat} {e : Ent} (hj : A[j]? = some e)
    {k : List Nat} {ref : Option (Nat × Bytes)} {mm : Nat} (hn : e.nf = .leaf k ref mm)
    (h0 : y.regs 0 = j) (h1 : y.regs 1 = o) (h5 : y.regs 5 = e.pre) (ho : o ≤ key.length) :
    wp P (Inp pub cb pb) pWalkLeaf y (fun y' => Com key.length A.length m y' ∧ y'.regs 2 = 0 ∧ y'.regs 0 = j ∧
      key.drop o = k) := by
  obtain ⟨hc3, hc7, hc9, hc14, hc15, hcm⟩ := hc
  obtain ⟨ht, hl, hhp, hend, hpf, hk⟩ := leaf_hdr h hj hn
  simp only [PF] at hpf
  have hkeyy : readMem y.mem S_KEY key.length = nibBytes key := by
    rw [rd_m hcm (by simp only [S_KEY, S_HP]; omega)]; exact hkey
  simp only [pWalkLeaf]
  walk_vc [hc3, hc15, hc14, h1, h5]
  refine wp_of_spec (walkHP_twp (key := key) (lf := true) (by simp [setReg_apply, hc15]) (by simp [setReg_apply, hc14])
    hkeyy hk16 hkl (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h1]; omega) (by simp [setReg_apply])) ?_
  rintro y2 c2 ⟨hm2, h62, hF2, -⟩
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h1] at hm2 h62
  have g := fun r (hr : r ∉ [4, 6, 8, 11, 12, 13]) => (hF2 r hr).trans (by simp only [setReg_apply]; rfl)
  have g5 : y2.regs 5 = e.pre := by rw [g 5 (by simp)]; simp [setReg_apply, h5]
  have g0 : y2.regs 0 = j := by rw [g 0 (by simp)]; simp [setReg_apply, h0]
  have g3 : y2.regs 3 = key.length := by rw [g 3 (by simp)]; simp [setReg_apply, hc3]
  have g7 : y2.regs 7 = A.length := by rw [g 7 (by simp)]; simp [setReg_apply, hc7]
  have g9 : y2.regs 9 = m.regs 9 := by rw [g 9 (by simp)]; simp [setReg_apply, hc9]
  have g14 : y2.regs 14 = 8 := by rw [g 14 (by simp)]; simp [setReg_apply, hc14]
  have g15 : y2.regs 15 = 1 := by rw [g 15 (by simp)]; simp [setReg_apply, hc15]
  have hcm2 := hp_mem hm2 (by omega) hcm
  have hrd : readMem y2.mem (e.pre + 1) 4 = readMem m.mem (e.pre + 1) 4 := rd_m hcm2 (by simp only [S_HP]; omega)
  have hrd2 : readMem y2.mem (e.pre + 5) (List.length (hexPrefix k true)) = hexPrefix k true := by
    rw [rd_m hcm2 (by simp only [S_HP]; omega)]; exact hhp
  have hrd3 := hp_read hm2 (by rw [hexPrefix_len]; simp only [List.length_take, List.length_drop]; omega)
  simp only [S_HP] at hrd3
  walk_vc [g5, g0, g3, g7, g9, g14, g15, h62, hrd, hl]
  rw [wp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, g14])
    (by simp [setReg_apply]; omega) (by simp)]
  walk_vc [g5, g0, g3, g7, g9, g14, g15, h62, hrd, hl]
  intro hlen _ _ heq
  rw [hrd2, hlen, hrd3, List.take_of_length_le (by simp)] at heq
  refine ⟨⟨by simp [setReg_apply, g3], by simp [setReg_apply, g7], by simp [setReg_apply, g9],
    by simp [setReg_apply, g14], by simp [setReg_apply, g15], hcm2⟩,
    hexPrefix_inj _ _ true (fun x hx => hk16 x (List.mem_of_mem_drop hx)) hk heq⟩


theorem walkLeaf_twp (h : TrieSt cb pb rs R A K vals m) {key : List Nat}
    (hkey : readMem m.mem S_KEY key.length = nibBytes key) (hk16 : ∀ x ∈ key, x < 16) (hkl : key.length ≤ 130)
    {y : M} (hc : Com key.length A.length m y) {j o : Nat} {e : Ent} (hj : A[j]? = some e)
    {k : List Nat} {ref : Option (Nat × Bytes)} {mm : Nat} (hn : e.nf = .leaf k ref mm)
    (h0 : y.regs 0 = j) (h1 : y.regs 1 = o) (h5 : y.regs 5 = e.pre) (ho : o ≤ key.length) (hkd : key.drop o = k) :
    twp P (Inp pub cb pb) pWalkLeaf y (fun y' c => Com key.length A.length m y' ∧ y'.regs 2 = 0 ∧ y'.regs 0 = j ∧
      c ≤ 60 + 6 * (key.length - o)) := by
  obtain ⟨hc3, hc7, hc9, hc14, hc15, hcm⟩ := hc
  obtain ⟨ht, hl, hhp, hend, hpf, hk⟩ := leaf_hdr h hj hn
  simp only [PF] at hpf
  have hkeyy : readMem y.mem S_KEY key.length = nibBytes key := by
    rw [rd_m hcm (by simp only [S_KEY, S_HP]; omega)]; exact hkey
  simp only [pWalkLeaf]
  walk_vc [hc3, hc15, hc14, h1, h5]
  refine twp_mono (walkHP_twp (key := key) (lf := true) (by simp [setReg_apply, hc15]) (by simp [setReg_apply, hc14])
    hkeyy hk16 hkl (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h1]; omega) (by simp [setReg_apply])) ?_
  rintro y2 c2 ⟨hm2, h62, hF2, hcost⟩
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h1] at hm2 h62 hcost
  have g := fun r (hr : r ∉ [4, 6, 8, 11, 12, 13]) => (hF2 r hr).trans (by simp only [setReg_apply]; rfl)
  have g5 : y2.regs 5 = e.pre := by rw [g 5 (by simp)]; simp [setReg_apply, h5]
  have g0 : y2.regs 0 = j := by rw [g 0 (by simp)]; simp [setReg_apply, h0]
  have g3 : y2.regs 3 = key.length := by rw [g 3 (by simp)]; simp [setReg_apply, hc3]
  have g7 : y2.regs 7 = A.length := by rw [g 7 (by simp)]; simp [setReg_apply, hc7]
  have g9 : y2.regs 9 = m.regs 9 := by rw [g 9 (by simp)]; simp [setReg_apply, hc9]
  have g14 : y2.regs 14 = 8 := by rw [g 14 (by simp)]; simp [setReg_apply, hc14]
  have g15 : y2.regs 15 = 1 := by rw [g 15 (by simp)]; simp [setReg_apply, hc15]
  have hcm2 := hp_mem hm2 (by omega) hcm
  have hrd : readMem y2.mem (e.pre + 1) 4 = readMem m.mem (e.pre + 1) 4 := rd_m hcm2 (by simp only [S_HP]; omega)
  have hrd2 : readMem y2.mem (e.pre + 5) (List.length (hexPrefix k true)) = hexPrefix k true := by
    rw [rd_m hcm2 (by simp only [S_HP]; omega)]; exact hhp
  have hrd3 := hp_read hm2 (by rw [hexPrefix_len]; simp only [List.length_take, List.length_drop]; omega)
  simp only [S_HP] at hrd3
  walk_vc [g5, g0, g3, g7, g9, g14, g15, h62, hrd, hl]
  rw [twp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, g14])
    (by simp [setReg_apply]; omega) (by simp)]
  walk_vc [g5, g0, g3, g7, g9, g14, g15, h62, hrd, hl]
  have hlen : (hexPrefix k true).length = 1 + (key.length - o) / 2 := by
    rw [hexPrefix_len, ← hkd, List.length_drop]
  refine ⟨hlen, by omega, by omega, ?_, ⟨by simp [setReg_apply, g3], by simp [setReg_apply, g7],
    by simp [setReg_apply, g9], by simp [setReg_apply, g14], by simp [setReg_apply, g15], hcm2⟩, ?_⟩
  · rw [hrd2, hlen, hrd3, List.take_of_length_le (by simp), hkd]
  · rw [hlen]; omega

set_option maxHeartbeats 1000000 in
theorem walkExt_wp (h : TrieSt cb pb rs R A K vals m) {key : List Nat}
    (hkey : readMem m.mem S_KEY key.length = nibBytes key) (hk16 : ∀ x ∈ key, x < 16) (hkl : key.length ≤ 130)
    {y : M} (hc : Com key.length A.length m y) {j o : Nat} {e : Ent} (hj : A[j]? = some e)
    {k : List Nat} {hh : Option Bytes} {mm : Nat} (hn : e.nf = .ext k hh mm)
    (h0 : y.regs 0 = j) (h1 : y.regs 1 = o) (h5 : y.regs 5 = e.pre) (ho : o ≤ key.length) :
    wp P (Inp pub cb pb) pWalkExt y (fun y' => Com key.length A.length m y' ∧ y'.regs 2 = y.regs 2 ∧
      hh = none ∧ o + k.length ≤ key.length ∧ (key.drop o).take k.length = k ∧ y'.regs 1 = o + k.length ∧
      y'.regs 0 = (A.getD (K.getD e.kid 0) default).res) := by
  obtain ⟨hc3, hc7, hc9, hc14, hc15, hcm⟩ := hc
  obtain ⟨ht, hl, hhp, hend, hpf, hk, hfl⟩ := ext_hdr h hj hn
  simp only [PF] at hpf
  have hjl := lt_of_get hj
  have hN := h.tok.wf.len_le
  simp only [NCAP] at hN
  have hlen := hexPrefix_len k false
  have hy1 : ArenaCore.Bytes.leToNat (readMem y.mem (e.pre + 1) 4) = 1 + k.length / 2 := by
    rw [rd_m hcm (by simp only [S_HP]; omega), hl, hlen]
  have hy5 : y.mem (e.pre + 5) = (hexPrefix k false).getD 0 0 := by
    rw [hcm _ (by simp only [S_HP]; omega)]
    have := congrArg (fun l => l.getD 0 0) hhp
    simp only [readMem, hlen, Nat.add_comm 1, List.range_succ_eq_map, List.map_cons, List.getD_cons_zero,
      Nat.add_zero] at this
    exact this
  have hk0 : k.getD 0 0 < 16 := by
    cases k with
    | nil => simp
    | cons a r => exact hk a (by simp)
  have hv : (y.mem (e.pre + 5)).toNat = if k.length % 2 = 1 then 16 + k.getD 0 0 else 0 := by
    rw [hy5, hexPrefix_getD0]
    split <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, UInt8.toNat_ofNat', Nat.reducePow] <;> omega
  have hxr : BinOp.xor.eval (if (y.mem (e.pre + 5)).toNat = 0 then 1 else 0) 1 = k.length % 2 := by
    rw [hv]
    by_cases hp : k.length % 2 = 1
    · rw [ite_pos hp, ite_neg (by omega), hp]; rfl
    · rw [ite_neg hp, ite_pos rfl, show k.length % 2 = 0 by omega]; rfl
  simp only [pWalkExt]
  walk_vc [hc3, hc15, hc14, h1, h5, h0]
  rw [wp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, hc14])
    (by simp [setReg_apply, h5]; omega) (by simp)]
  walk_vc [hc3, hc15, hc14, h1, h5, h0, hy1]
  intro y1 _ e1; subst e1
  walk_vc [hc3, hc15, hc14, h1, h5, h0, hxr]
  intro hkl'
  have hK : 1 + k.length / 2 - 1 + (1 + k.length / 2 - 1) + k.length % 2 = k.length := by omega
  simp only [hK] at hkl' ⊢
  have hkL : o + k.length ≤ key.length := by omega
  have hkeyy : readMem y.mem S_KEY key.length = nibBytes key := by
    rw [rd_m hcm (by simp only [S_KEY, S_HP]; omega)]; exact hkey
  refine wp_of_spec (walkHP_twp (key := key) (lf := false) (by simp [setReg_apply, hc15]) (by simp [setReg_apply, hc14])
    hkeyy hk16 hkl (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h1]; omega) (by simp [setReg_apply])) ?_
  rintro y2 c2 ⟨hm2, h62, hF2, -⟩
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h1] at hm2 h62
  have g := fun r (hr : r ∉ [4, 6, 8, 11, 12, 13]) => (hF2 r hr).trans (by simp only [setReg_apply]; rfl)
  have g5 : y2.regs 5 = e.pre := by rw [g 5 (by simp)]; simp [setReg_apply, h5]
  have g0 : y2.regs 0 = j := by rw [g 0 (by simp)]; simp [setReg_apply, h0]
  have g1 : y2.regs 1 = o := by rw [g 1 (by simp)]; simp [setReg_apply, h1]
  have g2 : y2.regs 2 = y.regs 2 := by rw [g 2 (by simp)]; simp [setReg_apply]
  have g3 : y2.regs 3 = key.length := by rw [g 3 (by simp)]; simp [setReg_apply, hc3]
  have g7 : y2.regs 7 = A.length := by rw [g 7 (by simp)]; simp [setReg_apply, hc7]
  have g9 : y2.regs 9 = m.regs 9 := by rw [g 9 (by simp)]; simp [setReg_apply, hc9]
  have g10 : y2.regs 10 = k.length := by rw [g 10 (by simp)]; simp [setReg_apply]
  have g14 : y2.regs 14 = 8 := by rw [g 14 (by simp)]; simp [setReg_apply, hc14]
  have g15 : y2.regs 15 = 1 := by rw [g 15 (by simp)]; simp [setReg_apply, hc15]
  have hcm2 := hp_mem hm2 (by omega) hcm
  have hrd2 : readMem y2.mem (e.pre + 5) (List.length (hexPrefix k false)) = hexPrefix k false := by
    rw [rd_m hcm2 (by simp only [S_HP]; omega)]; exact hhp
  have hrd3 := hp_read hm2 (by rw [hexPrefix_len]; simp only [List.length_take, List.length_drop]; omega)
  simp only [S_HP] at hrd3
  have hfl2 : (y2.mem (e.pre - 1)).toNat = if hh.isNone = true then 1 else 0 := by
    rw [hcm2 _ (by simp only [S_HP]; omega)]; exact hfl
  obtain ⟨hkid, hKl⟩ := kid_range h hj
  have hem := ent_mem h hj
  walk_vc [g5, g0, g1, g2, g3, g7, g9, g10, g14, g15, h62, hfl2]
  intro _ _ heq y3 _ e3; subst e3
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, ite10_ne_zero]
  intro hnone
  have hhn : hh = none := by
    cases hh with
    | none => rfl
    | some _ => simp at hnone
  subst hhn
  rw [hrd3, ← hlen, hrd2] at heq
  have htk : (key.drop o).take k.length = k :=
    hexPrefix_inj _ _ false (fun x hx => hk16 x (List.mem_of_mem_drop (List.mem_of_mem_take hx))) hk heq
  rw [hn] at hkid
  simp only [nKids, Option.isNone_none, ↓reduceIte] at hkid
  simp only [NCAP] at hKl
  obtain ⟨ec, hec, hclt, -, -⟩ := ext_child h.tok.wf hj hn
  have hcl := lt_of_get hec
  have hkidm : ArenaCore.Bytes.leToNat (readMem y2.mem (j * 24 + 117012) 4) = e.kid := by
    rw [rd_m hcm2 (by simp only [S_HP]; omega), show j * 24 + 117012 = AR + 24 * j + 12 by simp only [AR]; omega]
    exact hem.2.1
  have hkm : ArenaCore.Bytes.leToNat (readMem y2.mem (e.kid * 4 + 6662472) 4) = K.getD e.kid 0 := by
    rw [rd_m hcm2 (by simp only [S_HP]; omega), show e.kid * 4 + 6662472 = KL + 4 * e.kid by simp only [KL]; omega]
    exact k_mem h (by omega)
  have hrm : ArenaCore.Bytes.leToNat (readMem y2.mem (K.getD e.kid 0 * 24 + 117016) 4) =
      (A.getD (K.getD e.kid 0) default).res := by
    rw [rd_m hcm2 (by simp only [S_HP]; omega), show K.getD e.kid 0 * 24 + 117016 = AR + 24 * K.getD e.kid 0 + 16 by
      simp only [AR]; omega, getD_of hec]
    exact (ent_mem h hec).2.2
  walk_vc [g0, g14]
  rw [wp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, g14])
    (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega) (by simp)]
  walk_vc [g0, g14, hkidm]
  rw [wp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, g14])
    (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega) (by simp)]
  walk_vc [g0, g14, hkm]
  rw [wp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, g14])
    (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega) (by simp)]
  walk_vc [g0, g14, hrm]
  refine ⟨⟨by simp [setReg_apply, g3], by simp [setReg_apply, g7], by simp [setReg_apply, g9],
    by simp [setReg_apply, g14], by simp [setReg_apply, g15], hcm2⟩, ?_⟩
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, g2, hkL, htk, true_and]


set_option maxHeartbeats 1000000 in
theorem walkExt_twp (h : TrieSt cb pb rs R A K vals m) {key : List Nat}
    (hkey : readMem m.mem S_KEY key.length = nibBytes key) (hk16 : ∀ x ∈ key, x < 16) (hkl : key.length ≤ 130)
    {y : M} (hc : Com key.length A.length m y) {j o : Nat} {e : Ent} (hj : A[j]? = some e)
    {k : List Nat} {hh : Option Bytes} {mm : Nat} (hn : e.nf = .ext k hh mm)
    (h0 : y.regs 0 = j) (h1 : y.regs 1 = o) (h5 : y.regs 5 = e.pre) (ho : o ≤ key.length)
    (hhn : hh = none) (hkL : o + k.length ≤ key.length) (htk : (key.drop o).take k.length = k) :
    twp P (Inp pub cb pb) pWalkExt y (fun y' c => Com key.length A.length m y' ∧ y'.regs 2 = y.regs 2 ∧
      y'.regs 1 = o + k.length ∧ y'.regs 0 = (A.getD (K.getD e.kid 0) default).res ∧ c ≤ 130 + 6 * k.length) := by
  obtain ⟨hc3, hc7, hc9, hc14, hc15, hcm⟩ := hc
  obtain ⟨ht, hl, hhp, hend, hpf, hk, hfl⟩ := ext_hdr h hj hn
  simp only [PF] at hpf
  have hjl := lt_of_get hj
  have hN := h.tok.wf.len_le
  simp only [NCAP] at hN
  have hlen := hexPrefix_len k false
  have hy1 : ArenaCore.Bytes.leToNat (readMem y.mem (e.pre + 1) 4) = 1 + k.length / 2 := by
    rw [rd_m hcm (by simp only [S_HP]; omega), hl, hlen]
  have hy5 : y.mem (e.pre + 5) = (hexPrefix k false).getD 0 0 := by
    rw [hcm _ (by simp only [S_HP]; omega)]
    have := congrArg (fun l => l.getD 0 0) hhp
    simp only [readMem, hlen, Nat.add_comm 1, List.range_succ_eq_map, List.map_cons, List.getD_cons_zero,
      Nat.add_zero] at this
    exact this
  have hk0 : k.getD 0 0 < 16 := by
    cases k with
    | nil => simp
    | cons a r => exact hk a (by simp)
  have hv : (y.mem (e.pre + 5)).toNat = if k.length % 2 = 1 then 16 + k.getD 0 0 else 0 := by
    rw [hy5, hexPrefix_getD0]
    split <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, UInt8.toNat_ofNat', Nat.reducePow] <;> omega
  have hxr : BinOp.xor.eval (if (y.mem (e.pre + 5)).toNat = 0 then 1 else 0) 1 = k.length % 2 := by
    rw [hv]
    by_cases hp : k.length % 2 = 1
    · rw [ite_pos hp, ite_neg (by omega), hp]; rfl
    · rw [ite_neg hp, ite_pos rfl, show k.length % 2 = 0 by omega]; rfl
  simp only [pWalkExt]
  walk_vc [hc3, hc15, hc14, h1, h5, h0]
  rw [twp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, hc14])
    (by simp [setReg_apply, h5]; omega) (by simp)]
  walk_vc [hc3, hc15, hc14, h1, h5, h0, hy1, hxr]
  have hK : 1 + k.length / 2 - 1 + (1 + k.length / 2 - 1) + k.length % 2 = k.length := by omega
  simp only [hK]
  have hkeyy : readMem y.mem S_KEY key.length = nibBytes key := by
    rw [rd_m hcm (by simp only [S_KEY, S_HP]; omega)]; exact hkey
  refine ⟨by omega, by omega, twp_mono (walkHP_twp (key := key) (lf := false) (by simp [setReg_apply, hc15])
    (by simp [setReg_apply, hc14]) hkeyy hk16 hkl (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h1]; omega)
    (by simp [setReg_apply])) ?_⟩
  rintro y2 c2 ⟨hm2, h62, hF2, hcost⟩
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h1] at hm2 h62 hcost
  have g := fun r (hr : r ∉ [4, 6, 8, 11, 12, 13]) => (hF2 r hr).trans (by simp only [setReg_apply]; rfl)
  have g5 : y2.regs 5 = e.pre := by rw [g 5 (by simp)]; simp [setReg_apply, h5]
  have g0 : y2.regs 0 = j := by rw [g 0 (by simp)]; simp [setReg_apply, h0]
  have g1 : y2.regs 1 = o := by rw [g 1 (by simp)]; simp [setReg_apply, h1]
  have g2 : y2.regs 2 = y.regs 2 := by rw [g 2 (by simp)]; simp [setReg_apply]
  have g3 : y2.regs 3 = key.length := by rw [g 3 (by simp)]; simp [setReg_apply, hc3]
  have g7 : y2.regs 7 = A.length := by rw [g 7 (by simp)]; simp [setReg_apply, hc7]
  have g9 : y2.regs 9 = m.regs 9 := by rw [g 9 (by simp)]; simp [setReg_apply, hc9]
  have g10 : y2.regs 10 = k.length := by rw [g 10 (by simp)]; simp [setReg_apply]
  have g14 : y2.regs 14 = 8 := by rw [g 14 (by simp)]; simp [setReg_apply, hc14]
  have g15 : y2.regs 15 = 1 := by rw [g 15 (by simp)]; simp [setReg_apply, hc15]
  have hcm2 := hp_mem hm2 (by omega) hcm
  have hrd2 : readMem y2.mem (e.pre + 5) (List.length (hexPrefix k false)) = hexPrefix k false := by
    rw [rd_m hcm2 (by simp only [S_HP]; omega)]; exact hhp
  have hrd3 := hp_read hm2 (by rw [hexPrefix_len]; simp only [List.length_take, List.length_drop]; omega)
  simp only [S_HP] at hrd3
  have hfl2 : (y2.mem (e.pre - 1)).toNat = 1 := by
    rw [hcm2 _ (by simp only [S_HP]; omega), hfl, hhn]; rfl
  obtain ⟨hkid, hKl⟩ := kid_range h hj
  have hem := ent_mem h hj
  rw [hn, hhn] at hkid
  simp only [nKids, Option.isNone_none, ↓reduceIte] at hkid
  simp only [NCAP] at hKl
  obtain ⟨ec, hec, hclt, -, -⟩ := ext_child h.tok.wf hj (hhn ▸ hn)
  have hcl := lt_of_get hec
  have hkidm : ArenaCore.Bytes.leToNat (readMem y2.mem (j * 24 + 117012) 4) = e.kid := by
    rw [rd_m hcm2 (by simp only [S_HP]; omega), show j * 24 + 117012 = AR + 24 * j + 12 by simp only [AR]; omega]
    exact hem.2.1
  have hkm : ArenaCore.Bytes.leToNat (readMem y2.mem (e.kid * 4 + 6662472) 4) = K.getD e.kid 0 := by
    rw [rd_m hcm2 (by simp only [S_HP]; omega), show e.kid * 4 + 6662472 = KL + 4 * e.kid by simp only [KL]; omega]
    exact k_mem h (by omega)
  have hrm : ArenaCore.Bytes.leToNat (readMem y2.mem (K.getD e.kid 0 * 24 + 117016) 4) =
      (A.getD (K.getD e.kid 0) default).res := by
    rw [rd_m hcm2 (by simp only [S_HP]; omega), show K.getD e.kid 0 * 24 + 117016 = AR + 24 * K.getD e.kid 0 + 16 by
      simp only [AR]; omega, getD_of hec]
    exact (ent_mem h hec).2.2
  have heq : readMem y2.mem 768 (1 + k.length / 2) = readMem y2.mem (e.pre + 5) (1 + k.length / 2) := by
    rw [hrd3, ← hlen, hrd2, htk]
  walk_vc [g5, g0, g1, g2, g3, g7, g9, g10, g14, g15, h62, hfl2, heq]
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  rw [twp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, g14])
    (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega) (by simp)]
  walk_vc [g0, g14, hkidm]
  rw [twp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, g14])
    (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega) (by simp)]
  walk_vc [g0, g14, hkm]
  rw [twp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, g14])
    (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega) (by simp)]
  walk_vc [g0, g14, hrm]
  refine ⟨⟨by simp [setReg_apply, g3], by simp [setReg_apply, g7], by simp [setReg_apply, g9],
    by simp [setReg_apply, g14], by simp [setReg_apply, g15], hcm2⟩, ?_⟩
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, g2, true_and]
  omega

end

end ReexecNpai
