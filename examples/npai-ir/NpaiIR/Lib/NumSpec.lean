import NpaiIR.WP

/-!
# Specifications of `subLE`, `mulLE`, `popc16`

(See `Lib/Num.lean` for the code and for `addLE_spec`, the model proof.)
-/

set_option maxRecDepth 8000

namespace NpaiIR

open ArenaCore Interp

variable {p : Program} {inp : Inputs}

/-- Prefix difference `a_i + 256^i - b_i - c0` of two little-endian arrays. -/
def subPref (M0 : Nat → UInt8) (A B c0 i : Nat) : Nat :=
  Bytes.leToNat (readMem M0 A i) + 256 ^ i - Bytes.leToNat (readMem M0 B i) - c0

theorem subPref_lt (M0 : Nat → UInt8) (A B c0 i : Nat) :
    subPref M0 A B c0 i < 2 * 256 ^ i := by
  have := leToNat_readMem_lt M0 A i
  simp only [subPref]; omega

theorem subPref_div (M0 : Nat → UInt8) (A B c0 i : Nat) (h : c0 ≤ 1) :
    subPref M0 A B c0 i / 256 ^ i = if Bytes.leToNat (readMem M0 A i) <
      Bytes.leToNat (readMem M0 B i) + c0 then 0 else 1 := by
  have ha := leToNat_readMem_lt M0 A i
  have hb := leToNat_readMem_lt M0 B i
  have hp : 0 < 256 ^ i := Nat.pow_pos (by omega)
  simp only [subPref]
  by_cases hc : Bytes.leToNat (readMem M0 A i) < Bytes.leToNat (readMem M0 B i) + c0
  · rw [ite_pos hc]; exact Nat.div_eq_of_lt (by omega)
  · rw [ite_neg hc]
    apply Nat.div_eq_of_lt_le <;> omega

theorem subPref_succ (M0 : Nat → UInt8) (A B c0 i : Nat) (h : c0 ≤ 1) :
    subPref M0 A B c0 (i + 1) = subPref M0 A B c0 i + 256 ^ i * ((M0 (A + i)).toNat + 255 - (M0 (B + i)).toNat) := by
  have ha := leToNat_readMem_lt M0 A i
  have hb := leToNat_readMem_lt M0 B i
  have hy := byte_lt (M0 (B + i))
  have hyle : 256 ^ i * (M0 (B + i)).toNat ≤ 256 ^ i * 255 := Nat.mul_le_mul_left _ (by omega)
  have hp : 0 < 256 ^ i := Nat.pow_pos (by omega)
  simp only [subPref, leToNat_readMem_snoc, Nat.pow_succ]
  rw [Nat.mul_sub (256 ^ i), Nat.mul_add]
  have : 256 ^ i * 256 = 256 ^ i * 255 + 256 ^ i := by omega
  rw [this]
  omega

theorem subLE_spec {m : M} (hk : Kinv m) {n : Nat} (hn : m.regs 4 = n) (hc0 : m.regs 5 ≤ 1)
    (hba : m.regs 1 + n ≤ p.memSize) (hbb : m.regs 2 + n ≤ p.memSize)
    (hbd : m.regs 3 + n ≤ p.memSize) (hw : p.memSize < 2 ^ 32)
    (hal : Alias (m.regs 3) (m.regs 1) n) (hbl : Alias (m.regs 3) (m.regs 2) n) :
    ∃ m' c, Ev p inp subLE m (.ok m') c ∧
      m'.mem = writeMem m.mem (m.regs 3) n (Bytes.leN n
        ((Bytes.leToNat (readMem m.mem (m.regs 1) n) + 256 ^ n -
          Bytes.leToNat (readMem m.mem (m.regs 2) n) - m.regs 5) % 256 ^ n)) ∧
      m'.regs 5 = (if Bytes.leToNat (readMem m.mem (m.regs 1) n) <
          Bytes.leToNat (readMem m.mem (m.regs 2) n) + m.regs 5 then 1 else 0) ∧
      m'.regs 1 = m.regs 1 + n ∧ m'.regs 2 = m.regs 2 + n ∧ m'.regs 3 = m.regs 3 + n ∧ m'.regs 4 = 0 ∧
      Frame [1, 2, 3, 4, 5, 6, 7] m m' ∧ c ≤ 14 * n + 1 := by
  obtain ⟨hk1, hk8⟩ := hk
  obtain ⟨A, hA⟩ : ∃ A, m.regs 1 = A := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, m.regs 2 = B := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, m.regs 3 = D := ⟨_, rfl⟩
  obtain ⟨c0, hC⟩ : ∃ c0, m.regs 5 = c0 := ⟨_, rfl⟩
  simp only [hA, hB, hD, hC] at hba hbb hbd hal hbl hc0 ⊢
  have hbody : ∀ j x, 0 < j → (j ≤ n ∧ x.regs 1 = A + (n - j) ∧ x.regs 2 = B + (n - j) ∧
      x.regs 3 = D + (n - j) ∧ x.regs 5 = 1 - subPref m.mem A B c0 (n - j) / 256 ^ (n - j) ∧
      x.mem = writeMem m.mem D (n - j) (Bytes.leN (n - j) (subPref m.mem A B c0 (n - j))) ∧
      Frame [1, 2, 3, 4, 5, 6, 7] m x) → x.regs 4 = j → ∃ x' c, Ev p inp (block [.ld8 6 1, .addi 6 6 256,
      .ld8 7 2, .bin .sub 6 6 7, .bin .sub 6 6 5, .st8 3 6,
      .bin .shr 7 6 K8, .bin .sub 5 K1 7, .addi 1 1 1, .addi 2 2 1, .addi 3 3 1, .bin .sub 4 4 K1]) x
      (.ok x') c ∧ ((j - 1) ≤ n ∧ x'.regs 1 = A + (n - (j - 1)) ∧
      x'.regs 2 = B + (n - (j - 1)) ∧
      x'.regs 3 = D + (n - (j - 1)) ∧ x'.regs 5 = 1 - subPref m.mem A B c0 (n - (j - 1)) / 256 ^ (n - (j - 1)) ∧
      x'.mem = writeMem m.mem D (n - (j - 1)) (Bytes.leN (n - (j - 1)) (subPref m.mem A B c0 (n - (j - 1)))) ∧
      Frame [1, 2, 3, 4, 5, 6, 7] m x') ∧ x'.regs 4 = j - 1 ∧ c ≤ 12 := by
    intro j x hj ⟨hjn, hxa, hxb, hxd, hxc, hxm, hfr⟩ hxk
    have hx1 : x.regs 15 = 1 := by rw [hfr 15 (by decide)]; exact hk1
    have hx8 : x.regs 14 = 8 := by rw [hfr 14 (by decide)]; exact hk8
    obtain ⟨i, hi⟩ : ∃ i, n - j = i := ⟨_, rfl⟩
    rw [hi] at hxa hxb hxd hxc hxm
    have hi' : n - (j - 1) = i + 1 := by omega
    rw [hi']
    have hin : i < n := by omega
    have hra : x.mem (A + i) = m.mem (A + i) := by
      rw [hxm]; apply writeMem_apply_out; exact (hal.read_out hin)
    have hrb : x.mem (B + i) = m.mem (B + i) := by
      rw [hxm]; apply writeMem_apply_out; exact (hbl.read_out hin)
    have hcy : subPref m.mem A B c0 i / 256 ^ i ≤ 1 := div_pow_le_one (subPref_lt _ _ _ _ _)
    obtain ⟨q, hq⟩ : ∃ q, subPref m.mem A B c0 i / 256 ^ i = q := ⟨_, rfl⟩
    rw [hq] at hxc hcy
    have hba' := byte_lt (m.mem (A + i))
    have hbb' := byte_lt (m.mem (B + i))
    obtain ⟨hl1, hl2⟩ := leN_step _ _ i ((m.mem (A + i)).toNat + 255 - (m.mem (B + i)).toNat)
      (subPref_succ m.mem A B c0 i hc0)
    rw [hq] at hl1 hl2
    refine ⟨?x, ?c, ev_block_of (by simp [allOk, okInstr]) ?run, ?inv, ?k, ?cost⟩
    case run =>
      npai_sym [hxa, hxb, hxd, hxc, hxk, hx1, hx8, hra, hrb]
      rfl
    case inv =>
      refine ⟨by omega, by simp [setReg_apply]; omega, by simp [setReg_apply]; omega,
        by simp [setReg_apply]; omega, ?_, ?_, ?_⟩
      · simp only [setReg_apply]; simp only [Nat.reduceEqDiff, ↓reduceIte]
        rw [hl2]; omega
      · simp only; rw [hxm, hl1, ← writeMem_snoc _ _ _ _ (by simp [Bytes.leN_length])]
        congr 3; omega
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [setReg_apply, ite_neg hr.1, ite_neg hr.2.1, ite_neg hr.2.2.1, ite_neg hr.2.2.2.1,
          ite_neg hr.2.2.2.2.1, ite_neg hr.2.2.2.2.2.1, ite_neg hr.2.2.2.2.2.2]
        exact hfr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
          hr.2.2.2.2.2.2])
    case k => simp
    case cost => simp
  obtain ⟨m2, c2, h2, ⟨-, ha2, hb2, hd2, hc2, hm2, hf2⟩, hk2, hcost⟩ := loopDown_complete _ 12 hbody n m
    ⟨Nat.le_refl _, by simp [hA], by simp [hB], by simp [hD], by
      simp [hC, subPref, readMem_zero, Bytes.leToNat]; omega,
      by simp [writeMem_zero], Frame.refl _ _⟩ hn
  simp only [Nat.sub_zero] at ha2 hb2 hd2 hc2 hm2
  refine ⟨m2, c2, h2, ?_, ?_, ha2, hb2, hd2, hk2, hf2, by omega⟩
  · rw [hm2, leN_mod]; rfl
  · rw [hc2, subPref_div _ _ _ _ _ hc0]
    by_cases h : Bytes.leToNat (readMem m.mem A n) < Bytes.leToNat (readMem m.mem B n) + c0 <;> simp [h]

theorem mulPref_succ (M0 : Nat → UInt8) (A K c0 i : Nat) :
    Bytes.leToNat (readMem M0 A (i + 1)) * K + c0 =
      (Bytes.leToNat (readMem M0 A i) * K + c0) + 256 ^ i * ((M0 (A + i)).toNat * K) := by
  rw [leToNat_readMem_snoc, Nat.add_mul, Nat.mul_assoc]; omega

/-- `mulLE`: `d[0, n) := low n bytes of a * K + c0`, carry out `(a * K + c0) / 256^n`.
Fixed registers `r1 = pa`, `r3 = pd`, `r4 = n`, `r2 = K`, `r5 = carry`, temp `r6`. -/
theorem mulLE_spec {m : M} (hk : Kinv m) {n : Nat} (hn : m.regs 4 = n)
    (hK : m.regs 2 < 281474976710656) (hc0 : m.regs 5 < 281474976710656)
    (hba : m.regs 1 + n ≤ p.memSize) (hbd : m.regs 3 + n ≤ p.memSize) (hw : p.memSize < 2 ^ 32)
    (hal : Alias (m.regs 3) (m.regs 1) n) :
    ∃ m' c, Ev p inp mulLE m (.ok m') c ∧
      m'.mem = writeMem m.mem (m.regs 3) n (Bytes.leN n
        (Bytes.leToNat (readMem m.mem (m.regs 1) n) * m.regs 2 + m.regs 5)) ∧
      m'.regs 5 = (Bytes.leToNat (readMem m.mem (m.regs 1) n) * m.regs 2 + m.regs 5) / 256 ^ n ∧
      m'.regs 1 = m.regs 1 + n ∧ m'.regs 3 = m.regs 3 + n ∧ m'.regs 4 = 0 ∧ m'.regs 2 = m.regs 2 ∧
      Frame [1, 3, 4, 5, 6] m m' ∧ c ≤ 10 * n + 1 := by
  obtain ⟨hk1, hk8⟩ := hk
  obtain ⟨A, hA⟩ : ∃ A, m.regs 1 = A := ⟨_, rfl⟩
  obtain ⟨K, hKK⟩ : ∃ K, m.regs 2 = K := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, m.regs 3 = D := ⟨_, rfl⟩
  obtain ⟨c0, hC⟩ : ∃ c0, m.regs 5 = c0 := ⟨_, rfl⟩
  simp only [hA, hKK, hD, hC] at hba hbd hal hK hc0 ⊢
  have hbody : ∀ j x, 0 < j → (j ≤ n ∧ x.regs 1 = A + (n - j) ∧
      x.regs 3 = D + (n - j) ∧
      x.regs 5 = (Bytes.leToNat (readMem m.mem A (n - j)) * K + c0) / 256 ^ (n - j) ∧
      x.regs 5 < 281474976710656 ∧
      x.mem = writeMem m.mem D (n - j) (Bytes.leN (n - j) (Bytes.leToNat (readMem m.mem A (n - j)) * K + c0)) ∧
      Frame [1, 3, 4, 5, 6] m x) → x.regs 4 = j → ∃ x' c, Ev p inp (block [.ld8 6 1, .bin .mul 6 6 2,
      .bin .add 6 6 5, .st8 3 6, .bin .shr 5 6 K8, .addi 1 1 1, .addi 3 3 1, .bin .sub 4 4 K1]) x
      (.ok x') c ∧ ((j - 1) ≤ n ∧ x'.regs 1 = A + (n - (j - 1)) ∧
      x'.regs 3 = D + (n - (j - 1)) ∧
      x'.regs 5 = (Bytes.leToNat (readMem m.mem A (n - (j - 1))) * K + c0) / 256 ^ (n - (j - 1)) ∧
      x'.regs 5 < 281474976710656 ∧
      x'.mem = writeMem m.mem D (n - (j - 1)) (Bytes.leN (n - (j - 1))
        (Bytes.leToNat (readMem m.mem A (n - (j - 1))) * K + c0)) ∧
      Frame [1, 3, 4, 5, 6] m x') ∧ x'.regs 4 = j - 1 ∧ c ≤ 8 := by
    intro j x hj ⟨hjn, hxa, hxd, hxc, hxcl, hxm, hfr⟩ hxk
    have hx1 : x.regs 15 = 1 := by rw [hfr 15 (by decide)]; exact hk1
    have hx8 : x.regs 14 = 8 := by rw [hfr 14 (by decide)]; exact hk8
    have hxK : x.regs 2 = K := by rw [hfr 2 (by decide)]; exact hKK
    obtain ⟨i, hi⟩ : ∃ i, n - j = i := ⟨_, rfl⟩
    rw [hi] at hxa hxd hxc hxm
    have hi' : n - (j - 1) = i + 1 := by omega
    rw [hi']
    have hin : i < n := by omega
    have hra : x.mem (A + i) = m.mem (A + i) := by
      rw [hxm]; apply writeMem_apply_out; exact (hal.read_out hin)
    obtain ⟨q, hq⟩ : ∃ q, (Bytes.leToNat (readMem m.mem A i) * K + c0) / 256 ^ i = q := ⟨_, rfl⟩
    rw [hq] at hxc
    rw [hxc] at hxcl
    have hba' := byte_lt (m.mem (A + i))
    have hmk : (m.mem (A + i)).toNat * K ≤ 255 * K := Nat.mul_le_mul_right _ (by omega)
    obtain ⟨hl1, hl2⟩ := leN_step _ _ i ((m.mem (A + i)).toNat * K) (mulPref_succ m.mem A K c0 i)
    rw [hq] at hl1 hl2
    refine ⟨?x, ?c, ev_block_of (by simp [allOk, okInstr]) ?run, ?inv, ?k, ?cost⟩
    case run =>
      npai_sym [hxa, hxd, hxc, hxk, hx1, hx8, hxK, hra, evMbyte]
      rfl
    case inv =>
      refine ⟨by omega, by simp [setReg_apply]; omega, by simp [setReg_apply]; omega, ?_, ?_, ?_, ?_⟩
      · simp only [setReg_apply]; simp only [Nat.reduceEqDiff, ↓reduceIte]
        rw [hl2]; congr 1; omega
      · simp only [setReg_apply]; simp only [Nat.reduceEqDiff, ↓reduceIte]
        omega
      · simp only; rw [hxm, hl1, ← writeMem_snoc _ _ _ _ (by simp [Bytes.leN_length])]
        congr 3; omega
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [setReg_apply, ite_neg hr.1, ite_neg hr.2.1, ite_neg hr.2.2.1, ite_neg hr.2.2.2.1,
          ite_neg hr.2.2.2.2]
        exact hfr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])
    case k => simp
    case cost => simp
  obtain ⟨m2, c2, h2, ⟨-, ha2, hd2, hc2, -, hm2, hf2⟩, hk2, hcost⟩ := loopDown_complete _ 8 hbody n m
    ⟨Nat.le_refl _, by simp [hA], by simp [hD], by simp [hC, readMem_zero, Bytes.leToNat], by omega,
      by simp [writeMem_zero], Frame.refl _ _⟩ hn
  simp only [Nat.sub_zero] at ha2 hd2 hc2 hm2
  refine ⟨m2, c2, h2, hm2, hc2, ha2, hd2, hk2, by rw [hf2 2 (by decide)]; exact hKK, hf2, by omega⟩

/-- Number of set bits among the low `n` bits (same definition as in the NEAR codec). -/
def popcN : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => x % 2 + popcN n (x / 2)

theorem popcN_le : ∀ (k x : Nat), popcN k x ≤ k
  | 0, _ => by simp [popcN]
  | k + 1, x => by
    have := popcN_le k (x / 2); have : x % 2 < 2 := Nat.mod_lt _ (by omega)
    simp only [popcN]; omega

theorem popcN_succ : ∀ (k x : Nat), popcN (k + 1) x = popcN k x + x / 2 ^ k % 2
  | 0, x => by simp [popcN]
  | k + 1, x => by
    show x % 2 + popcN (k + 1) (x / 2) = (x % 2 + popcN k (x / 2)) + x / 2 ^ (k + 1) % 2
    rw [popcN_succ k (x / 2), Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2 (2 ^ k)]
    omega

theorem evAnd1 (x : Nat) : BinOp.and.eval x 1 = x % 2 := by
  simp only [BinOp.eval, Nat.and_one_is_mod]
  exact Nat.mod_eq_of_lt (by have := Nat.mod_lt x (show 2 > 0 by omega); unfold wordMod; omega)

theorem evShr1 (x : Nat) (h : x < 18446744073709551616) : BinOp.shr.eval x 1 = x / 2 := by
  rw [eval_shr x 1 (by omega) h]

theorem popc16_spec {d s a b c : Nat} (hd : [d, s, a, b, c].Nodup) (hK : ∀ r ∈ [d, a, b, c], r ≠ 14 ∧ r ≠ 15)
    {m : M} (hk : Kinv m) (hs : m.regs s < 18446744073709551616) :
    ∃ m' c', Ev p inp (popc16 d s a b c) m (.ok m') c' ∧
      m'.regs d = popcN 16 (m.regs s) ∧ m'.mem = m.mem ∧ Frame [d, a, b, c] m m' ∧ c' ≤ 100 := by
  obtain ⟨hk1, -⟩ := hk
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hds, hda, hdb, hdc⟩, ⟨hsa, hsb, hsc⟩, ⟨hab, hac⟩, hbc, -⟩ := hd
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hK
  obtain ⟨⟨hd14, hd15⟩, ⟨ha14, ha15⟩, ⟨hb14, hb15⟩, ⟨hc14, hc15⟩⟩ := hK
  obtain ⟨S, hS⟩ : ∃ S, m.regs s = S := ⟨_, rfl⟩
  simp only [hS] at hs ⊢
  have e1 : Ev p inp (.op (.const d 0)) m (.ok ⟨setReg m.regs d 0, m.mem⟩) 1 :=
    Ev.op rfl (by simp [ins])
  have e2 : Ev p inp (.op (.mov a s)) ⟨setReg m.regs d 0, m.mem⟩
      (.ok ⟨setReg (setReg m.regs d 0) a S, m.mem⟩) 1 :=
    Ev.op rfl (by simp only [ins, setReg_apply, ite_neg (Ne.symm hds), hS])
  have e3 : Ev p inp (.op (.const b 16)) ⟨setReg (setReg m.regs d 0) a S, m.mem⟩
      (.ok ⟨setReg (setReg (setReg m.regs d 0) a S) b 16, m.mem⟩) 1 :=
    Ev.op rfl (by simp [ins, wordMod])
  have hbody : ∀ j x, 0 < j → (j ≤ 16 ∧ x.regs d = popcN (16 - j) S ∧ x.regs a = S / 2 ^ (16 - j) ∧
      x.mem = m.mem ∧ Frame [d, a, b, c] m x) → x.regs b = j →
      ∃ x' c', Ev p inp (block [.bin .and c a K1, .bin .add d d c, .bin .shr a a K1, .bin .sub b b K1])
        x (.ok x') c' ∧ ((j - 1) ≤ 16 ∧ x'.regs d = popcN (16 - (j - 1)) S ∧
        x'.regs a = S / 2 ^ (16 - (j - 1)) ∧ x'.mem = m.mem ∧ Frame [d, a, b, c] m x') ∧
        x'.regs b = j - 1 ∧ c' ≤ 4 := by
    intro j x hj ⟨hj16, hxd, hxa, hxm, hfr⟩ hxb
    have hx1 : x.regs 15 = 1 := by
      rw [hfr 15 (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)]; exact hk1
    obtain ⟨k, hk⟩ : ∃ k, 16 - j = k := ⟨_, rfl⟩
    rw [hk] at hxd hxa
    have hk' : 16 - (j - 1) = k + 1 := by omega
    rw [hk']
    have hpk := popcN_le k S
    have hk16 : k ≤ 16 := by omega
    have hSk : S / 2 ^ k < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hs
    have hm2 := Nat.mod_lt (S / 2 ^ k) (show 2 > 0 by omega)
    refine ⟨?x, ?c, ev_block_of (by simp [allOk, okInstr]) ?run, ?inv, ?kk, ?cost⟩
    case run =>
      npai_sym [hxa, hxd, hxb, hx1, evAnd1, evShr1]
      rfl
    case inv =>
      refine ⟨by omega, ?_, ?_, hxm, ?_⟩
      · simp (disch := omega) only [setReg_apply, ite_neg, ↓reduceIte]
        rw [popcN_succ]
      · simp (disch := omega) only [setReg_apply, ite_neg, ↓reduceIte]
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp (disch := omega) only [setReg_apply, ite_neg]
        exact hfr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)
    case kk => simp (disch := omega) only [setReg_apply, ↓reduceIte]
    case cost => simp
  obtain ⟨m2, c2, h2, ⟨-, hd2, -, hm2, hf2⟩, -, hcost⟩ := loopDown_complete (k := b) _ 4 hbody 16
    ⟨setReg (setReg (setReg m.regs d 0) a S) b 16, m.mem⟩
    ⟨by omega, by simp (disch := omega) only [setReg_apply, ite_neg, ↓reduceIte]; simp [popcN],
      by simp (disch := omega) only [setReg_apply, ite_neg, ↓reduceIte]; simp, rfl, by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (disch := omega) only [setReg_apply, ite_neg]⟩ (by simp)
  refine ⟨m2, _, Ev.seqOk e1 (Ev.seqOk e2 (Ev.seqOk e3 h2)), hd2, hm2, hf2, by omega⟩

end NpaiIR
