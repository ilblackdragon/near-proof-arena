import NpaiIR.Lib.Mem

/-!
# NpaiIR.Lib.Num — little-endian byte-array arithmetic in memory

Multi-byte numbers (`u128` balances, gas prices, products) live in memory as
little-endian byte arrays; the routines here work byte by byte with a carry
register, so every intermediate value fits a 64-bit register and the
specifications are plain `Nat` equations on `Bytes.leToNat`.
-/

set_option maxRecDepth 8000

namespace NpaiIR

open ArenaCore Interp

variable {p : Program} {inp : Inputs}

/-! ## Little-endian lemmas -/

theorem leN_succ_snoc : ∀ (i x : Nat),
    Bytes.leN (i + 1) x = Bytes.leN i x ++ [UInt8.ofNat (x / 256 ^ i % 256)]
  | 0, x => by simp [Bytes.leN]
  | i + 1, x => by
    rw [Bytes.leN, leN_succ_snoc i (x / 256), Bytes.leN]
    simp [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm (256 ^ i) 256]

theorem leN_add_mul : ∀ (i x y : Nat), Bytes.leN i (x + 256 ^ i * y) = Bytes.leN i x
  | 0, _, _ => rfl
  | i + 1, x, y => by
    simp only [Bytes.leN, List.cons.injEq]
    constructor
    · congr 1; rw [Nat.pow_succ]
      have : x + 256 ^ i * 256 * y = x + 256 * (256 ^ i * y) := by
        rw [Nat.mul_comm (256 ^ i) 256, Nat.mul_assoc]
      rw [this, Nat.add_mul_mod_self_left]
    · have : (x + 256 ^ (i + 1) * y) / 256 = x / 256 + 256 ^ i * y := by
        rw [Nat.pow_succ, Nat.mul_comm (256 ^ i) 256, Nat.mul_assoc, Nat.add_mul_div_left _ _ (by omega)]
      rw [this, leN_add_mul i]

theorem leN_mod (i x : Nat) : Bytes.leN i (x % 256 ^ i) = Bytes.leN i x := by
  conv => rhs; rw [← Nat.mod_add_div x (256 ^ i)]
  rw [leN_add_mul]

theorem leToNat_readMem_snoc (M0 : Nat → UInt8) (a i : Nat) :
    Bytes.leToNat (readMem M0 a (i + 1)) = Bytes.leToNat (readMem M0 a i) + 256 ^ i * (M0 (a + i)).toNat := by
  rw [readMem_snoc, leToNat_append]
  simp [Bytes.leToNat]

theorem leToNat_readMem_lt (M0 : Nat → UInt8) (a i : Nat) :
    Bytes.leToNat (readMem M0 a i) < 256 ^ i := by
  have := leToNat_lt (readMem M0 a i); simpa using this

theorem leToNat_leN (w x : Nat) (h : x < 256 ^ w) : Bytes.leToNat (Bytes.leN w x) = x :=
  leToNat_leN_eq w x h
where
  leToNat_leN_eq : ∀ (w x : Nat), x < 256 ^ w → Bytes.leToNat (Bytes.leN w x) = x
    | 0, x, h => by simp at h; simp [Bytes.leN, Bytes.leToNat, h]
    | w + 1, x, h => by
      simp only [Bytes.leN, Bytes.leToNat]
      have h' : x / 256 < 256 ^ w := by
        rw [Nat.pow_succ] at h; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
      rw [leToNat_leN_eq w _ h']
      have : (UInt8.ofNat (x % 256)).toNat = x % 256 := by simp
      rw [this]; omega

/-! ## `addLE`: `d[0,n) := a + b + cy (mod 256^n)`, carry out in `cy`

Fixed registers: `r1 = pa`, `r2 = pb`, `r3 = pd` (pointers, advanced by `n`),
`r4 = k` (count), `r5 = cy` (carry in/out), `r6 r7` temporaries. -/

def addLE : Stmt :=
  .loop 4 (block [.ld8 6 1, .ld8 7 2, .bin .add 6 6 7, .bin .add 6 6 5, .st8 3 6,
    .bin .shr 5 6 K8, .addi 1 1 1, .addi 2 2 1, .addi 3 3 1, .bin .sub 4 4 K1])

theorem addLE_ok : addLE.ok := by simp [addLE, Stmt.ok, block, okInstr]
theorem addLE_noHalt : addLE.noHalt := by simp [addLE, Stmt.noHalt, block]

/-- No-clobber condition for an in-place or disjoint destination. -/
def Alias (D A n : Nat) : Prop := D = A ∨ D + n ≤ A ∨ A + n ≤ D

theorem Alias.read_out {D A n i : Nat} (h : Alias D A n) (hi : i < n) :
    A + i < D ∨ D + i ≤ A + i := by
  rcases h with rfl | h | h <;> omega

theorem div_pow_le_one {x i : Nat} (h : x < 2 * 256 ^ i) : x / 256 ^ i ≤ 1 := by
  have hp : 0 < 256 ^ i := Nat.pow_pos (by omega)
  have := Nat.div_lt_of_lt_mul (show x < 256 ^ i * 2 by rw [Nat.mul_comm]; exact h)
  omega

/-- Prefix sum of two little-endian arrays plus a carry. -/
def sumPref (M0 : Nat → UInt8) (A B c0 i : Nat) : Nat :=
  Bytes.leToNat (readMem M0 A i) + Bytes.leToNat (readMem M0 B i) + c0

theorem sumPref_lt (M0 : Nat → UInt8) (A B c0 i : Nat) (h : c0 ≤ 1) :
    sumPref M0 A B c0 i < 2 * 256 ^ i := by
  have := leToNat_readMem_lt M0 A i; have := leToNat_readMem_lt M0 B i
  simp only [sumPref]; omega

theorem sumPref_succ (M0 : Nat → UInt8) (A B c0 i : Nat) :
    sumPref M0 A B c0 (i + 1) = sumPref M0 A B c0 i + 256 ^ i * ((M0 (A + i)).toNat + (M0 (B + i)).toNat) := by
  simp only [sumPref, leToNat_readMem_snoc, Nat.mul_add]; omega

/-- One step of a byte-serial carry computation: writing byte `i` of `s (i+1)`
after the bytes of `s i`. -/
theorem leN_step (s s' i d : Nat) (h : s' = s + 256 ^ i * d) :
    Bytes.leN (i + 1) s' = Bytes.leN i s ++ [UInt8.ofNat ((s / 256 ^ i + d) % 256)] ∧
      s' / 256 ^ (i + 1) = (s / 256 ^ i + d) / 256 := by
  have hp : 0 < 256 ^ i := Nat.pow_pos (by omega)
  have e1 : s' / 256 ^ i = s / 256 ^ i + d := by
    rw [h, Nat.add_mul_div_left _ _ hp]
  refine ⟨?_, ?_⟩
  · rw [leN_succ_snoc, e1, h, leN_add_mul]
  · rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, e1]

theorem addLE_spec {m : M} (hk : Kinv m) {n : Nat} (hn : m.regs 4 = n) (hc0 : m.regs 5 ≤ 1)
    (hba : m.regs 1 + n ≤ p.memSize) (hbb : m.regs 2 + n ≤ p.memSize)
    (hbd : m.regs 3 + n ≤ p.memSize) (hw : p.memSize < 2 ^ 32)
    (hal : Alias (m.regs 3) (m.regs 1) n) (hbl : Alias (m.regs 3) (m.regs 2) n) :
    ∃ m' c, Ev p inp addLE m (.ok m') c ∧
      m'.mem = writeMem m.mem (m.regs 3) n (Bytes.leN n (sumPref m.mem (m.regs 1) (m.regs 2) (m.regs 5) n)) ∧
      m'.regs 5 = sumPref m.mem (m.regs 1) (m.regs 2) (m.regs 5) n / 256 ^ n ∧
      Frame [1, 2, 3, 4, 5, 6, 7] m m' ∧ c ≤ 12 * n + 1 := by
  obtain ⟨hk1, hk8⟩ := hk
  obtain ⟨A, hA⟩ : ∃ A, m.regs 1 = A := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, m.regs 2 = B := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, m.regs 3 = D := ⟨_, rfl⟩
  obtain ⟨c0, hC⟩ : ∃ c0, m.regs 5 = c0 := ⟨_, rfl⟩
  simp only [hA, hB, hD, hC] at hba hbb hbd hal hbl hc0 ⊢
  have hbody : ∀ j x, 0 < j → (j ≤ n ∧ x.regs 1 = A + (n - j) ∧ x.regs 2 = B + (n - j) ∧
      x.regs 3 = D + (n - j) ∧ x.regs 5 = sumPref m.mem A B c0 (n - j) / 256 ^ (n - j) ∧
      x.mem = writeMem m.mem D (n - j) (Bytes.leN (n - j) (sumPref m.mem A B c0 (n - j))) ∧
      Frame [1, 2, 3, 4, 5, 6, 7] m x) → x.regs 4 = j → ∃ x' c, Ev p inp (block [.ld8 6 1, .ld8 7 2,
      .bin .add 6 6 7, .bin .add 6 6 5, .st8 3 6, .bin .shr 5 6 K8, .addi 1 1 1, .addi 2 2 1,
      .addi 3 3 1, .bin .sub 4 4 K1]) x (.ok x') c ∧ ((j - 1) ≤ n ∧ x'.regs 1 = A + (n - (j - 1)) ∧
      x'.regs 2 = B + (n - (j - 1)) ∧
      x'.regs 3 = D + (n - (j - 1)) ∧ x'.regs 5 = sumPref m.mem A B c0 (n - (j - 1)) / 256 ^ (n - (j - 1)) ∧
      x'.mem = writeMem m.mem D (n - (j - 1)) (Bytes.leN (n - (j - 1)) (sumPref m.mem A B c0 (n - (j - 1)))) ∧
      Frame [1, 2, 3, 4, 5, 6, 7] m x') ∧ x'.regs 4 = j - 1 ∧ c ≤ 10 := by
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
    have hcy : sumPref m.mem A B c0 i / 256 ^ i ≤ 1 := div_pow_le_one (sumPref_lt _ _ _ _ _ hc0)
    have hba' := byte_lt (m.mem (A + i))
    have hbb' := byte_lt (m.mem (B + i))
    obtain ⟨hl1, hl2⟩ := leN_step _ _ i ((m.mem (A + i)).toNat + (m.mem (B + i)).toNat)
      (sumPref_succ m.mem A B c0 i)
    refine ⟨?x, ?c, ev_block_of (by simp [allOk, okInstr]) ?run, ?inv, ?k, ?cost⟩
    case run =>
      npai_sym [hxa, hxb, hxd, hxc, hxk, hx1, hx8, hra, hrb]
      rfl
    case inv =>
      refine ⟨by omega, by simp [setReg_apply]; omega, by simp [setReg_apply]; omega,
        by simp [setReg_apply]; omega, ?_, ?_, ?_⟩
      · simp only [setReg_apply]; simp only [Nat.reduceEqDiff, ↓reduceIte]
        rw [hl2]; congr 1; omega
      · simp only; rw [hxm, hl1, ← writeMem_snoc _ _ _ _ (by simp [Bytes.leN_length])]
        congr 3; omega
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [setReg_apply, if_neg hr.1, if_neg hr.2.1, if_neg hr.2.2.1, if_neg hr.2.2.2.1,
          if_neg hr.2.2.2.2.1, if_neg hr.2.2.2.2.2.1, if_neg hr.2.2.2.2.2.2]
        exact hfr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
          hr.2.2.2.2.2.2])
    case k => simp
    case cost => simp
  obtain ⟨m2, c2, h2, ⟨-, -, -, -, hc2, hm2, hf2⟩, -, hcost⟩ := loopDown_complete _ 10 hbody n m
    ⟨Nat.le_refl _, by simp [hA], by simp [hB], by simp [hD], by simp [hC, sumPref, readMem_zero, Bytes.leToNat],
      by simp [writeMem_zero], Frame.refl _ _⟩ hn
  refine ⟨m2, c2, h2, by rw [hm2]; simp, by rw [hc2]; simp, hf2, by omega⟩

end NpaiIR

namespace NpaiIR

open ArenaCore Interp

/-! ## `subLE`: `d[0,n) := a - b - bw (mod 256^n)`, borrow out in `bw`

Fixed registers: `r1 = pa`, `r2 = pb`, `r3 = pd`, `r4 = k`, `r5 = bw` (borrow
in/out, `0/1`), `r6 r7` temporaries. Byte step:
`t = a_i + 256 - b_i - bw; d_i = t mod 256; bw = 1 - t / 256`. -/
def subLE : Stmt :=
  .loop 4 (block [.ld8 6 1, .addi 6 6 256, .ld8 7 2, .bin .sub 6 6 7, .bin .sub 6 6 5, .st8 3 6,
    .bin .shr 7 6 K8, .bin .sub 5 K1 7, .addi 1 1 1, .addi 2 2 1, .addi 3 3 1, .bin .sub 4 4 K1])

/-! ## `mulLE`: `d[0,n) ‖ carry := a[0,n) * K`

Fixed registers: `r1 = pa`, `r3 = pd` (advanced), `r4 = k`, `r2 = K`
(multiplier, `< 2^48`), `r5 = cy` (carry out), `r6` temporary. The carry
(`< K`) is left in `r5`; callers store it with `stLE`. -/
def mulLE : Stmt :=
  .loop 4 (block [.ld8 6 1, .bin .mul 6 6 2, .bin .add 6 6 5, .st8 3 6, .bin .shr 5 6 K8,
    .addi 1 1 1, .addi 3 3 1, .bin .sub 4 4 K1])

/-! ## `popc16 d s a b c`: `d := popcount (s mod 2^16)` (clobbers `d a b c`) -/
def popc16 (d s a b c : Nat) : Stmt :=
  .seq (.op (.const d 0)) (.seq (.op (.mov a s)) (.seq (.op (.const b 16))
    (.loop b (block [.bin .and c a K1, .bin .add d d c, .bin .shr a a K1, .bin .sub b b K1]))))

end NpaiIR
