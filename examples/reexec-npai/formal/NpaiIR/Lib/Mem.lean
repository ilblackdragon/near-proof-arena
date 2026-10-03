import NpaiIR.Lib.Loop

/-!
# NpaiIR.Lib.Mem — little-endian loads/stores and byte copies
-/

set_option maxRecDepth 8000

namespace NpaiIR

open ArenaCore Interp

variable {p : Program} {inp : Inputs}

theorem leToNat_lt : ∀ l : Bytes, Bytes.leToNat l < 256 ^ l.length
  | [] => by simp [Bytes.leToNat]
  | x :: xs => by
    have := leToNat_lt xs
    have hx := x.toNat_lt
    simp only [Bytes.leToNat, List.length_cons, Nat.pow_succ]
    omega

theorem leToNat_append (a b : Bytes) :
    Bytes.leToNat (a ++ b) = Bytes.leToNat a + 256 ^ a.length * Bytes.leToNat b := by
  induction a with
  | nil => simp [Bytes.leToNat]
  | cons x xs ih =>
    simp only [List.cons_append, Bytes.leToNat, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 256 (256 ^ xs.length)]
    omega

/-! ## `ldLE`: little-endian load of `n ≤ 8` bytes -/

/-- `d := leToNat mem[a, a+n)`; clobbers `d k t`. -/
def ldLE (d a k t n : Nat) : Stmt :=
  .seq (.op (.const d 0)) (.seq (.op (.const k n))
    (.loop k (block [.bin .sub k k K1, .bin .add t a k, .ld8 t t, .bin .shl d d K8, .bin .add d d t])))

theorem ldLE_ok (d a k t n : Nat) : (ldLE d a k t n).ok := by
  simp [ldLE, Stmt.ok, block, okInstr]

theorem ldLE_noHalt (d a k t n : Nat) : (ldLE d a k t n).noHalt := by
  simp [ldLE, Stmt.noHalt, block]

theorem ldLE_spec {d a k t n : Nat} (hda : d ≠ a) (hdk : d ≠ k) (hdt : d ≠ t) (hak : a ≠ k)
    (hat : a ≠ t) (hkt : k ≠ t) (hK : K1 ≠ d ∧ K1 ≠ k ∧ K1 ≠ t ∧ K8 ≠ d ∧ K8 ≠ k ∧ K8 ≠ t)
    (hn : n ≤ 8) {m : M} (hk : Kinv m) (hb : m.regs a + n ≤ p.memSize) (hw : p.memSize < 2 ^ 32) :
    ∃ m' c, Ev p inp (ldLE d a k t n) m (.ok m') c ∧
      m'.regs d = Bytes.leToNat (readMem m.mem (m.regs a) n) ∧ m'.mem = m.mem ∧
      Frame [d, k, t] m m' ∧ c ≤ 7 * n + 3 := by
  obtain ⟨hk1, hk8⟩ := hk
  obtain ⟨h1d, h1k, h1t, h8d, h8k, h8t⟩ := hK
  let m1 : M := { m with regs := setReg (setReg m.regs d 0) k n }
  let I : M → Prop := fun x => x.mem = m.mem ∧ Frame [d, k, t] m x ∧ x.regs k ≤ n ∧
    x.regs d = Bytes.leToNat (readMem m.mem (m.regs a + x.regs k) (n - x.regs k))
  have hI1 : I m1 := by
    refine ⟨rfl, ?_, by simp [m1, setReg], ?_⟩
    · intro j hj; simp only [List.mem_cons, not_or] at hj
      simp [m1, setReg, hj.1, hj.2.1]
    · simp [m1, setReg, hdk, Nat.sub_self, readMem_zero, Bytes.leToNat]
  have hbody : ∀ x, I x → x.regs k ≠ 0 → ∃ x' c, Ev p inp (block [.bin .sub k k K1, .bin .add t a k,
      .ld8 t t, .bin .shl d d K8, .bin .add d d t]) x (.ok x') c ∧ I x' ∧ c + 2 + 7 * x'.regs k ≤
      7 * x.regs k := by
    intro x ⟨hmem, hfr, hkn, hd⟩ hk0
    have ha : x.regs a = m.regs a := hfr a (by simp [hda.symm, hak, hat])
    have hx1 : x.regs K1 = 1 := by rw [hfr K1 (by simp [h1d, h1k, h1t])]; exact hk1
    have hx8 : x.regs K8 = 8 := by rw [hfr K8 (by simp [h8d, h8k, h8t])]; exact hk8
    have hd_lt : x.regs d < 256 ^ (n - x.regs k) := by
      rw [hd]; have := leToNat_lt (readMem m.mem (m.regs a + x.regs k) (n - x.regs k))
      simpa using this
    obtain ⟨j, hj⟩ : ∃ j, x.regs k = j := ⟨_, rfl⟩
    rw [hj] at hkn hd hd_lt hk0
    have hpow : 256 ^ (n - j) ≤ 256 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
    have hd56 : x.regs d < 72057594037927936 :=
      Nat.lt_of_lt_of_le hd_lt (Nat.le_trans hpow (by decide))
    refine ⟨?x, ?c, ev_block_of (by simp [allOk, okInstr]) ?run, ?inv, ?pot⟩
    case run =>
      simp (disch := omega) only [runSL, ins, Option.map_some, setReg_apply, hx1, hx8, hj, ha, ite_pos,
        ite_neg, evAbyte, evA, evS, evShl8, cost, ↓reduceIte, Nat.reduceAdd, hmem]
      rfl
    case inv =>
      refine ⟨rfl, ?_, ?_, ?_⟩
      · intro r hr; simp only [List.mem_cons, not_or] at hr
        simp only [setReg_apply, if_neg hr.1, if_neg hr.2.1, if_neg hr.2.2.1]
        exact hfr r (by simp [hr.1, hr.2.1, hr.2.2.1])
      · simp [setReg_apply, hdk.symm, hkt]; omega
      · simp only [setReg_apply, ↓reduceIte, if_neg hdk.symm, if_neg hkt]
        rw [show n - (j - 1) = (n - j) + 1 by omega, readMem_succ,
          show m.regs a + (j - 1) + 1 = m.regs a + j by omega]
        simp only [Bytes.leToNat, ← hd]; omega
    case pot =>
      simp [setReg_apply, hdk.symm, hkt]; omega
  obtain ⟨m2, c2, h2, ⟨hm2, hf2, -, hd2⟩, hz, hc2⟩ := loop_complete I (fun x => 7 * x.regs k) hbody m1 hI1
  refine ⟨m2, 1 + (1 + c2), ?_, ?_, hm2, hf2, ?_⟩
  · have e1 : Ev p inp (.op (.const d 0)) m (.ok { m with regs := setReg m.regs d 0 }) 1 :=
      Ev.op rfl (by simp [ins, wordMod])
    have e2 : Ev p inp (.op (.const k n)) { m with regs := setReg m.regs d 0 } (.ok m1) 1 :=
      Ev.op rfl (by simp only [ins, m1]; rw [evConst n (by omega)])
    exact Ev.seqOk e1 (Ev.seqOk e2 h2)
  · rw [hd2, hz]; simp
  · simp [m1, setReg] at hc2; omega

end NpaiIR

namespace NpaiIR

open ArenaCore Interp

variable {p : Program} {inp : Inputs}

theorem writeMem_snoc (M0 : Nat → UInt8) (a n : Nat) (L : Bytes) (hL : L.length = n) (b : UInt8) :
    writeMem (writeMem M0 a n L) (a + n) 1 [b] = writeMem M0 a (n + 1) (L ++ [b]) := by
  funext j
  simp only [writeMem]
  by_cases h1 : a + n ≤ j ∧ j < a + n + 1
  · have hj : j = a + n := by omega
    subst hj
    simp [hL, List.getD_eq_getElem?_getD]
  · rw [if_neg h1]
    by_cases h2 : a ≤ j ∧ j < a + n
    · rw [if_pos h2, if_pos ⟨h2.1, by omega⟩]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show j - a < L.length by omega)]
    · rw [if_neg h2, if_neg (by omega)]

theorem writeMem_zero (M0 : Nat → UInt8) (a : Nat) (L : Bytes) : writeMem M0 a 0 L = M0 := by
  funext j; simp [writeMem]; omega

theorem readMem_snoc (m : Nat → UInt8) (a n : Nat) : readMem m a (n + 1) = readMem m a n ++ [m (a + n)] := by
  rw [readMem_add, readMem_one]

theorem leN_take_succ : ∀ (n i V : Nat), i < n →
    (Bytes.leN n V).take (i + 1) = (Bytes.leN n V).take i ++ [UInt8.ofNat (V / 256 ^ i % 256)]
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, V, _ => by simp [Bytes.leN]
  | n + 1, i + 1, V, h => by
    simp only [Bytes.leN, List.take_succ_cons, List.cons_append]
    rw [leN_take_succ n i (V / 256) (by omega), Nat.pow_succ, Nat.div_div_eq_div_mul,
      Nat.mul_comm (256 ^ i) 256]

theorem leN_take_self (n V : Nat) : (Bytes.leN n V).take n = Bytes.leN n V := by
  rw [List.take_of_length_le (by simp [Bytes.leN_length])]

/-! ## `stLE`: little-endian store of `n` bytes -/

/-- `mem[a, a+n) := leN n (regs v)`; clobbers `k t w`. -/
def stLE (a v n k t w : Nat) : Stmt :=
  .seq (.op (.mov t v)) (.seq (.op (.const k n)) (.seq (.op (.mov w a))
    (.loop k (block [.st8 w t, .bin .shr t t K8, .addi w w 1, .bin .sub k k K1]))))

theorem stLE_ok (a v n k t w : Nat) : (stLE a v n k t w).ok := by
  simp [stLE, Stmt.ok, block, okInstr]

theorem stLE_noHalt (a v n k t w : Nat) : (stLE a v n k t w).noHalt := by
  simp [stLE, Stmt.noHalt, block]

theorem stLE_spec {a v n k t w : Nat} (hak : a ≠ k) (hat : a ≠ t) (haw : a ≠ w) (hvk : v ≠ k)
    (hkt : k ≠ t) (hkw : k ≠ w) (htw : t ≠ w)
    (hK : K1 ≠ k ∧ K1 ≠ t ∧ K1 ≠ w ∧ K8 ≠ k ∧ K8 ≠ t ∧ K8 ≠ w)
    {m : M} (hk : Kinv m) (hb : m.regs a + n ≤ p.memSize) (hw : p.memSize < 2 ^ 32)
    (hv : m.regs v < 18446744073709551616) :
    ∃ m' c, Ev p inp (stLE a v n k t w) m (.ok m') c ∧
      m'.mem = writeMem m.mem (m.regs a) n (Bytes.leN n (m.regs v)) ∧
      Frame [k, t, w] m m' ∧ c ≤ 6 * n + 4 := by
  obtain ⟨hk1, hk8⟩ := hk
  obtain ⟨h1k, h1t, h1w, h8k, h8t, h8w⟩ := hK
  have hn : n < 4294967296 := by omega
  let A := m.regs a
  let V := m.regs v
  let m1 : M := { m with regs := setReg (setReg (setReg m.regs t V) k n) w A }
  let J : Nat → M → Prop := fun j x => j ≤ n ∧ x.regs t = V / 256 ^ (n - j) ∧ x.regs w = A + (n - j) ∧
    x.mem = writeMem m.mem A (n - j) ((Bytes.leN n V).take (n - j)) ∧ Frame [k, t, w] m x
  have hJ1 : J n m1 := by
    refine ⟨Nat.le_refl _, by simp [m1, setReg_apply, htw, hkt.symm], by simp [m1], ?_, ?_⟩
    · simp [m1, writeMem_zero]
    · intro j hj; simp only [List.mem_cons, not_or] at hj
      simp [m1, setReg_apply, hj.1, hj.2.1, hj.2.2.1]
  have hbody : ∀ j x, 0 < j → J j x → x.regs k = j → ∃ x' c, Ev p inp (block [.st8 w t,
      .bin .shr t t K8, .addi w w 1, .bin .sub k k K1]) x (.ok x') c ∧ J (j - 1) x' ∧
      x'.regs k = j - 1 ∧ c ≤ 4 := by
    intro j x hj ⟨hjn, hxt, hxw, hxm, hfr⟩ hxk
    have hx1 : x.regs K1 = 1 := by rw [hfr K1 (by simp [h1k, h1t, h1w])]; exact hk1
    have hx8 : x.regs K8 = 8 := by rw [hfr K8 (by simp [h8k, h8t, h8w])]; exact hk8
    have hVt : V / 256 ^ (n - j) < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hv
    refine ⟨?x, ?c, ev_block_of (by simp [allOk, okInstr]) ?run, ?inv, ?k, ?cost⟩
    case run =>
      npai_sym [hxt, hxw, hxk, hx1, hx8]
      rfl
    case inv =>
      refine ⟨by omega, ?_, ?_, ?_, ?_⟩
      · simp [setReg_apply, hkt.symm, htw, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
        congr 2; omega
      · simp [setReg_apply, hkw.symm]; omega
      · simp only
        rw [hxm, show n - (j - 1) = (n - j) + 1 by omega, leN_take_succ _ _ _ (by omega),
          ← writeMem_snoc _ _ _ _ (by simp only [List.length_take, Bytes.leN_length]; omega)]
      · intro r hr; simp only [List.mem_cons, not_or] at hr
        simp only [setReg_apply, if_neg hr.1, if_neg hr.2.1, if_neg hr.2.2.1]
        exact hfr r (by simp [hr.1, hr.2.1, hr.2.2.1])
    case k => simp [setReg_apply, hkw.symm, hkt.symm]
    case cost => simp
  obtain ⟨m2, c2, h2, ⟨-, -, -, hm2, hf2⟩, -, hc2⟩ := loopDown_complete J 4 hbody n m1 hJ1
    (by simp [m1, setReg_apply, hkw])
  refine ⟨m2, 1 + (1 + (1 + c2)), ?_, ?_, hf2, by omega⟩
  · have e1 : Ev p inp (.op (.mov t v)) m (.ok { m with regs := setReg m.regs t V }) 1 := Ev.op rfl rfl
    have e2 : Ev p inp (.op (.const k n)) { m with regs := setReg m.regs t V }
        (.ok { m with regs := setReg (setReg m.regs t V) k n }) 1 :=
      Ev.op rfl (by simp only [ins]; rw [evConst n (by omega)])
    have e3 : Ev p inp (.op (.mov w a)) { m with regs := setReg (setReg m.regs t V) k n } (.ok m1) 1 :=
      Ev.op rfl (by simp [ins, m1, setReg_apply, hak, hat]; rfl)
    exact Ev.seqOk e1 (Ev.seqOk e2 (Ev.seqOk e3 h2))
  · rw [hm2]; simp [leN_take_self]; rfl

end NpaiIR

namespace NpaiIR

open ArenaCore Interp

variable {p : Program} {inp : Inputs}

/-! ## `memcpy`: forward byte copy of `regs k` bytes from `regs s` to `regs d` -/

def memcpy (d s k t : Nat) : Stmt :=
  .loop k (block [.ld8 t s, .st8 d t, .addi s s 1, .addi d d 1, .bin .sub k k K1])

theorem memcpy_ok (d s k t : Nat) : (memcpy d s k t).ok := by
  simp [memcpy, Stmt.ok, block, okInstr]

theorem memcpy_noHalt (d s k t : Nat) : (memcpy d s k t).noHalt := by
  simp [memcpy, Stmt.noHalt, block]

theorem writeMem_apply_out' (M0 : Nat → UInt8) (d len : Nat) (src : Bytes) (j : Nat)
    (h : j < d ∨ d + len ≤ j) : writeMem M0 d len src j = M0 j := writeMem_apply_out M0 d len src j h

theorem memcpy_spec {d s k t : Nat} (hds : d ≠ s) (hdk : d ≠ k) (hdt : d ≠ t) (hsk : s ≠ k)
    (hst : s ≠ t) (hkt : k ≠ t) (hK : K1 ≠ d ∧ K1 ≠ s ∧ K1 ≠ k ∧ K1 ≠ t)
    {m : M} (hk1 : m.regs K1 = 1) {n : Nat} (hn : m.regs k = n)
    (hbd : m.regs d + n ≤ p.memSize) (hbs : m.regs s + n ≤ p.memSize) (hw : p.memSize < 2 ^ 32)
    (hov : m.regs d ≤ m.regs s ∨ m.regs s + n ≤ m.regs d) :
    ∃ m' c, Ev p inp (memcpy d s k t) m (.ok m') c ∧
      m'.mem = writeMem m.mem (m.regs d) n (readMem m.mem (m.regs s) n) ∧
      m'.regs d = m.regs d + n ∧ m'.regs s = m.regs s + n ∧ m'.regs k = 0 ∧
      Frame [d, s, k, t] m m' ∧ c ≤ 7 * n + 1 := by
  obtain ⟨h1d, h1s, h1k, h1t⟩ := hK
  let D := m.regs d
  let S := m.regs s
  let J : Nat → M → Prop := fun j x => j ≤ n ∧ x.regs d = D + (n - j) ∧ x.regs s = S + (n - j) ∧
    x.mem = writeMem m.mem D (n - j) (readMem m.mem S (n - j)) ∧ Frame [d, s, k, t] m x
  have hJ0 : J n m := ⟨Nat.le_refl _, by simp [D], by simp [S], by simp [writeMem_zero, readMem_zero],
    Frame.refl _ _⟩
  have hbody : ∀ j x, 0 < j → J j x → x.regs k = j → ∃ x' c, Ev p inp (block [.ld8 t s, .st8 d t,
      .addi s s 1, .addi d d 1, .bin .sub k k K1]) x (.ok x') c ∧ J (j - 1) x' ∧
      x'.regs k = j - 1 ∧ c ≤ 5 := by
    intro j x hj ⟨hjn, hxd, hxs, hxm, hfr⟩ hxk
    have hx1 : x.regs K1 = 1 := by rw [hfr K1 (by simp [h1d, h1s, h1k, h1t])]; exact hk1
    have hsrc : x.mem (S + (n - j)) = m.mem (S + (n - j)) := by
      rw [hxm]; apply writeMem_apply_out; omega
    refine ⟨?x, ?c, ev_block_of (by simp [allOk, okInstr]) ?run, ?inv, ?k, ?cost⟩
    case run =>
      npai_sym [hxd, hxs, hxk, hx1, hsrc]
      rfl
    case inv =>
      refine ⟨by omega, ?_, ?_, ?_, ?_⟩
      · simp [setReg_apply, hds, hdk, hdt]; omega
      · simp [setReg_apply, hsk, hst, hds.symm]; omega
      · simp only
        rw [hxm, show n - (j - 1) = (n - j) + 1 by omega, readMem_snoc,
          ← writeMem_snoc _ _ _ _ (by simp)]
        simp [hsrc, Nat.mod_mod]
      · intro r hr; simp only [List.mem_cons, not_or] at hr
        simp only [setReg_apply, if_neg hr.1, if_neg hr.2.1, if_neg hr.2.2.1, if_neg hr.2.2.2.1]
        exact hfr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1])
    case k => simp [setReg_apply]
    case cost => simp
  obtain ⟨m2, c2, h2, ⟨-, hd2, hs2, hm2, hf2⟩, hk2, hc2⟩ := loopDown_complete J 5 hbody n m hJ0 hn
  refine ⟨m2, c2, h2, by rw [hm2]; simp; rfl, by rw [hd2]; simp; rfl, by rw [hs2]; simp; rfl, hk2, hf2, by omega⟩

theorem memcpy_det {d s k t : Nat} {m m1 m2 : M} {c1 c2 : Nat}
    (h1 : Ev p inp (memcpy d s k t) m (.ok m1) c1) (h2 : Ev p inp (memcpy d s k t) m (.ok m2) c2) :
    m1 = m2 := by
  obtain ⟨e, -⟩ := Ev.det h1 h2; cases e; rfl

end NpaiIR
