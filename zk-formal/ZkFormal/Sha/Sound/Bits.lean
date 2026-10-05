import ZkFormal.Sha.View

/-!
# ZkFormal.Sha.Sound.Bits — bit-level facts about `ofBits` and the SHA-256 word functions

`bt x b` is bit `b` of `x` as `0/1`.  We characterize the bits of
`ArenaCore.SHA256.{rotr, bsig0, bsig1, ssig0, ssig1, ch, maj}` (for words
`< 2^32`) in exactly the shape the AIR expressions compute them, and relate
`View.ofBits` to `bt`.
-/

namespace ZkFormal.Sha.Sound

open ArenaCore.SHA256 ZkFormal.Sha.View

/-- Bit `b` of `x`. -/
def bt (x b : Nat) : Nat := x / 2 ^ b % 2

theorem bt_le (x b : Nat) : bt x b ≤ 1 := by
  unfold bt; have := Nat.mod_lt (x / 2 ^ b) (show 2 > 0 by decide); omega

theorem bt_eq (x b : Nat) : bt x b = if x.testBit b then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]; unfold bt
  have := Nat.mod_lt (x / 2 ^ b) (show 2 > 0 by decide)
  by_cases h : x / 2 ^ b % 2 = 1
  · simp [h]
  · simp [h]; omega

theorem bt_xor (x y b : Nat) : bt (x ^^^ y) b = (bt x b + bt y b) % 2 := by
  rw [bt_eq, bt_eq, bt_eq, Nat.testBit_xor]
  cases x.testBit b <;> cases y.testBit b <;> rfl

theorem bt_and (x y b : Nat) : bt (x &&& y) b = bt x b * bt y b := by
  rw [bt_eq, bt_eq, bt_eq, Nat.testBit_and]
  cases x.testBit b <;> cases y.testBit b <;> rfl

theorem bt_shiftRight (x n b : Nat) : bt (x >>> n) b = bt x (n + b) := by
  rw [bt_eq, bt_eq, Nat.testBit_shiftRight]

theorem bt_of_lt {x n b : Nat} (hx : x < 2 ^ n) (hb : n ≤ b) : bt x b = 0 := by
  unfold bt
  have : x < 2 ^ b := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hb)
  rw [Nat.div_eq_of_lt this]

theorem bt_mask32 {b : Nat} (hb : b < 32) : bt mask32 b = 1 := by
  rw [bt_eq, show mask32 = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  simp [hb]

theorem testBit_rotr {x n b : Nat} (hx : x < 2 ^ 32) (hn : n < 32) (hb : b < 32) :
    (rotr x n).testBit b = x.testBit ((b + n) % 32) := by
  unfold rotr
  rw [show mask32 = 2 ^ 32 - 1 from rfl, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight,
    Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h : b + n < 32
  · rw [Nat.mod_eq_of_lt h]
    have h1 : ¬ (b ≥ 32 - n) := by omega
    simp [h1, hb, Nat.add_comm]
  · have h1 : x.testBit (n + b) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
    have h2 : (b + n) % 32 = b - (32 - n) := by omega
    have h3 : b ≥ 32 - n := by omega
    simp [h1, h2, h3, hb]

theorem bt_rotr {x n b : Nat} (hx : x < 2 ^ 32) (hn : n < 32) (hb : b < 32) :
    bt (rotr x n) b = bt x ((b + n) % 32) := by
  rw [bt_eq, bt_eq, testBit_rotr hx hn hb]

theorem bt_sig3 {x r1 r2 r3 b : Nat} (hx : x < 2 ^ 32) (h1 : r1 < 32) (h2 : r2 < 32) (h3 : r3 < 32)
    (hb : b < 32) :
    bt (rotr x r1 ^^^ rotr x r2 ^^^ rotr x r3) b =
      ((bt x ((b + r1) % 32) + bt x ((b + r2) % 32)) % 2 + bt x ((b + r3) % 32)) % 2 := by
  rw [bt_xor, bt_xor, bt_rotr hx h1 hb, bt_rotr hx h2 hb, bt_rotr hx h3 hb]

theorem bt_sigS {x r1 r2 r3 b : Nat} (hx : x < 2 ^ 32) (h1 : r1 < 32) (h2 : r2 < 32)
    (hb : b < 32) :
    bt (rotr x r1 ^^^ rotr x r2 ^^^ (x >>> r3)) b =
      ((bt x ((b + r1) % 32) + bt x ((b + r2) % 32)) % 2 +
        (if b + r3 < 32 then bt x (b + r3) else 0)) % 2 := by
  rw [bt_xor, bt_xor, bt_rotr hx h1 hb, bt_rotr hx h2 hb, bt_shiftRight, Nat.add_comm r3 b]
  by_cases h : b + r3 < 32
  · simp only [h, ite_true]
  · simp only [h, ite_false, bt_of_lt (b := b + r3) hx (by omega)]

theorem bt_ch {x y z b : Nat} (hb : b < 32) :
    bt (ch x y z) b = (bt x b * bt y b + ((bt x b + 1) % 2) * bt z b) % 2 := by
  unfold ch
  rw [bt_xor, bt_and, bt_and, bt_xor, bt_mask32 hb]

theorem bt_maj (x y z b : Nat) :
    bt (maj x y z) b = ((bt x b * bt y b + bt x b * bt z b) % 2 + bt y b * bt z b) % 2 := by
  unfold maj
  rw [bt_xor, bt_xor, bt_and, bt_and, bt_and]

theorem rotr_lt (x n : Nat) : rotr x n < 2 ^ 32 := by
  unfold rotr; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem sig3_lt (x r1 r2 r3 : Nat) : rotr x r1 ^^^ rotr x r2 ^^^ rotr x r3 < 2 ^ 32 :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (rotr_lt _ _) (rotr_lt _ _)) (rotr_lt _ _)

theorem sigS_lt {x : Nat} (hx : x < 2 ^ 32) (r1 r2 r3 : Nat) :
    rotr x r1 ^^^ rotr x r2 ^^^ (x >>> r3) < 2 ^ 32 :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (rotr_lt _ _) (rotr_lt _ _))
    (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hx)

theorem ch_lt (x : Nat) {y z : Nat} (hy : y < 2 ^ 32) (hz : z < 2 ^ 32) : ch x y z < 2 ^ 32 := by
  unfold ch
  exact Nat.xor_lt_two_pow (Nat.and_lt_two_pow _ hy) (Nat.and_lt_two_pow _ hz)

theorem maj_lt (x : Nat) {y z : Nat} (hy : y < 2 ^ 32) (hz : z < 2 ^ 32) : maj x y z < 2 ^ 32 := by
  unfold maj
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.and_lt_two_pow _ hy) (Nat.and_lt_two_pow _ hz))
    (Nat.and_lt_two_pow _ hz)

/-! ## `ofBits` -/

theorem ofBits_succ (f : Nat → Nat) (n : Nat) : ofBits f (n + 1) = ofBits f n + 2 ^ n * f n := rfl

theorem ofBits_congr {f g : Nat → Nat} {n : Nat} (h : ∀ b, b < n → f b = g b) :
    ofBits f n = ofBits g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ofBits_succ, ofBits_succ, ih (fun b hb => h b (by omega)), h n (by omega)]

theorem ofBits_lt {f : Nat → Nat} {n : Nat} (h : ∀ b, b < n → f b ≤ 1) : ofBits f n < 2 ^ n := by
  induction n with
  | zero => show 0 < 1; decide
  | succ n ih =>
    rw [ofBits_succ, Nat.pow_succ]
    have := ih (fun b hb => h b (by omega))
    have : 2 ^ n * f n ≤ 2 ^ n * 1 := Nat.mul_le_mul_left _ (h n (by omega))
    omega

theorem ofBits_add (f : Nat → Nat) (m n : Nat) :
    ofBits f (m + n) = ofBits f m + 2 ^ m * ofBits (fun b => f (m + b)) n := by
  induction n with
  | zero => simp [ofBits]
  | succ n ih =>
    rw [← Nat.add_assoc, ofBits_succ, ih, ofBits_succ, Nat.pow_add, Nat.mul_add, Nat.mul_assoc,
      Nat.add_assoc]

theorem ofBits_bt (x n : Nat) : ofBits (bt x) n = x % 2 ^ n := by
  induction n with
  | zero => simp [ofBits, Nat.mod_one]
  | succ n ih => rw [ofBits_succ, ih, Nat.mod_pow_succ]; rfl

theorem bt_ofBits {f : Nat → Nat} {n c : Nat} (h : ∀ b, b < n → f b ≤ 1) (hc : c < n) :
    bt (ofBits f n) c = f c := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [ofBits_succ]
    have hA := ofBits_lt (fun b hb => h b (by omega) : ∀ b, b < n → f b ≤ 1)
    by_cases hcn : c < n
    · rw [← ih (fun b hb => h b (by omega)) hcn]
      unfold bt
      obtain ⟨d, hd⟩ : ∃ d, n = c + 1 + d := ⟨n - c - 1, by omega⟩
      have e : 2 ^ n * f n = 2 ^ c * (2 * (2 ^ d * f n)) := by
        rw [hd, Nat.pow_add, Nat.pow_succ]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos c)]
      omega
    · have hc' : c = n := by omega
      subst hc'
      unfold bt
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos c), Nat.div_eq_of_lt hA]
      have := h c (by omega)
      omega

end ZkFormal.Sha.Sound
