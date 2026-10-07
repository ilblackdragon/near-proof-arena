import ZkFormal.NearV3.Render.Ups.Gen

/-! Integer arithmetic for the two honest memory-usage carry chains. -/
set_option maxHeartbeats 2000000

namespace ZkFormal.NearV3.Render.UpsGen

/-- The carry defined from prefix sums satisfies the byte recurrence, even when
individual input limbs are negative or larger than a byte. -/
theorem pfx_byte_carry (f : Nat → Int) {i : Nat} (hi : i < 8) :
    f i + (if i = 0 then 0 else
      (pfx f i - pfx f 8 % 256 ^ i) / 256 ^ i) =
    pfx f 8 / 256 ^ i % 256 +
      256 * ((pfx f (i + 1) - pfx f 8 % 256 ^ (i + 1)) / 256 ^ (i + 1)) := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [pfx, Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false,
      Int.reducePow, Int.zero_add, Int.mul_one, Int.emod_one, Int.ediv_one] <;> omega

/-- A prefix-sum carry at the last byte is exactly the high limb. -/
theorem pfx_last_carry (f : Nat → Int) :
    (pfx f 8 - pfx f 8 % 256 ^ 8) / 256 ^ 8 = pfx f 8 / 256 ^ 8 := by
  simp only [Int.reducePow]
  omega

/-- Multiplying the input limbs multiplies every prefix sum. -/
theorem pfx_mul (s : Int) (f : Nat → Int) : ∀ n,
    pfx (fun i => s * f i) n = s * pfx f n
  | 0 => by simp [pfx]
  | n + 1 => by
    simp only [pfx, pfx_mul s f n, Int.mul_add, Int.mul_assoc]

/-- Inside-chain recurrence for the generator's actual signed limbs. -/
theorem inside_carry (I : UpsInst) (Q : UpsPartI) {i : Nat} (hi : i < 8) :
    sigV Q * X1V I Q i + (if i = 0 then 0 else coV I Q (i - 1)) =
      tV I Q i + 256 * coV I Q i := by
  have h := pfx_byte_carry (fun j => sigV Q * X1V I Q j) hi
  simp only [pfx_mul] at h
  by_cases hz : i = 0
  · subst i
    simpa only [coV, TV, tV, Nat.reduceAdd, ite_true] using h
  · have he : i - 1 + 1 = i := by omega
    simpa only [coV, TV, tV, hz, ite_false, he] using h

/-- Eight byte limbs reconstruct exactly the low 64 bits, including for signed integers. -/
theorem pfx_bytes (x : Int) :
    pfx (fun i => x / 256 ^ i % 256) 8 = x % 256 ^ 8 := by
  simp only [pfx, Int.reducePow, Int.zero_add, Int.mul_one, Int.ediv_one]
  omega

/-- Outside-chain recurrence for either value of the truncation bit. -/
theorem outside_carry (I : UpsInst) (Q : UpsPartI) (hn : Q.neg ≤ 1)
    {i : Nat} (hi : i < 8) :
    EinV I Q i + (1 - (Q.neg : Int)) * tV I Q i +
      (if i = 0 then 0 else co2V I Q (i - 1)) =
    RV I Q / 256 ^ i % 256 + 256 * co2V I Q i := by
  rcases (show Q.neg = 0 ∨ Q.neg = 1 by omega) with he | he <;>
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [co2V, RV, tV, pfx, he, Nat.reduceAdd, Nat.reduceSub, Nat.reduceEqDiff,
      ite_true, ite_false, Int.natCast_zero, Int.natCast_one, Int.reduceSub,
      Int.reducePow, Int.zero_add, Int.add_zero, Int.mul_one, Int.one_mul, Int.zero_mul,
      Int.emod_one, Int.ediv_one] <;> omega

/-- Prefix sums distribute over addition. -/
theorem pfx_add (f g : Nat → Int) : ∀ n,
    pfx (fun i => f i + g i) n = pfx f n + pfx g n
  | 0 => by simp [pfx]
  | n + 1 => by
    simp only [pfx, pfx_add f g n, Int.add_mul]
    omega

/-- The inside carry on the last row is the exact high limb of T. -/
theorem inside_last_high (I : UpsInst) (Q : UpsPartI) :
    coV I Q 7 = TV I Q / 256 ^ 8 := by
  simp only [coV, TV, Nat.reduceAdd, Int.reducePow]
  omega

/-- Exact final limb sent to the parent, including overflow above the stored eight bytes. -/
theorem outside_last_high (I : UpsInst) (Q : UpsPartI) (hn : Q.neg ≤ 1) :
    limb (RV I Q) 7 = RV I Q / 256 ^ 7 % 256 +
      256 * ((1 - (Q.neg : Int)) * coV I Q 7 + co2V I Q 7) := by
  have hp : pfx (fun i => EinV I Q i + (1 - (Q.neg : Int)) * tV I Q i) 8 =
      pfx (EinV I Q) 8 + (1 - (Q.neg : Int)) * (TV I Q % 256 ^ 8) := by
    rw [pfx_add, pfx_mul]
    unfold tV
    rw [pfx_bytes]
  rw [inside_last_high]
  simp only [co2V, Nat.reduceAdd, hp]
  rcases (show Q.neg = 0 ∨ Q.neg = 1 by omega) with he | he <;>
    simp only [limb, RV, he, Nat.lt_irrefl, ite_false, Int.natCast_zero,
      Int.natCast_one, Int.reduceSub, Int.zero_mul, Int.one_mul, Int.add_zero, Int.reducePow] <;> omega

/-- The eight bit-registers reconstruct any byte. -/
theorem byte_bits (x : Int) (h0 : 0 ≤ x) (h1 : x < 256) :
    x % 2 + 2 * (x / 2 % 2) + 4 * (x / 4 % 2) + 8 * (x / 8 % 2) +
    16 * (x / 16 % 2) + 32 * (x / 32 % 2) + 64 * (x / 64 % 2) +
    128 * (x / 128 % 2) = x := by omega

/-- The three bit-registers reconstruct a bounded carry. -/
theorem carry_bits (x : Int) (h0 : 0 ≤ x) (h1 : x < 8) :
    x % 2 + 2 * (x / 2 % 2) + 4 * (x / 4 % 2) = x := by omega

end ZkFormal.NearV3.Render.UpsGen
