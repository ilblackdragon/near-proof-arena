import ZkFormal.Algebra.Transport
import ZkFormal.Algebra.NatPrime

/-!
# ZkFormal.Algebra.Fp — the BabyBear field `F_p`, `p = 15·2^27 + 1`

One type serves as both the specification and the executable field: an
element is a `UInt32` below `p`, addition/subtraction are conditional
subtractions on `UInt32`, multiplication is a `UInt64` product reduced
mod `p`.  So the compiled verifier (lane L4) uses the spec field directly
and there is no separate refinement step; the proven bridge to arithmetic
mod `p` is `toNat_add`, `toNat_mul`, … and `toFin` (into core's `Fin p`).

Main results:
* `p_prime : IsPrime P` — kernel trial division up to `√p < 44 870`;
* `instance : Lean.Grind.Field Fp`, `IsCharP Fp P`;
* `pow_card_sub_one : a ≠ 0 → a ^ (P - 1) = 1` (Fermat);
* `eleven_nonsquare : ∀ x : Fp, x * x ≠ 11` (Euler's criterion);
* `sqrtNegOne_sq : sqrtNegOne * sqrtNegOne = -1`;
* two-adic generators `twoAdicGen k` (`k ≤ 27`) of exact order `2^k`.
-/

namespace ZkFormal.Algebra

open Lean.Grind

/-- The BabyBear prime. -/
def P : Nat := 2013265921

theorem P_eq : P = 15 * 2 ^ 27 + 1 := rfl

theorem P_lt : P < 2 ^ 31 := by decide

/-- **`p` is prime** (kernel trial division, ≈5 s). -/
theorem p_prime : IsPrime P :=
  isPrime_of_trialDiv (fuel := 44870) (by decide) (by decide +kernel)

instance : NeZero P := ⟨by decide⟩

/-- BabyBear field element: a `UInt32` below `p`. -/
structure Fp where
  val : UInt32
  isLt : val.toNat < P

namespace Fp

/-- The canonical representative in `[0, p)`. -/
@[inline] def toNat (a : Fp) : Nat := a.val.toNat

theorem toNat_lt (a : Fp) : a.toNat < P := a.isLt

theorem ext {a b : Fp} (h : a.toNat = b.toNat) : a = b := by
  cases a; cases b
  simp only [toNat] at h
  simp only [Fp.mk.injEq]
  exact UInt32.toNat_inj.mp h

theorem toNat_inj {a b : Fp} : a.toNat = b.toNat ↔ a = b := ⟨ext, fun h => h ▸ rfl⟩

instance : DecidableEq Fp := fun a b =>
  if h : a.val = b.val then isTrue (by cases a; cases b; simp only at h; subst h; rfl)
  else isFalse (fun e => h (e ▸ rfl))

@[inline] def P32 : UInt32 := 2013265921
@[inline] def P64 : UInt64 := 2013265921

theorem P32_toNat : P32.toNat = P := rfl
theorem P64_toNat : P64.toNat = P := rfl

/-- `n mod p`. -/
@[inline] def ofNat (n : Nat) : Fp :=
  ⟨UInt32.ofNat (n % P), by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))]
    exact Nat.mod_lt _ (by decide)⟩

@[simp] theorem toNat_ofNat (n : Nat) : (ofNat n).toNat = n % P := by
  simp only [ofNat, toNat, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

@[inline] def add (a b : Fp) : Fp :=
  let s := a.val + b.val
  ⟨if P32 ≤ s then s - P32 else s, by
    have ha := a.isLt; have hb := b.isLt
    have hs : s.toNat = a.val.toNat + b.val.toNat := by
      simp only [s, UInt32.toNat_add]; rw [Nat.mod_eq_of_lt]; unfold P at ha hb; omega
    split
    · next h =>
      rw [UInt32.le_iff_toNat_le] at h
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr h), hs, P32_toNat]
      rw [hs, P32_toNat] at h; omega
    · next h =>
      rw [UInt32.le_iff_toNat_le, hs, P32_toNat] at h; rw [hs]; omega⟩

@[simp] theorem toNat_add (a b : Fp) : (add a b).toNat = (a.toNat + b.toNat) % P := by
  have ha := a.isLt; have hb := b.isLt
  have hs : (a.val + b.val).toNat = a.val.toNat + b.val.toNat := by
    simp only [UInt32.toNat_add]; rw [Nat.mod_eq_of_lt]; unfold P at ha hb; omega
  simp only [add, toNat]
  split
  · next h =>
    rw [UInt32.le_iff_toNat_le, hs, P32_toNat] at h
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [hs, P32_toNat]; exact h)),
      hs, P32_toNat]
    have : a.val.toNat + b.val.toNat - P < P := by omega
    rw [← Nat.mod_eq_of_lt this, Nat.mod_eq_sub_mod h]
  · next h =>
    rw [UInt32.le_iff_toNat_le, hs, P32_toNat] at h
    rw [hs, Nat.mod_eq_of_lt (by omega)]

@[inline] def neg (a : Fp) : Fp :=
  ⟨if a.val = 0 then 0 else P32 - a.val, by
    have ha := a.isLt
    split
    · simp; decide
    · next h =>
      have h0 : a.val.toNat ≠ 0 := fun e => h (UInt32.toNat_inj.mp (by simpa using e))
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [P32_toNat]; omega)),
        P32_toNat]; omega⟩

@[simp] theorem toNat_neg (a : Fp) : (neg a).toNat = (P - a.toNat) % P := by
  have ha := a.isLt
  simp only [neg, toNat]
  split
  · next h => rw [h]; simp
  · next h =>
    have h0 : a.val.toNat ≠ 0 := fun e => h (UInt32.toNat_inj.mp (by simpa using e))
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [P32_toNat]; omega)),
      P32_toNat, Nat.mod_eq_of_lt (by omega)]

@[inline] def sub (a b : Fp) : Fp :=
  ⟨if b.val ≤ a.val then a.val - b.val else a.val + (P32 - b.val), by
    have ha := a.isLt; have hb := b.isLt
    split
    · next h =>
      rw [UInt32.toNat_sub_of_le _ _ h]; omega
    · next h =>
      rw [UInt32.le_iff_toNat_le] at h
      have h1 : (P32 - b.val).toNat = P - b.val.toNat := by
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [P32_toNat]; omega)),
          P32_toNat]
      rw [UInt32.toNat_add, h1, Nat.mod_eq_of_lt (by unfold P at *; omega)]; omega⟩

@[simp] theorem toNat_sub (a b : Fp) : (sub a b).toNat = (a.toNat + (P - b.toNat)) % P := by
  have ha := a.isLt; have hb := b.isLt
  simp only [sub, toNat]
  split
  · next h =>
    rw [UInt32.le_iff_toNat_le] at h
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr h)]
    rw [show a.val.toNat + (P - b.val.toNat) = (a.val.toNat - b.val.toNat) + P by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · next h =>
    rw [UInt32.le_iff_toNat_le] at h
    have h1 : (P32 - b.val).toNat = P - b.val.toNat := by
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [P32_toNat]; omega)),
        P32_toNat]
    rw [UInt32.toNat_add, h1, Nat.mod_eq_of_lt (by unfold P at *; omega),
      Nat.mod_eq_of_lt (by omega)]

@[inline] def mul (a b : Fp) : Fp :=
  ⟨((a.val.toUInt64 * b.val.toUInt64) % P64).toUInt32, by
    have ha := a.isLt; have hb := b.isLt
    have hm : (a.val.toUInt64 * b.val.toUInt64).toNat = a.val.toNat * b.val.toNat := by
      rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64, Nat.mod_eq_of_lt]
      exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (by omega))
        (by decide)
    rw [UInt64.toNat_toUInt32, UInt64.toNat_mod, hm, P64_toNat,
      Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))]
    exact Nat.mod_lt _ (by decide)⟩

@[simp] theorem toNat_mul (a b : Fp) : (mul a b).toNat = a.toNat * b.toNat % P := by
  have ha := a.isLt; have hb := b.isLt
  have hm : (a.val.toUInt64 * b.val.toUInt64).toNat = a.val.toNat * b.val.toNat := by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64, Nat.mod_eq_of_lt]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (by omega))
      (by decide)
  simp only [mul, toNat]
  rw [UInt64.toNat_toUInt32, UInt64.toNat_mod, hm, P64_toNat,
    Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))]


/-- Integer cast: `i mod p`. -/
def ofInt : Int → Fp
  | .ofNat n => ofNat n
  | .negSucc n => neg (ofNat (n + 1))

instance : Add Fp := ⟨add⟩
instance : Mul Fp := ⟨mul⟩
instance : Neg Fp := ⟨neg⟩
instance : Sub Fp := ⟨sub⟩
instance (n : Nat) : OfNat Fp n := ⟨ofNat n⟩
instance : NatCast Fp := ⟨ofNat⟩
instance : IntCast Fp := ⟨ofInt⟩
instance : SMul Nat Fp := ⟨fun k a => mul (ofNat k) a⟩
instance : SMul Int Fp := ⟨fun k a => mul (ofInt k) a⟩
/-- Powers by square-and-multiply. -/
instance : HPow Fp Nat Fp := ⟨fun a n => binPow n a (ofNat 1) n⟩
instance : Inhabited Fp := ⟨ofNat 0⟩
instance : Repr Fp := ⟨fun a _ => repr a.toNat⟩
instance : ToString Fp := ⟨fun a => toString a.toNat⟩

theorem add_def (a b : Fp) : a + b = add a b := rfl
theorem mul_def (a b : Fp) : a * b = mul a b := rfl
theorem neg_def (a : Fp) : -a = neg a := rfl
theorem sub_def (a b : Fp) : a - b = sub a b := rfl
theorem ofNat_def (n : Nat) : (OfNat.ofNat n : Fp) = ofNat n := rfl

/-- The embedding into core's `Fin p` (a `Lean.Grind.CommRing`). -/
def toFin (a : Fp) : Fin P := ⟨a.toNat, a.isLt⟩

theorem toFin_inj (a b : Fp) (h : toFin a = toFin b) : a = b := by
  have := congrArg Fin.val h
  exact ext this

theorem toFin_ofNat (n : Nat) : toFin (ofNat n) = (OfNat.ofNat n : Fin P) := by
  apply Fin.ext; simp [toFin]; rfl

theorem toFin_mul (a b : Fp) : toFin (a * b) = toFin a * toFin b := by
  apply Fin.ext; simp [toFin, Fin.mul_def, mul_def]

theorem toFin_neg (a : Fp) : toFin (-a) = -toFin a := by
  apply Fin.ext; simp [toFin, Fin.neg_def, neg_def]

attribute [local instance] Semiring.natCast Ring.intCast

theorem toFin_ofInt (i : Int) : toFin (ofInt i) = (Int.cast i : Fin P) := by
  cases i with
  | ofNat n =>
    simp only [ofInt]; rw [toFin_ofNat]
    show _ = Fin.intCast _
    simp [Fin.intCast]; rfl
  | negSucc n =>
    simp only [ofInt]; rw [← neg_def, toFin_neg, toFin_ofNat]
    show _ = Fin.intCast _
    simp [Fin.intCast]; rfl

/-- `toFin` preserves every ring operation. -/
def finEmbedding : Embedding Fp (Fin P) where
  f := toFin
  inj := toFin_inj
  map_add a b := by apply Fin.ext; simp [toFin, Fin.add_def, add_def]
  map_mul := toFin_mul
  map_neg := toFin_neg
  map_sub a b := by apply Fin.ext; simp [toFin, Fin.sub_def, sub_def, Nat.add_comm]
  map_ofNat n := toFin_ofNat n
  map_natCast n := toFin_ofNat n
  map_intCast i := toFin_ofInt i
  map_nsmul n a := by
    show toFin (mul (ofNat n) a) = _
    rw [← mul_def, toFin_mul, toFin_ofNat]; rfl
  map_zsmul i a := by
    show toFin (mul (ofInt i) a) = _
    rw [← mul_def, toFin_mul, toFin_ofInt]; rfl
  map_pow a n := by
    show toFin (binPow n a (ofNat 1) n) = _
    rw [map_binPow toFin toFin_mul, binPow_eq _ _ _ _ (Nat.le_refl _), toFin_ofNat,
      Semiring.one_mul]

instance commRing : CommRing Fp := CommRing.ofEmbedding finEmbedding

theorem toNat_pow (a : Fp) (n : Nat) : (a ^ n).toNat = a.toNat ^ n % P := by
  induction n with
  | zero => show (binPow 0 a (ofNat 1) 0).toNat = _; simp [binPow]
  | succ n ih =>
    rw [Semiring.pow_succ, mul_def, toNat_mul, ih, Nat.pow_succ, Nat.mod_mul_mod]

theorem toNat_zero : (0 : Fp).toNat = 0 := rfl
theorem toNat_one : (1 : Fp).toNat = 1 := rfl

theorem eq_zero_iff (a : Fp) : a = 0 ↔ a.toNat = 0 := by
  rw [← toNat_inj]; rfl

/-! ## Fermat and the field structure -/

/-- **Fermat's little theorem** in `F_p`. -/
theorem pow_card_sub_one {a : Fp} (ha : a ≠ 0) : a ^ (P - 1) = 1 := by
  apply ext
  rw [toNat_pow, toNat_one]
  have h : a.toNat % P ≠ 0 := by
    rw [Nat.mod_eq_of_lt a.toNat_lt]; exact fun h => ha ((eq_zero_iff a).mpr h)
  exact fermat p_prime h

/-- Inverse as `a^(p-2)` (`0⁻¹ = 0`). -/
instance : Inv Fp := ⟨fun a => a ^ (P - 2)⟩

theorem inv_def (a : Fp) : a⁻¹ = a ^ (P - 2) := rfl

theorem mul_inv_cancel {a : Fp} (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  rw [inv_def, ← pow_card_sub_one ha, show P - 1 = 1 + (P - 2) by decide, Semiring.pow_add,
    Semiring.pow_one]

instance field : Field Fp :=
  Field.ofInv (by decide +kernel) (by decide +kernel) mul_inv_cancel

instance : IsCharP Fp P := IsCharP.mk' _ _ (ofNat_eq_zero_iff := fun x => by
  show ofNat x = ofNat 0 ↔ _
  rw [← toNat_inj, toNat_ofNat, toNat_ofNat]; simp)

/-! ## Enumeration -/

theorem ofNat_toNat (a : Fp) : ofNat a.toNat = a := ext (by rw [toNat_ofNat, Nat.mod_eq_of_lt a.toNat_lt])

/-- All `p` field elements (never evaluated; used for counting). -/
def all : List Fp := (List.range P).map ofNat

theorem mem_all (a : Fp) : a ∈ all :=
  List.mem_map.mpr ⟨a.toNat, List.mem_range.mpr a.toNat_lt, ofNat_toNat a⟩

theorem nodup_all : all.Nodup :=
  nodup_map_on (fun x hx y hy h => by
    have := congrArg toNat h
    rwa [toNat_ofNat, toNat_ofNat, Nat.mod_eq_of_lt (List.mem_range.mp hx),
      Nat.mod_eq_of_lt (List.mem_range.mp hy)] at this) List.nodup_range

theorem length_all : all.length = P := by simp [all]

/-! ## Distinguished elements -/

/-- `11` is a quadratic non-residue: Euler's criterion, `11^((p-1)/2) = -1`. -/
theorem eleven_pow_half : (11 : Fp) ^ ((P - 1) / 2) = -1 := by decide +kernel

theorem neg_one_ne_one : (-1 : Fp) ≠ 1 := by decide +kernel

/-- **`11` is not a square in `F_p`.** -/
theorem eleven_nonsquare (x : Fp) : x * x ≠ 11 := by
  intro h
  have hx : x ≠ 0 := by intro h0; rw [h0] at h; exact absurd h (by decide +kernel)
  have h1 : (11 : Fp) ^ ((P - 1) / 2) = 1 := by
    rw [← h, ← pow_two_mul, show 2 * ((P - 1) / 2) = P - 1 by decide, pow_card_sub_one hx]
  exact neg_one_ne_one (eleven_pow_half ▸ h1)

/-- A square root of `-1` (`p ≡ 1 mod 4`): `31^((p-1)/4)`. -/
def sqrtNegOne : Fp := (31 : Fp) ^ ((P - 1) / 4)

theorem sqrtNegOne_sq : sqrtNegOne * sqrtNegOne = -1 := by decide +kernel

/-! ## Two-adic generators -/

/-- The two-adicity of `p - 1`. -/
def twoAdicity : Nat := 27

/-- A generator of the order-`2^27` subgroup: `31^15` (`31` generates `F_p^×`). -/
def twoAdicGen27 : Fp := (31 : Fp) ^ 15

/-- A generator of the subgroup of order `2^k` (for `k ≤ 27`). -/
def twoAdicGen (k : Nat) : Fp := twoAdicGen27 ^ (2 ^ (27 - k))

theorem twoAdicGen27_pow_half : twoAdicGen27 ^ (2 ^ 26) = -1 := by decide +kernel

theorem twoAdicGen_pow_half {k : Nat} (hk1 : 1 ≤ k) (hk : k ≤ 27) :
    twoAdicGen k ^ (2 ^ (k - 1)) = -1 := by
  rw [twoAdicGen, ← pow_mul_eq, ← Nat.pow_add, show 27 - k + (k - 1) = 26 by omega,
    twoAdicGen27_pow_half]

/-- `twoAdicGen k` has order dividing `2^k` … -/
theorem twoAdicGen_pow {k : Nat} (hk : k ≤ 27) : twoAdicGen k ^ (2 ^ k) = 1 := by
  rw [twoAdicGen, ← pow_mul_eq, ← Nat.pow_add, show 27 - k + k = 26 + 1 by omega,
    Nat.pow_succ, pow_mul_eq, twoAdicGen27_pow_half]
  decide +kernel

/-- … and exactly `2^k`: its powers below `2^k` are distinct. -/
theorem twoAdicGen_pow_inj {k : Nat} (hk : k ≤ 27) {i j : Nat} (hi : i < 2 ^ k) (hj : j < 2 ^ k)
    (h : twoAdicGen k ^ i = twoAdicGen k ^ j) : i = j :=
  pow_inj_of_half (twoAdicGen k) k (fun hk1 => twoAdicGen_pow_half hk1 hk) neg_one_ne_one hi hj h

theorem twoAdicGen_ne_zero (k : Nat) (hk : k ≤ 27) : twoAdicGen k ≠ 0 := by
  intro h
  have := twoAdicGen_pow hk
  rw [h, show 2 ^ k = (2 ^ k - 1) + 1 by have := Nat.pow_pos (n := k) (show 0 < 2 by decide); omega,
    Semiring.pow_succ, Semiring.mul_zero] at this
  exact absurd this (by decide +kernel)

end Fp
end ZkFormal.Algebra
