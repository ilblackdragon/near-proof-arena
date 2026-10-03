/-!
# ZkFormal.Algebra.Transport — building `Lean.Grind` ring/field instances

Two generic constructions, used for the concrete fields of the backend
(DESIGN.md §9 L1):

* `CommRing.ofEmbedding` — transport a commutative-ring structure along an
  injective map `f : β → α` into a commutative ring `α` that preserves all
  the operations.  Used for `Fp` (embedded in core's `Fin p`) and for the flat
  `Fp8` (embedded in the quadratic tower).
* `Field.ofInv` — a `Field` from a `CommRing` with an inverse satisfying
  `0⁻¹ = 0` and `a ≠ 0 → a·a⁻¹ = 1`; division and integer powers are the
  canonical ones.
-/

namespace ZkFormal.Algebra

open Lean.Grind

universe u v

attribute [local instance] Semiring.natCast Ring.intCast

/-- An operation-preserving injection of a ring-shaped type `β` into a
commutative ring `α`. -/
structure Embedding (β : Type u) (α : Type v) [CommRing α]
    [Add β] [Mul β] [Neg β] [Sub β] [∀ n, OfNat β n] [NatCast β] [IntCast β]
    [SMul Nat β] [SMul Int β] [HPow β Nat β] where
  f : β → α
  inj : ∀ a b, f a = f b → a = b
  map_add : ∀ a b, f (a + b) = f a + f b
  map_mul : ∀ a b, f (a * b) = f a * f b
  map_neg : ∀ a, f (-a) = -f a
  map_sub : ∀ a b, f (a - b) = f a - f b
  map_ofNat : ∀ n, f (OfNat.ofNat n) = OfNat.ofNat n
  map_natCast : ∀ n : Nat, f (n : β) = (n : α)
  map_intCast : ∀ i : Int, f (i : β) = (i : α)
  map_nsmul : ∀ (n : Nat) a, f (n • a) = n • f a
  map_zsmul : ∀ (i : Int) a, f (i • a) = i • f a
  map_pow : ∀ a (n : Nat), f (a ^ n) = f a ^ n

/-- Transport of a commutative ring structure along an `Embedding`. -/
@[reducible] def CommRing.ofEmbedding {β : Type u} {α : Type v} [CommRing α]
    [Add β] [Mul β] [Neg β] [Sub β] [iO : ∀ n, OfNat β n] [iN : NatCast β] [iI : IntCast β]
    [iS : SMul Nat β] [iZ : SMul Int β] [iP : HPow β Nat β] (e : Embedding β α) : CommRing β where
  natCast := iN
  ofNat := iO
  nsmul := iS
  npow := iP
  intCast := iI
  zsmul := iZ
  add_zero a := e.inj _ _ (by rw [e.map_add, e.map_ofNat, Semiring.add_zero])
  add_comm a b := e.inj _ _ (by rw [e.map_add, e.map_add, Semiring.add_comm])
  add_assoc a b c := e.inj _ _ (by simp only [e.map_add, Semiring.add_assoc])
  mul_assoc a b c := e.inj _ _ (by simp only [e.map_mul, Semiring.mul_assoc])
  mul_one a := e.inj _ _ (by rw [e.map_mul, e.map_ofNat, Semiring.mul_one])
  one_mul a := e.inj _ _ (by rw [e.map_mul, e.map_ofNat, Semiring.one_mul])
  left_distrib a b c := e.inj _ _ (by simp only [e.map_mul, e.map_add, Semiring.left_distrib])
  right_distrib a b c := e.inj _ _ (by simp only [e.map_mul, e.map_add, Semiring.right_distrib])
  zero_mul a := e.inj _ _ (by rw [e.map_mul, e.map_ofNat, Semiring.zero_mul])
  mul_zero a := e.inj _ _ (by rw [e.map_mul, e.map_ofNat, Semiring.mul_zero])
  pow_zero a := e.inj _ _ (by rw [e.map_pow, e.map_ofNat, Semiring.pow_zero])
  pow_succ a n := e.inj _ _ (by rw [e.map_pow, e.map_mul, e.map_pow, Semiring.pow_succ])
  ofNat_succ n := e.inj _ _ (by rw [e.map_add, e.map_ofNat, e.map_ofNat, e.map_ofNat,
    Semiring.ofNat_succ])
  ofNat_eq_natCast n := e.inj _ _ (by rw [e.map_ofNat, e.map_natCast, Semiring.ofNat_eq_natCast])
  nsmul_eq_natCast_mul n a := e.inj _ _ (by
    rw [e.map_nsmul, e.map_mul, e.map_natCast, Semiring.nsmul_eq_natCast_mul])
  neg_add_cancel a := e.inj _ _ (by rw [e.map_add, e.map_neg, e.map_ofNat, Ring.neg_add_cancel])
  sub_eq_add_neg a b := e.inj _ _ (by rw [e.map_sub, e.map_add, e.map_neg, Ring.sub_eq_add_neg])
  neg_zsmul i a := e.inj _ _ (by rw [e.map_zsmul, e.map_neg, e.map_zsmul, Ring.neg_zsmul])
  zsmul_natCast_eq_nsmul n a := e.inj _ _ (by
    rw [e.map_zsmul, e.map_nsmul, Ring.zsmul_natCast_eq_nsmul])
  intCast_ofNat n := e.inj _ _ (by rw [e.map_intCast, e.map_ofNat, Ring.intCast_ofNat])
  intCast_neg i := e.inj _ _ (by rw [e.map_intCast, e.map_neg, e.map_intCast, Ring.intCast_neg])
  mul_comm a b := e.inj _ _ (by rw [e.map_mul, e.map_mul, CommSemiring.mul_comm])

/-- Canonical integer powers from natural powers and an inverse. -/
def zpowOf {α : Type u} [HPow α Nat α] [Inv α] (a : α) : Int → α
  | .ofNat n => a ^ n
  | .negSucc n => (a ^ (n + 1))⁻¹

/-- A `Field` from a commutative ring with a lawful inverse. -/
@[reducible] def Field.ofInv {α : Type u} [R : CommRing α] [I : Inv α]
    (zero_ne_one : (0 : α) ≠ 1) (inv_zero : (0 : α)⁻¹ = 0)
    (mul_inv_cancel : ∀ {a : α}, a ≠ 0 → a * a⁻¹ = 1) : Field α :=
  have inv_inv : ∀ a : α, a⁻¹⁻¹ = a := by
    intro a
    by_cases ha : a = 0
    · subst ha; rw [inv_zero, inv_zero]
    · have h1 := mul_inv_cancel ha
      have hi : a⁻¹ ≠ 0 := by
        intro h; rw [h, Semiring.mul_zero] at h1; exact zero_ne_one h1
      have h2 := mul_inv_cancel hi
      calc a⁻¹⁻¹ = (a * a⁻¹) * a⁻¹⁻¹ := by rw [h1, Semiring.one_mul]
        _ = a * (a⁻¹ * a⁻¹⁻¹) := Semiring.mul_assoc _ _ _
        _ = a := by rw [h2, Semiring.mul_one]
  have inv_one : (1 : α)⁻¹ = 1 := by
    have := mul_inv_cancel (a := (1 : α)) (fun h => zero_ne_one h.symm)
    rwa [Semiring.one_mul] at this
  { R, I with
    div := fun a b => a * b⁻¹
    zpow := ⟨zpowOf⟩
    div_eq_mul_inv := fun _ _ => rfl
    zero_ne_one := zero_ne_one
    inv_zero := inv_zero
    mul_inv_cancel := mul_inv_cancel
    zpow_zero := fun a => Semiring.pow_zero a
    zpow_succ := fun a n => Semiring.pow_succ a n
    zpow_neg := fun a n => by
      match n with
      | .ofNat 0 => show a ^ (0 : Nat) = (a ^ (0 : Nat))⁻¹; rw [Semiring.pow_zero, inv_one]
      | .ofNat (k + 1) => rfl
      | .negSucc k => show a ^ (k + 1 : Nat) = ((a ^ (k + 1 : Nat))⁻¹)⁻¹; rw [inv_inv] }

/-! ## Square-and-multiply -/

/-- Square-and-multiply: `binPow fuel b acc n = acc · b^n` whenever `n ≤ fuel`
(`binPow_eq`).  Structural on `fuel`, so it reduces in the kernel. -/
def binPow {α : Type u} [Mul α] : Nat → α → α → Nat → α
  | 0, _, acc, _ => acc
  | fuel + 1, b, acc, n =>
    if n = 0 then acc else binPow fuel (b * b) (if n % 2 = 1 then acc * b else acc) (n / 2)

theorem pow_two_mul {α : Type u} [CommRing α] (b : α) : ∀ m : Nat, b ^ (2 * m) = (b * b) ^ m
  | 0 => by rw [Nat.mul_zero, Semiring.pow_zero, Semiring.pow_zero]
  | m + 1 => by
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, Semiring.pow_succ, Semiring.pow_succ,
      Semiring.pow_succ, pow_two_mul b m, Semiring.mul_assoc]

theorem binPow_eq {α : Type u} [CommRing α] : ∀ (fuel : Nat) (b acc : α) (n : Nat), n ≤ fuel →
    binPow fuel b acc n = acc * b ^ n
  | 0, b, acc, n, h => by
    have : n = 0 := by omega
    subst this; rw [binPow, Semiring.pow_zero, Semiring.mul_one]
  | fuel + 1, b, acc, n, h => by
    rw [binPow]
    split
    · next hn => subst hn; rw [Semiring.pow_zero, Semiring.mul_one]
    · rw [binPow_eq fuel _ _ _ (by omega)]
      have hn : n = 2 * (n / 2) + n % 2 := by omega
      conv => rhs; rw [hn, Semiring.pow_add, pow_two_mul]
      split
      · next h1 => rw [h1, Semiring.pow_one]; rw [Semiring.mul_assoc, CommSemiring.mul_comm b]
      · next h1 => rw [show n % 2 = 0 by omega, Semiring.pow_zero, Semiring.mul_one]

theorem map_binPow {α : Type u} {β : Type v} [Mul α] [Mul β] (f : β → α)
    (hf : ∀ a b, f (a * b) = f a * f b) : ∀ (fuel : Nat) (b acc : β) (n : Nat),
    f (binPow fuel b acc n) = binPow fuel (f b) (f acc) n
  | 0, _, _, _ => rfl
  | fuel + 1, b, acc, n => by
    simp only [binPow]
    split
    · rfl
    · rw [map_binPow f hf fuel, hf]
      congr 1
      split <;> simp [hf]

/-! ## Generic power lemmas -/

section Pow
variable {α : Type u}

theorem pow_mul_eq [CommRing α] (a : α) (m : Nat) : ∀ n : Nat, a ^ (m * n) = (a ^ m) ^ n
  | 0 => by rw [Nat.mul_zero, Semiring.pow_zero, Semiring.pow_zero]
  | n + 1 => by rw [Nat.mul_succ, Semiring.pow_add, pow_mul_eq a m n, Semiring.pow_succ]

theorem neg_one_pow_odd [CommRing α] (o : Nat) (h : o % 2 = 1) : (-1 : α) ^ o = -1 := by
  rw [show o = 2 * (o / 2) + 1 by omega, Semiring.pow_succ, pow_two_mul]
  have : (-1 : α) * -1 = 1 := by grind
  rw [this, Semiring.one_pow, Semiring.one_mul]

theorem exists_two_pow_mul_odd : ∀ m : Nat, 0 < m → ∃ v o, m = 2 ^ v * o ∧ o % 2 = 1
  | m, hm => by
    by_cases h : m % 2 = 1
    · exact ⟨0, m, by simp, h⟩
    · have : m / 2 < m := by omega
      obtain ⟨v, o, hv, ho⟩ := exists_two_pow_mul_odd (m / 2) (by omega)
      exact ⟨v + 1, o, by rw [Nat.pow_succ, Nat.mul_comm (2 ^ v) 2, Nat.mul_assoc]; omega, ho⟩

/-- An element with `g^(2^(k-1)) = -1 ≠ 1` has no power `g^m = 1` with `0 < m < 2^k`. -/
theorem pow_ne_one_of_half [CommRing α] (hne : (-1 : α) ≠ 1) (g : α) (k : Nat)
    (hg : g ^ (2 ^ (k - 1)) = -1) (m : Nat) (hm0 : 0 < m) (hm : m < 2 ^ k) : g ^ m ≠ 1 := by
  intro h1
  obtain ⟨v, o, rfl, ho⟩ := exists_two_pow_mul_odd m hm0
  have hvk : v < k := by
    refine Classical.byContradiction fun hv => ?_
    have : 2 ^ k ≤ 2 ^ v := Nat.pow_le_pow_right (by decide) (by omega)
    have : 2 ^ v ≤ 2 ^ v * o := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have e : 2 ^ v * o * 2 ^ (k - 1 - v) = 2 ^ (k - 1) * o := by
    rw [Nat.mul_comm (2 ^ v) o, Nat.mul_assoc, ← Nat.pow_add, show v + (k - 1 - v) = k - 1 by omega,
      Nat.mul_comm]
  have h2 : g ^ (2 ^ v * o * 2 ^ (k - 1 - v)) = 1 := by
    rw [pow_mul_eq, h1, Semiring.one_pow]
  rw [e, pow_mul_eq, hg, neg_one_pow_odd o ho] at h2
  exact hne h2

/-- Powers below the order are distinct (fields). -/
theorem pow_inj_of_half [Field α] (g : α) (k : Nat)
    (hg : 1 ≤ k → g ^ (2 ^ (k - 1)) = -1) (hne : (-1 : α) ≠ 1)
    {i j : Nat} (hi : i < 2 ^ k) (hj : j < 2 ^ k) (h : g ^ i = g ^ j) : i = j := by
  have key : ∀ i j, i < j → j < 2 ^ k → g ^ i ≠ g ^ j := by
    intro i j hij hj' heq
    have hk : 1 ≤ k := by
      refine Classical.byContradiction fun hk => ?_
      have : k = 0 := by omega
      subst this; simp at hj'; omega
    have hg0 : g ≠ 0 := by
      intro h0; have := hg hk
      obtain ⟨n, hn⟩ : ∃ n, 2 ^ (k - 1) = n + 1 := ⟨2 ^ (k - 1) - 1, by
        have := Nat.pow_pos (n := k - 1) (show 0 < 2 by decide); omega⟩
      rw [hn, h0, Semiring.pow_succ, Semiring.mul_zero] at this
      exact hne (by grind)
    have hgi : g ^ i ≠ 0 := fun h0 => hg0 (Field.of_pow_eq_zero g i h0)
    have e : g ^ j = g ^ i * g ^ (j - i) := by rw [← Semiring.pow_add]; congr 1; omega
    rw [e] at heq
    have h1 : g ^ (j - i) = 1 := by
      have := congrArg (fun x => (g ^ i)⁻¹ * x) heq
      rwa [← Semiring.mul_assoc, Field.inv_mul_cancel hgi, Semiring.one_mul,
        eq_comm] at this
    exact pow_ne_one_of_half hne g k (hg hk) (j - i) (by omega) (by omega) h1
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · exact absurd h (key i j hij hj)
  · exact hij
  · exact absurd h.symm (key j i hij hi)

end Pow

end ZkFormal.Algebra
