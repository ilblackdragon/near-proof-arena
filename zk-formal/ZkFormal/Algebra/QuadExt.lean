import ZkFormal.Algebra.Transport

/-!
# ZkFormal.Algebra.QuadExt — quadratic extensions `K[t]/(t² − r)`

For a field `K` and a non-square `r`, `QuadExt K r` is a field
(`QuadExt.field`): `(a + b·t)⁻¹ = (a − b·t)/(a² − r·b²)` and the norm
`a² − r·b²` vanishes only at `0`.  If moreover `-1` is a square in `K`, the
generator `t` is a non-square in `QuadExt K r` (`QuadExt.t_nonsquare`), so
the construction iterates: this is the tower behind `Fp8` (DESIGN.md R5).
This is the *specification* tower; the executable `Fp8` is flat.
-/

namespace ZkFormal.Algebra

open Lean.Grind

/-- `a + b·t` with `t² = r`. -/
@[ext] structure QuadExt (K : Type) (r : K) where
  a : K
  b : K
  deriving DecidableEq

namespace QuadExt

variable {K : Type} [CommRing K] {r : K}

attribute [local instance] Semiring.natCast Ring.intCast

instance : Add (QuadExt K r) := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Mul (QuadExt K r) := ⟨fun x y => ⟨x.a * y.a + r * (x.b * y.b), x.a * y.b + x.b * y.a⟩⟩
instance : Neg (QuadExt K r) := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub (QuadExt K r) := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩
instance (n : Nat) : OfNat (QuadExt K r) n := ⟨⟨OfNat.ofNat n, 0⟩⟩
instance : NatCast (QuadExt K r) := ⟨fun n => ⟨(n : K), 0⟩⟩
instance : IntCast (QuadExt K r) := ⟨fun i => ⟨(i : K), 0⟩⟩
instance : SMul Nat (QuadExt K r) := ⟨fun k x => ⟨k • x.a, k • x.b⟩⟩
instance : SMul Int (QuadExt K r) := ⟨fun k x => ⟨k • x.a, k • x.b⟩⟩
instance : HPow (QuadExt K r) Nat (QuadExt K r) := ⟨fun x n => npowRec n x⟩

@[simp] theorem add_a (x y : QuadExt K r) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : QuadExt K r) : (x + y).b = x.b + y.b := rfl
@[simp] theorem mul_a (x y : QuadExt K r) : (x * y).a = x.a * y.a + r * (x.b * y.b) := rfl
@[simp] theorem mul_b (x y : QuadExt K r) : (x * y).b = x.a * y.b + x.b * y.a := rfl
@[simp] theorem neg_a (x : QuadExt K r) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : QuadExt K r) : (-x).b = -x.b := rfl
@[simp] theorem sub_a (x y : QuadExt K r) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b (x y : QuadExt K r) : (x - y).b = x.b - y.b := rfl
@[simp] theorem ofNat_a (n : Nat) : (no_index (OfNat.ofNat n) : QuadExt K r).a = OfNat.ofNat n := rfl
@[simp] theorem ofNat_b (n : Nat) : (no_index (OfNat.ofNat n) : QuadExt K r).b = 0 := rfl
@[simp] theorem natCast_a (n : Nat) : (n : QuadExt K r).a = (n : K) := rfl
@[simp] theorem natCast_b (n : Nat) : (n : QuadExt K r).b = 0 := rfl
@[simp] theorem intCast_a (i : Int) : (i : QuadExt K r).a = (i : K) := rfl
@[simp] theorem intCast_b (i : Int) : (i : QuadExt K r).b = 0 := rfl
@[simp] theorem nsmul_a (k : Nat) (x : QuadExt K r) : (k • x).a = k • x.a := rfl
@[simp] theorem nsmul_b (k : Nat) (x : QuadExt K r) : (k • x).b = k • x.b := rfl
@[simp] theorem zsmul_a (k : Int) (x : QuadExt K r) : (k • x).a = k • x.a := rfl
@[simp] theorem zsmul_b (k : Int) (x : QuadExt K r) : (k • x).b = k • x.b := rfl

protected theorem add_zero' (x : QuadExt K r) : x + 0 = x := by
  ext <;> simp <;> grind

protected theorem add_comm' (x y : QuadExt K r) : x + y = y + x := by
  ext <;> simp <;> grind

protected theorem add_assoc' (x y z : QuadExt K r) : x + y + z = x + (y + z) := by
  ext <;> simp <;> grind

protected theorem mul_assoc' (x y z : QuadExt K r) : x * y * z = x * (y * z) := by
  ext <;> simp <;> grind

protected theorem mul_one' (x : QuadExt K r) : x * 1 = x := by
  ext <;> simp <;> grind

protected theorem one_mul' (x : QuadExt K r) : 1 * x = x := by
  ext <;> simp <;> grind

protected theorem left_distrib' (x y z : QuadExt K r) : x * (y + z) = x * y + x * z := by
  ext <;> simp <;> grind

protected theorem right_distrib' (x y z : QuadExt K r) : (x + y) * z = x * z + y * z := by
  ext <;> simp <;> grind

protected theorem zero_mul' (x : QuadExt K r) : 0 * x = 0 := by
  ext <;> simp <;> grind

protected theorem mul_zero' (x : QuadExt K r) : x * 0 = 0 := by
  ext <;> simp <;> grind

protected theorem ofNat_succ' (n : Nat) : (OfNat.ofNat (n + 1) : QuadExt K r) = OfNat.ofNat n + 1 := by
  ext
  · exact Semiring.ofNat_succ n
  · simp [Semiring.add_zero]

protected theorem ofNat_eq_natCast' (n : Nat) : (OfNat.ofNat n : QuadExt K r) = ((n : Nat) : QuadExt K r) := by
  ext
  · exact Semiring.ofNat_eq_natCast n
  · rfl

protected theorem nsmul_eq_natCast_mul' (n : Nat) (x : QuadExt K r) : n • x = ((n : Nat) : QuadExt K r) * x := by
  ext
  · simp [Semiring.nsmul_eq_natCast_mul, Semiring.zero_mul, Semiring.mul_zero, Semiring.add_zero]
  · simp [Semiring.nsmul_eq_natCast_mul, Semiring.zero_mul, Semiring.add_zero]

protected theorem neg_add_cancel' (x : QuadExt K r) : -x + x = 0 := by
  ext <;> simp <;> grind

protected theorem sub_eq_add_neg' (x y : QuadExt K r) : x - y = x + -y := by
  ext <;> simp <;> grind

protected theorem neg_zsmul' (i : Int) (x : QuadExt K r) : (-i) • x = -(i • x) := by
  ext
  · exact Ring.neg_zsmul i x.a
  · exact Ring.neg_zsmul i x.b

protected theorem zsmul_natCast_eq_nsmul' (n : Nat) (x : QuadExt K r) : ((n : Int)) • x = n • x := by
  ext
  · exact Ring.zsmul_natCast_eq_nsmul n x.a
  · exact Ring.zsmul_natCast_eq_nsmul n x.b

protected theorem intCast_ofNat' (n : Nat) : ((OfNat.ofNat n : Int) : QuadExt K r) = OfNat.ofNat n := by
  ext
  · exact Ring.intCast_ofNat n
  · rfl

protected theorem intCast_neg' (i : Int) : ((-i : Int) : QuadExt K r) = -((i : Int) : QuadExt K r) := by
  ext
  · exact Ring.intCast_neg i
  · simp; grind

protected theorem mul_comm' (x y : QuadExt K r) : x * y = y * x := by
  ext <;> simp <;> grind

instance commRing : CommRing (QuadExt K r) where
  add_zero := QuadExt.add_zero'
  add_comm := QuadExt.add_comm'
  add_assoc := QuadExt.add_assoc'
  mul_assoc := QuadExt.mul_assoc'
  mul_one := QuadExt.mul_one'
  one_mul := QuadExt.one_mul'
  left_distrib := QuadExt.left_distrib'
  right_distrib := QuadExt.right_distrib'
  zero_mul := QuadExt.zero_mul'
  mul_zero := QuadExt.mul_zero'
  ofNat_succ := QuadExt.ofNat_succ'
  ofNat_eq_natCast := QuadExt.ofNat_eq_natCast'
  nsmul_eq_natCast_mul := QuadExt.nsmul_eq_natCast_mul'
  neg_add_cancel := QuadExt.neg_add_cancel'
  sub_eq_add_neg := QuadExt.sub_eq_add_neg'
  neg_zsmul := QuadExt.neg_zsmul'
  zsmul_natCast_eq_nsmul := QuadExt.zsmul_natCast_eq_nsmul'
  intCast_ofNat := QuadExt.intCast_ofNat'
  intCast_neg := QuadExt.intCast_neg'
  mul_comm := QuadExt.mul_comm'
  pow_zero _ := rfl
  pow_succ _ _ := rfl

/-! ## The field structure -/

section Field
variable {K : Type} [Field K] {r : K}

/-- The norm `a² − r·b²`. -/
def norm (x : QuadExt K r) : K := x.a * x.a - r * (x.b * x.b)

instance : Inv (QuadExt K r) := ⟨fun x => ⟨x.a * (norm x)⁻¹, -(x.b * (norm x)⁻¹)⟩⟩

@[simp] theorem inv_a (x : QuadExt K r) : x⁻¹.a = x.a * (norm x)⁻¹ := rfl
@[simp] theorem inv_b (x : QuadExt K r) : x⁻¹.b = -(x.b * (norm x)⁻¹) := rfl

theorem eq_zero_iff (x : QuadExt K r) : x = 0 ↔ x.a = 0 ∧ x.b = 0 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; ext <;> simp [h1, h2]

theorem norm_ne_zero (hr : ∀ y : K, y * y ≠ r) {x : QuadExt K r} (hx : x ≠ 0) : norm x ≠ 0 := by
  intro hn
  simp only [norm] at hn
  by_cases hb : x.b = 0
  · have ha : x.a ≠ 0 := fun ha => hx ((eq_zero_iff x).mpr ⟨ha, hb⟩)
    rw [hb] at hn
    have : x.a * x.a = 0 := by grind
    rcases Field.of_mul_eq_zero this with h | h <;> exact ha h
  · apply hr (x.a * x.b⁻¹)
    have hbb := Field.mul_inv_cancel hb
    grind

theorem mul_inv_cancel' (hr : ∀ y : K, y * y ≠ r) {x : QuadExt K r} (hx : x ≠ 0) :
    x * x⁻¹ = 1 := by
  have hn := Field.mul_inv_cancel (norm_ne_zero hr hx)
  simp only [norm] at hn
  ext <;> simp [norm] <;> grind

theorem zero_ne_one' : (0 : QuadExt K r) ≠ 1 := by
  intro h
  have := congrArg QuadExt.a h
  exact Field.zero_ne_one this

theorem inv_zero' : (0 : QuadExt K r)⁻¹ = 0 := by
  ext <;> simp <;> grind

/-- `K[t]/(t² − r)` is a field when `r` is a non-square. -/
@[reducible] def field (hr : ∀ y : K, y * y ≠ r) : Field (QuadExt K r) :=
  Field.ofInv zero_ne_one' inv_zero' (mul_inv_cancel' hr)

/-- The generator `t`. -/
def t : QuadExt K r := ⟨0, 1⟩

@[simp] theorem t_a : (t : QuadExt K r).a = 0 := rfl
@[simp] theorem t_b : (t : QuadExt K r).b = 1 := rfl

/-- The base field embedding. -/
def base (c : K) : QuadExt K r := ⟨c, 0⟩

/-- If `-1 = i²` in `K` and `r` is a non-square, then `t` is a non-square in
`K[t]/(t² − r)`. -/
theorem t_nonsquare (i : K) (hi : i * i = -1) (hr : ∀ y : K, y * y ≠ r) :
    ∀ x : QuadExt K r, x * x ≠ t := by
  intro x hx
  have h1 := congrArg QuadExt.a hx
  have h2 := congrArg QuadExt.b hx
  simp [t] at h1 h2
  -- `x.a² + r·x.b² = 0`, `2·x.a·x.b = 1`
  have hb : x.b ≠ 0 := by
    intro hb; rw [hb] at h2
    exact Field.zero_ne_one (α := K) (by grind)
  apply hr (i * x.a * x.b⁻¹)
  have hbb := Field.mul_inv_cancel hb
  grind

/-- `i ∈ K` stays a square root of `-1` in the extension. -/
theorem base_sq_neg_one (i : K) (hi : i * i = -1) :
    (base i : QuadExt K r) * base i = -1 := by
  ext <;> simp [base] <;> grind

end Field

end QuadExt
end ZkFormal.Algebra
