import ZkFormal.Algebra.Fp
import ZkFormal.Algebra.QuadExt

/-!
# ZkFormal.Algebra.Fp8 — the degree-8 extension `K = F_p[x]/(x^8 − 11)`

`K` is Plonky3's `BinomialExtensionField<BabyBear, 8>` (`W = 11`).

* **Executable representation** `Fp8`: eight `Fp` coefficients
  `c0 + c1·x + … + c7·x^7`, schoolbook multiplication reduced by
  `x^8 = 11`.  This is what the compiled verifier uses.
* **Specification tower** `Fp8T = Fp4[x]/(x² − z)`, `Fp4 = Fp2[z]/(z² − y)`,
  `Fp2 = Fp[y]/(y² − 11)` (DESIGN.md R5), a field by `QuadExt.field` at each
  level: `11` is a non-square in `F_p` (Euler), and non-squareness of the
  generator propagates because `-1` is a square.
* **Refinement** `toT : Fp8 → Fp8T` (`x^k ↦ x^{k₀} z^{k₁} y^{k₂}` for
  `k = k₀ + 2k₁ + 4k₂`) is a bijective ring map (`toT_mul`, …); the ring
  structure of `Fp8` is transported along it and the inverse is computed
  through the tower.  Hence `instance : Lean.Grind.Field Fp8`.
* Enumeration `Fp8.all` with `mem_all`, `nodup_all`, `length_all`
  (`|K| = p^8`).
-/

namespace ZkFormal.Algebra

open Lean.Grind

/-! ## Product enumerations -/

/-- All length-`n` lists over `l`. -/
def vecs {α : Type} (l : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => l.flatMap fun a => (vecs l n).map (a :: ·)

theorem mem_vecs {α : Type} {l : List α} : ∀ {n : Nat} {v : List α},
    v.length = n → (∀ x ∈ v, x ∈ l) → v ∈ vecs l n
  | 0, v, h, _ => by simp_all [vecs]
  | n + 1, [], h, _ => by simp at h
  | n + 1, a :: v, h, hv => by
    simp only [vecs, List.mem_flatMap, List.mem_map]
    exact ⟨a, hv a (by simp), v, mem_vecs (by simpa using h) (fun x hx => hv x (by simp [hx])), rfl⟩

theorem length_of_mem_vecs {α : Type} {l : List α} : ∀ {n : Nat} {v : List α},
    v ∈ vecs l n → v.length = n
  | 0, v, h => by simp [vecs] at h; simp [h]
  | n + 1, v, h => by
    simp only [vecs, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a, _, w, hw, rfl⟩ := h
    simp [length_of_mem_vecs hw]

theorem nodup_flatMap_cons {α : Type} (L : List (List α)) (hL : L.Nodup) :
    ∀ l : List α, l.Nodup → (l.flatMap fun a => L.map (a :: ·)).Nodup
  | [], _ => by simp
  | a :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨nodup_map_on (fun x _ y _ h => (List.cons.inj h).2) hL,
      nodup_flatMap_cons L hL l hl.2, ?_⟩
    intro x hx y hy hxy
    simp only [List.mem_map, List.mem_flatMap] at hx hy
    obtain ⟨u, _, rfl⟩ := hx
    obtain ⟨b, hb, w, _, rfl⟩ := hy
    exact hl.1 ((List.cons.inj hxy).1 ▸ hb)

theorem nodup_vecs {α : Type} {l : List α} (hl : l.Nodup) : ∀ n, (vecs l n).Nodup
  | 0 => by simp [vecs]
  | n + 1 => nodup_flatMap_cons _ (nodup_vecs hl n) l hl

theorem length_flatMap_cons' {α : Type} (L : List (List α)) :
    ∀ l : List α, (l.flatMap fun a => L.map (a :: ·)).length = l.length * L.length
  | [] => by simp
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, length_flatMap_cons' L l, List.length_map,
      List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem length_vecs {α : Type} (l : List α) : ∀ n, (vecs l n).length = l.length ^ n
  | 0 => rfl
  | n + 1 => by
    simp only [vecs]
    rw [length_flatMap_cons', length_vecs l n, Nat.pow_succ, Nat.mul_comm]

/-! ## The specification tower -/

/-- `F_p[y]/(y² − 11)`. -/
abbrev Fp2 := QuadExt Fp 11
instance Fp2.field : Field Fp2 := QuadExt.field Fp.eleven_nonsquare

/-- `F_{p²}[z]/(z² − y)`. -/
abbrev Fp4 := QuadExt Fp2 QuadExt.t
instance Fp4.field : Field Fp4 :=
  QuadExt.field (QuadExt.t_nonsquare Fp.sqrtNegOne Fp.sqrtNegOne_sq Fp.eleven_nonsquare)

/-- `F_{p⁴}[x]/(x² − z)`. -/
abbrev Fp8T := QuadExt Fp4 QuadExt.t
instance Fp8T.field : Field Fp8T :=
  QuadExt.field (QuadExt.t_nonsquare (QuadExt.base Fp.sqrtNegOne)
    (QuadExt.base_sq_neg_one _ Fp.sqrtNegOne_sq)
    (QuadExt.t_nonsquare Fp.sqrtNegOne Fp.sqrtNegOne_sq Fp.eleven_nonsquare))

/-! ## The executable flat representation -/

/-- `c0 + c1·x + … + c7·x^7` in `F_p[x]/(x^8 − 11)`. -/
structure Fp8 where
  c0 : Fp
  c1 : Fp
  c2 : Fp
  c3 : Fp
  c4 : Fp
  c5 : Fp
  c6 : Fp
  c7 : Fp
  deriving DecidableEq, Inhabited, Repr

namespace Fp8

/-- The binomial constant: `x^8 = W`. -/
@[inline] def W : Fp := 11

@[ext] theorem ext {a b : Fp8} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) (h2 : a.c2 = b.c2)
    (h3 : a.c3 = b.c3) (h4 : a.c4 = b.c4) (h5 : a.c5 = b.c5) (h6 : a.c6 = b.c6)
    (h7 : a.c7 = b.c7) : a = b := by
  cases a; cases b; simp_all

@[inline] def add (a b : Fp8) : Fp8 :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3, a.c4 + b.c4, a.c5 + b.c5, a.c6 + b.c6,
    a.c7 + b.c7⟩
@[inline] def sub (a b : Fp8) : Fp8 :=
  ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2, a.c3 - b.c3, a.c4 - b.c4, a.c5 - b.c5, a.c6 - b.c6,
    a.c7 - b.c7⟩
@[inline] def neg (a : Fp8) : Fp8 := ⟨-a.c0, -a.c1, -a.c2, -a.c3, -a.c4, -a.c5, -a.c6, -a.c7⟩
/-- Schoolbook product reduced by `x^8 = 11`. -/
def mul (a b : Fp8) : Fp8 :=
⟨
    a.c0 * b.c0 + W * (a.c1 * b.c7 + a.c2 * b.c6 + a.c3 * b.c5 + a.c4 * b.c4 + a.c5 * b.c3 + a.c6 * b.c2 + a.c7 * b.c1),
    a.c0 * b.c1 + a.c1 * b.c0 + W * (a.c2 * b.c7 + a.c3 * b.c6 + a.c4 * b.c5 + a.c5 * b.c4 + a.c6 * b.c3 + a.c7 * b.c2),
    a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 + W * (a.c3 * b.c7 + a.c4 * b.c6 + a.c5 * b.c5 + a.c6 * b.c4 + a.c7 * b.c3),
    a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0 + W * (a.c4 * b.c7 + a.c5 * b.c6 + a.c6 * b.c5 + a.c7 * b.c4),
    a.c0 * b.c4 + a.c1 * b.c3 + a.c2 * b.c2 + a.c3 * b.c1 + a.c4 * b.c0 + W * (a.c5 * b.c7 + a.c6 * b.c6 + a.c7 * b.c5),
    a.c0 * b.c5 + a.c1 * b.c4 + a.c2 * b.c3 + a.c3 * b.c2 + a.c4 * b.c1 + a.c5 * b.c0 + W * (a.c6 * b.c7 + a.c7 * b.c6),
    a.c0 * b.c6 + a.c1 * b.c5 + a.c2 * b.c4 + a.c3 * b.c3 + a.c4 * b.c2 + a.c5 * b.c1 + a.c6 * b.c0 + W * (a.c7 * b.c7),
    a.c0 * b.c7 + a.c1 * b.c6 + a.c2 * b.c5 + a.c3 * b.c4 + a.c4 * b.c3 + a.c5 * b.c2 + a.c6 * b.c1 + a.c7 * b.c0⟩

/-- The base-field embedding `F_p → K`. -/
@[inline] def ofBase (c : Fp) : Fp8 := ⟨c, 0, 0, 0, 0, 0, 0, 0⟩
/-- Scalar multiplication by a base-field element. -/
@[inline] def smulBase (c : Fp) (a : Fp8) : Fp8 :=
  ⟨c * a.c0, c * a.c1, c * a.c2, c * a.c3, c * a.c4, c * a.c5, c * a.c6, c * a.c7⟩

instance : Add Fp8 := ⟨add⟩
instance : Sub Fp8 := ⟨sub⟩
instance : Neg Fp8 := ⟨neg⟩
instance : Mul Fp8 := ⟨mul⟩
instance (n : Nat) : OfNat Fp8 n := ⟨ofBase (OfNat.ofNat n)⟩
instance : NatCast Fp8 := ⟨fun n => ofBase (n : Fp)⟩
instance : IntCast Fp8 := ⟨fun i => ofBase (i : Fp)⟩
instance : SMul Nat Fp8 := ⟨fun k a =>
  ⟨k • a.c0, k • a.c1, k • a.c2, k • a.c3, k • a.c4, k • a.c5, k • a.c6, k • a.c7⟩⟩
instance : SMul Int Fp8 := ⟨fun k a =>
  ⟨k • a.c0, k • a.c1, k • a.c2, k • a.c3, k • a.c4, k • a.c5, k • a.c6, k • a.c7⟩⟩
/-- Powers by square-and-multiply. -/
instance : HPow Fp8 Nat Fp8 := ⟨fun a n => binPow n a (ofBase 1) n⟩

@[simp] theorem add_c0 (a b : Fp8) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem sub_c0 (a b : Fp8) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem neg_c0 (a : Fp8) : (-a).c0 = -a.c0 := rfl
@[simp] theorem add_c1 (a b : Fp8) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem sub_c1 (a b : Fp8) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem neg_c1 (a : Fp8) : (-a).c1 = -a.c1 := rfl
@[simp] theorem add_c2 (a b : Fp8) : (a + b).c2 = a.c2 + b.c2 := rfl
@[simp] theorem sub_c2 (a b : Fp8) : (a - b).c2 = a.c2 - b.c2 := rfl
@[simp] theorem neg_c2 (a : Fp8) : (-a).c2 = -a.c2 := rfl
@[simp] theorem add_c3 (a b : Fp8) : (a + b).c3 = a.c3 + b.c3 := rfl
@[simp] theorem sub_c3 (a b : Fp8) : (a - b).c3 = a.c3 - b.c3 := rfl
@[simp] theorem neg_c3 (a : Fp8) : (-a).c3 = -a.c3 := rfl
@[simp] theorem add_c4 (a b : Fp8) : (a + b).c4 = a.c4 + b.c4 := rfl
@[simp] theorem sub_c4 (a b : Fp8) : (a - b).c4 = a.c4 - b.c4 := rfl
@[simp] theorem neg_c4 (a : Fp8) : (-a).c4 = -a.c4 := rfl
@[simp] theorem add_c5 (a b : Fp8) : (a + b).c5 = a.c5 + b.c5 := rfl
@[simp] theorem sub_c5 (a b : Fp8) : (a - b).c5 = a.c5 - b.c5 := rfl
@[simp] theorem neg_c5 (a : Fp8) : (-a).c5 = -a.c5 := rfl
@[simp] theorem add_c6 (a b : Fp8) : (a + b).c6 = a.c6 + b.c6 := rfl
@[simp] theorem sub_c6 (a b : Fp8) : (a - b).c6 = a.c6 - b.c6 := rfl
@[simp] theorem neg_c6 (a : Fp8) : (-a).c6 = -a.c6 := rfl
@[simp] theorem add_c7 (a b : Fp8) : (a + b).c7 = a.c7 + b.c7 := rfl
@[simp] theorem sub_c7 (a b : Fp8) : (a - b).c7 = a.c7 - b.c7 := rfl
@[simp] theorem neg_c7 (a : Fp8) : (-a).c7 = -a.c7 := rfl
@[simp] theorem mul_c0 (a b : Fp8) : (a * b).c0 =
    a.c0 * b.c0 + W * (a.c1 * b.c7 + a.c2 * b.c6 + a.c3 * b.c5 + a.c4 * b.c4 + a.c5 * b.c3 + a.c6 * b.c2 + a.c7 * b.c1) := rfl
@[simp] theorem mul_c1 (a b : Fp8) : (a * b).c1 =
    a.c0 * b.c1 + a.c1 * b.c0 + W * (a.c2 * b.c7 + a.c3 * b.c6 + a.c4 * b.c5 + a.c5 * b.c4 + a.c6 * b.c3 + a.c7 * b.c2) := rfl
@[simp] theorem mul_c2 (a b : Fp8) : (a * b).c2 =
    a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 + W * (a.c3 * b.c7 + a.c4 * b.c6 + a.c5 * b.c5 + a.c6 * b.c4 + a.c7 * b.c3) := rfl
@[simp] theorem mul_c3 (a b : Fp8) : (a * b).c3 =
    a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0 + W * (a.c4 * b.c7 + a.c5 * b.c6 + a.c6 * b.c5 + a.c7 * b.c4) := rfl
@[simp] theorem mul_c4 (a b : Fp8) : (a * b).c4 =
    a.c0 * b.c4 + a.c1 * b.c3 + a.c2 * b.c2 + a.c3 * b.c1 + a.c4 * b.c0 + W * (a.c5 * b.c7 + a.c6 * b.c6 + a.c7 * b.c5) := rfl
@[simp] theorem mul_c5 (a b : Fp8) : (a * b).c5 =
    a.c0 * b.c5 + a.c1 * b.c4 + a.c2 * b.c3 + a.c3 * b.c2 + a.c4 * b.c1 + a.c5 * b.c0 + W * (a.c6 * b.c7 + a.c7 * b.c6) := rfl
@[simp] theorem mul_c6 (a b : Fp8) : (a * b).c6 =
    a.c0 * b.c6 + a.c1 * b.c5 + a.c2 * b.c4 + a.c3 * b.c3 + a.c4 * b.c2 + a.c5 * b.c1 + a.c6 * b.c0 + W * (a.c7 * b.c7) := rfl
@[simp] theorem mul_c7 (a b : Fp8) : (a * b).c7 =
    a.c0 * b.c7 + a.c1 * b.c6 + a.c2 * b.c5 + a.c3 * b.c4 + a.c4 * b.c3 + a.c5 * b.c2 + a.c6 * b.c1 + a.c7 * b.c0 := rfl

/-! ## Refinement to the tower -/

/-- Flat coefficients to the tower (`x^k ↦ x^{k₀} z^{k₁} y^{k₂}`, `k = k₀ + 2k₁ + 4k₂`). -/
def toT (a : Fp8) : Fp8T := ⟨⟨⟨a.c0, a.c4⟩, ⟨a.c2, a.c6⟩⟩, ⟨⟨a.c1, a.c5⟩, ⟨a.c3, a.c7⟩⟩⟩

/-- The tower to flat coefficients. -/
def ofT (t : Fp8T) : Fp8 := ⟨t.a.a.a, t.b.a.a, t.a.b.a, t.b.b.a, t.a.a.b, t.b.a.b, t.a.b.b, t.b.b.b⟩

@[simp] theorem ofT_toT (a : Fp8) : ofT (toT a) = a := rfl
@[simp] theorem toT_ofT (t : Fp8T) : toT (ofT t) = t := rfl

theorem toT_inj (a b : Fp8) (h : toT a = toT b) : a = b := by
  rw [← ofT_toT a, h, ofT_toT]

theorem toT_mul (a b : Fp8) : toT (a * b) = toT a * toT b := by
  simp only [toT]
  apply QuadExt.ext <;> apply QuadExt.ext <;> apply QuadExt.ext <;> simp [W] <;> grind


attribute [local instance] Semiring.natCast Ring.intCast

theorem toT_ofBase (c : Fp) : toT (ofBase c) = ⟨⟨⟨c, 0⟩, 0⟩, 0⟩ := rfl

/-- `toT` preserves every ring operation. -/
def towerEmbedding : Embedding Fp8 Fp8T where
  f := toT
  inj := toT_inj
  map_add _ _ := rfl
  map_mul := toT_mul
  map_neg _ := rfl
  map_sub _ _ := rfl
  map_ofNat _ := rfl
  map_natCast _ := rfl
  map_intCast _ := rfl
  map_nsmul _ _ := rfl
  map_zsmul _ _ := rfl
  map_pow a n := by
    show toT (binPow n a (ofBase 1) n) = _
    rw [map_binPow toT toT_mul, binPow_eq _ _ _ _ (Nat.le_refl _)]
    show (1 : Fp8T) * _ = _
    rw [Semiring.one_mul]

instance commRing : CommRing Fp8 := CommRing.ofEmbedding towerEmbedding

/-- Inverse, computed in the tower (`0⁻¹ = 0`). -/
instance : Inv Fp8 := ⟨fun a => ofT (toT a)⁻¹⟩

theorem toT_inv (a : Fp8) : toT a⁻¹ = (toT a)⁻¹ := rfl
theorem toT_one : toT 1 = 1 := rfl
theorem toT_zero : toT 0 = 0 := rfl

theorem toT_eq_zero {a : Fp8} : toT a = 0 ↔ a = 0 :=
  ⟨fun h => toT_inj _ _ h, fun h => h ▸ rfl⟩

instance field : Field Fp8 :=
  Field.ofInv (by decide +kernel)
    (toT_inj _ _ (by rw [toT_inv, toT_zero, Field.inv_zero]))
    (fun {a} ha => toT_inj _ _ (by
      rw [toT_mul, toT_inv, toT_one]
      exact Field.mul_inv_cancel (fun h => ha (toT_eq_zero.mp h))))

theorem ofBase_ofNat (n : Nat) : ofBase (OfNat.ofNat n) = (OfNat.ofNat n : Fp8) := rfl

instance : IsCharP Fp8 P := IsCharP.mk' _ _ (ofNat_eq_zero_iff := fun x => by
  constructor
  · intro h
    have := congrArg Fp8.c0 h
    exact (IsCharP.ofNat_eq_zero_iff P x).mp this
  · intro h
    have : (OfNat.ofNat x : Fp) = 0 := (IsCharP.ofNat_eq_zero_iff P x).mpr h
    show ofBase _ = ofBase _
    rw [this])

/-! ## Base field -/

theorem ofBase_add (a b : Fp) : ofBase (a + b) = ofBase a + ofBase b := by
  ext <;> simp [ofBase] <;> grind
theorem ofBase_mul (a b : Fp) : ofBase (a * b) = ofBase a * ofBase b := by
  ext <;> simp [ofBase, W] <;> grind
theorem ofBase_neg (a : Fp) : ofBase (-a) = -ofBase a := by
  ext <;> simp [ofBase] <;> grind
theorem ofBase_sub (a b : Fp) : ofBase (a - b) = ofBase a - ofBase b := by
  ext <;> simp [ofBase] <;> grind
theorem smulBase_eq (c : Fp) (a : Fp8) : smulBase c a = ofBase c * a := by
  ext <;> simp [smulBase, ofBase, W] <;> grind

theorem ofBase_inj {a b : Fp} (h : ofBase a = ofBase b) : a = b := congrArg Fp8.c0 h

/-- `a` lies in the base field `F_p`. -/
def IsBase (a : Fp8) : Prop :=
  a.c1 = 0 ∧ a.c2 = 0 ∧ a.c3 = 0 ∧ a.c4 = 0 ∧ a.c5 = 0 ∧ a.c6 = 0 ∧ a.c7 = 0

instance (a : Fp8) : Decidable (IsBase a) := by unfold IsBase; infer_instance

theorem isBase_iff (a : Fp8) : IsBase a ↔ ∃ c, a = ofBase c := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨a.c0, by ext <;> simp [ofBase, *]⟩
  · rintro ⟨c, rfl⟩; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Coefficients -/

/-- Coefficient of `x^i` (`0` for `i ≥ 8`). -/
def coeff (a : Fp8) : Nat → Fp
  | 0 => a.c0 | 1 => a.c1 | 2 => a.c2 | 3 => a.c3
  | 4 => a.c4 | 5 => a.c5 | 6 => a.c6 | 7 => a.c7
  | _ => 0

/-- From coefficients `f 0, …, f 7`. -/
def ofCoeffs (f : Nat → Fp) : Fp8 := ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7⟩

theorem coeff_ofCoeffs (f : Nat → Fp) (i : Nat) (hi : i < 8) : coeff (ofCoeffs f) i = f i := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

theorem ofCoeffs_coeff (a : Fp8) : ofCoeffs (coeff a) = a := rfl

theorem ext_coeff {a b : Fp8} (h : ∀ i, i < 8 → coeff a i = coeff b i) : a = b := by
  rw [← ofCoeffs_coeff a, ← ofCoeffs_coeff b]
  ext
  · exact h 0 (by decide)
  · exact h 1 (by decide)
  · exact h 2 (by decide)
  · exact h 3 (by decide)
  · exact h 4 (by decide)
  · exact h 5 (by decide)
  · exact h 6 (by decide)
  · exact h 7 (by decide)

/-! ## Enumeration of `K` -/

/-- Coefficient list `[c0, …, c7]`. -/
def toList (a : Fp8) : List Fp := [a.c0, a.c1, a.c2, a.c3, a.c4, a.c5, a.c6, a.c7]

/-- From a coefficient list (missing entries are `0`). -/
def ofList (l : List Fp) : Fp8 :=
  ⟨l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0, l.getD 5 0, l.getD 6 0,
    l.getD 7 0⟩

theorem ofList_toList (a : Fp8) : ofList (toList a) = a := rfl

theorem toList_ofList {l : List Fp} (h : l.length = 8) : toList (ofList l) = l := by
  match l, h with
  | [_, _, _, _, _, _, _, _], _ => rfl

/-- All `p^8` elements of `K` (never evaluated; used for counting). -/
def all : List Fp8 := (vecs Fp.all 8).map ofList

theorem mem_all (a : Fp8) : a ∈ all :=
  List.mem_map.mpr ⟨toList a, mem_vecs rfl (fun x _ => Fp.mem_all x), ofList_toList a⟩

theorem nodup_all : all.Nodup :=
  nodup_map_on (fun x hx y hy h => by
    rw [← toList_ofList (length_of_mem_vecs hx), ← toList_ofList (length_of_mem_vecs hy), h])
    (nodup_vecs Fp.nodup_all 8)

theorem length_all : all.length = P ^ 8 := by
  rw [all, List.length_map, length_vecs, Fp.length_all]

end Fp8
end ZkFormal.Algebra
