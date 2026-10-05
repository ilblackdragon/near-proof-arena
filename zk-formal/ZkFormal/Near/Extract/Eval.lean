import ZkFormal.Near.Extract.Common
import ZkFormal.Near.Tables.Dsl
import ZkFormal.Algebra.Fp

/-!
# ZkFormal.Near.Extract.Eval — evaluating NEAR table expressions on a trace

Toolkit for the table-view extractions:

* `Dsl` constructs evaluate to field expressions (`eval_c`, `eval_n`, `eval_sub`, …,
  all `@[simp]`);
* field facts over `Fp`: `mul_eq_zero'`, `sub_eq_zero'`, `bool_cases`;
* `Fp` values as naturals: `cv`, `ofNat` injectivity below `P`, and
  `eq_of_lin` (a linear equation between small naturals that holds in `Fp`
  holds in `ℕ`).
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

section Eval
variable (tr : Trace Fp) (t r : Nat) (pub : List Fp)

@[simp] theorem eval_c (x : Nat) : (c x).eval tr t r pub = tr.cell t r x := rfl
@[simp] theorem eval_n (x : Nat) :
    (n x).eval tr t r pub = tr.cell t ((r + 1) % tr.height t) x := rfl
@[simp] theorem eval_k (v : Nat) : (k v).eval tr t r pub = (v : Fp) := rfl
@[simp] theorem eval_add (a b : Expr) :
    (Expr.add a b).eval tr t r pub = a.eval tr t r pub + b.eval tr t r pub := rfl
@[simp] theorem eval_mul (a b : Expr) :
    (Expr.mul a b).eval tr t r pub = a.eval tr t r pub * b.eval tr t r pub := rfl
@[simp] theorem eval_neg (a : Expr) : (Expr.neg a).eval tr t r pub = -a.eval tr t r pub := rfl
@[simp] theorem eval_sub (a b : Expr) :
    (sub a b).eval tr t r pub = a.eval tr t r pub - b.eval tr t r pub := by
  simp [sub, Lean.Grind.Ring.sub_eq_add_neg]
@[simp] theorem eval_not (a : Expr) : (Dsl.not a).eval tr t r pub = 1 - a.eval tr t r pub := by
  simp [Dsl.not]; rfl
@[simp] theorem eval_mul3 (a b d : Expr) :
    (mul3 a b d).eval tr t r pub = a.eval tr t r pub * b.eval tr t r pub * d.eval tr t r pub := rfl
@[simp] theorem eval_bool (a : Expr) :
    (Dsl.bool a).eval tr t r pub = a.eval tr t r pub * (a.eval tr t r pub - 1) := by
  simp [Dsl.bool]; rfl
@[simp] theorem eval_eqG (g a b : Expr) :
    (eqG g a b).eval tr t r pub = g.eval tr t r pub * (a.eval tr t r pub - b.eval tr t r pub) := by
  simp [eqG]
@[simp] theorem eval_smul (v : Nat) (a : Expr) :
    (smul v a).eval tr t r pub = (v : Fp) * a.eval tr t r pub := rfl
@[simp] theorem eval_pub (i : Nat) : (Expr.pub i).eval tr t r pub = pub.getD i 0 := rfl
@[simp] theorem eval_isFirst :
    Expr.isFirst.eval tr t r pub = if r = 0 then 1 else 0 := rfl
@[simp] theorem eval_isLast :
    Expr.isLast.eval tr t r pub = if r + 1 = tr.height t then 1 else 0 := rfl
@[simp] theorem eval_isTransition :
    Expr.isTransition.eval tr t r pub = if r + 1 = tr.height t then 0 else 1 := rfl
@[simp] theorem eval_sum_nil : (sum []).eval tr t r pub = 0 := rfl
@[simp] theorem eval_sum_cons (e : Expr) (es : List Expr) :
    (sum (e :: es)).eval tr t r pub = e.eval tr t r pub + (sum es).eval tr t r pub := rfl
@[simp] theorem eval_mid (kind : Nat) (idx : Expr) :
    (mid kind idx).eval tr t r pub = (kind : Fp) + (16 : Nat) * idx.eval tr t r pub := rfl

end Eval

/-! ## Field facts -/

theorem mul_eq_zero' {a b : Fp} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · exact Lean.Grind.Field.of_mul_eq_zero
  · rintro (rfl | rfl) <;> grind

theorem sub_eq_zero' {a b : Fp} : a - b = 0 ↔ a = b := by
  constructor
  · intro h; grind
  · rintro rfl; grind

theorem bool_cases {a : Fp} (h : a * (a - 1) = 0) : a = 0 ∨ a = 1 := by
  rcases mul_eq_zero'.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero'.mp h)

/-! ## Naturals -/

/-- Cell value as a natural `< P`. -/
def cv (tr : Trace Fp) (t r x : Nat) : Nat := (tr.cell t r x).toNat

theorem cv_lt (tr : Trace Fp) (t r x : Nat) : cv tr t r x < P := Fp.toNat_lt _

theorem ofNat_cv (tr : Trace Fp) (t r x : Nat) : Fp.ofNat (cv tr t r x) = tr.cell t r x :=
  Fp.ofNat_toNat _

theorem natCast_eq (n : Nat) : (n : Fp) = Fp.ofNat n := rfl

theorem toNat_natCast (n : Nat) : (n : Fp).toNat = n % P := Fp.toNat_ofNat n

/-- Two naturals below `P` with equal images in `Fp` are equal. -/
theorem ofNat_inj {a b : Nat} (ha : a < P) (hb : b < P) (h : (a : Fp) = (b : Fp)) : a = b := by
  have := congrArg Fp.toNat h
  rwa [toNat_natCast, toNat_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- Map naturals into `Fp`: addition and multiplication commute with the cast. -/
theorem natCast_add (a b : Nat) : ((a + b : Nat) : Fp) = (a : Fp) + (b : Fp) := by
  apply Fp.ext; simp [natCast_eq, Fp.add_def]
theorem natCast_mul (a b : Nat) : ((a * b : Nat) : Fp) = (a : Fp) * (b : Fp) := by
  apply Fp.ext; simp [natCast_eq, Fp.mul_def, Nat.mul_mod]

theorem cell_eq_cast (tr : Trace Fp) (t r x : Nat) : tr.cell t r x = (cv tr t r x : Fp) :=
  (ofNat_cv tr t r x).symm

/-- **Linear equations of small naturals.** If `a + b·… ` style sums `L` and `R`
(as naturals) are `< P` and equal in `Fp`, they are equal. -/
theorem eq_of_cast {L R : Nat} (hL : L < P) (hR : R < P) (h : (L : Fp) = (R : Fp)) : L = R :=
  ofNat_inj hL hR h

end ZkFormal.Near
