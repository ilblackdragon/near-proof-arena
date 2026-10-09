import ZkFormal.Chacha.ZEval
import ZkFormal.NearV3.Sched.Gen.Common

/-!
# ZkFormal.NearV3.Sched.Complete.Field — constraints that vanish only mod `P` (M4)

`mem_complete` / `cmp_complete` evaluate constraints as integers (`eval_zero_of`). Tables with
inverse / zero-test columns (`sprV3`: `ikc`, `iK`, `irem`, `ia`; the generators write
`finv x`, the inverse of `x mod P`, `0 ↦ 0`) only vanish mod `P`:

* `eval_zero_of_dvd`: `P ∣ zev e` (as an integer) gives a vanishing constraint;
* `finv_mul`: `x · finv x ≡ 1 (mod P)` for `x ≢ 0`; `finv_zero`, `finv_lt`.
-/

namespace ZkFormal.NearV3.Sched.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched.Gen

theorem eval_zero_of_dvd {tr : Trace Fp} {t r : Nat} {pub : List Fp} {e : Expr}
    (h : (2013265921 : Int) ∣ zev (tenv tr t r pub) e) : e.eval tr t r pub = 0 := by
  rw [eval_eq]
  exact (Lean.Grind.IsCharP.intCast_eq_zero_iff (α := Fp) P _).mpr (by rw [P_val]; exact Int.emod_eq_zero_of_dvd h)

theorem fp_toNat_mul (a b : Fp) : (a * b).toNat = a.toNat * b.toNat % P := by
  have := congrArg Fin.val (Fp.toFin_mul a b)
  simpa [Fp.toFin, Fin.val_mul] using this

theorem finv_lt (x : Nat) : finv x < P := by
  unfold finv
  split
  · decide
  · exact Fp.toNat_lt _

theorem finv_zero {x : Nat} (hx : x % P = 0) : finv x = 0 := by
  unfold finv; rw [if_pos hx]

theorem finv_mul {x : Nat} (hx : x % P ≠ 0) : x * finv x % P = 1 := by
  unfold finv
  rw [if_neg hx]
  have hne : Fp.ofNat x ≠ 0 := by
    intro h
    rw [Fp.eq_zero_iff, Fp.toNat_ofNat] at h
    exact hx h
  have h1 := congrArg Fp.toNat (Fp.mul_inv_cancel hne)
  rw [fp_toNat_mul, Fp.toNat_ofNat, Fp.toNat_one] at h1
  rw [Nat.mul_mod, Nat.mod_eq_of_lt (Fp.toNat_lt ((Fp.ofNat x)⁻¹))]
  exact h1

end ZkFormal.NearV3.Sched.Complete
