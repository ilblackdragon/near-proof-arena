import ZkFormal.Air.Basic
import ZkFormal.Algebra.Fp

/-!
# ZkFormal.Sha.Eval — evaluation of AIR expressions over BabyBear, on `Nat`

The only facts about `ZkFormal.Air.Expr.eval` (lane L4) and
`ZkFormal.Algebra.Fp` (lane L1) that the SHA-256 table proofs use.
-/

namespace ZkFormal.Sha

open ZkFormal.Air ZkFormal.Algebra


namespace Ev
variable (tr : Trace Fp) (t r : Nat) (pub : List Fp)

@[simp] theorem eval_const (c : Nat) : (Expr.const c).eval tr t r pub = Fp.ofNat c := rfl
@[simp] theorem eval_col (c : Nat) : (Expr.col c false).eval tr t r pub = tr.cell t r c := rfl
@[simp] theorem eval_colNext (c : Nat) :
    (Expr.col c true).eval tr t r pub = tr.cell t ((r + 1) % tr.height t) c := rfl
@[simp] theorem eval_add (a b : Expr) :
    (Expr.add a b).eval tr t r pub = Fp.add (a.eval tr t r pub) (b.eval tr t r pub) := rfl
@[simp] theorem eval_mul (a b : Expr) :
    (Expr.mul a b).eval tr t r pub = Fp.mul (a.eval tr t r pub) (b.eval tr t r pub) := rfl
@[simp] theorem eval_neg (a : Expr) :
    (Expr.neg a).eval tr t r pub = Fp.neg (a.eval tr t r pub) := rfl
@[simp] theorem eval_isFirst :
    Expr.isFirst.eval tr t r pub = if r = 0 then 1 else 0 := rfl
end Ev

theorem fp_mul_eq_zero {a b : Fp} (h : Fp.mul a b = 0) : a = 0 ∨ b = 0 := by
  rw [Fp.eq_zero_iff, Fp.toNat_mul] at h
  rcases (p_prime.2 _ (Nat.gcd_dvd_left P a.toNat)) with h1 | h1
  · right
    rw [Fp.eq_zero_iff]
    have hc : Nat.Coprime P a.toNat := h1
    have := hc.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero h)
    rcases Nat.eq_zero_or_pos b.toNat with h0 | h0
    · exact h0
    · have := Nat.le_of_dvd h0 this; have := b.toNat_lt; omega
  · left
    rw [Fp.eq_zero_iff]
    have : P ∣ a.toNat := h1 ▸ Nat.gcd_dvd_right P a.toNat
    rcases Nat.eq_zero_or_pos a.toNat with h0 | h0
    · exact h0
    · have := Nat.le_of_dvd h0 this; have := a.toNat_lt; omega

end ZkFormal.Sha
