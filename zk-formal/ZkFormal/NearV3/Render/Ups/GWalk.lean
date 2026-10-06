import ZkFormal.NearV3.Render.Ups.Tac
import ZkFormal.NearV3.Render.WalkLocal

/-!
# ZkFormal.NearV3.Render.Ups.GWalk — `cWalk` on the honest table

Helpers for `cWalk` (in progress): the inverse cell `inv = (sym − nib)⁻¹` (`inv_cast`) and the
bitmap bits of `W1`/`W2` (`bm_bits`).  The walk conditions are `WalkOkU` (`Ok.lean`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

namespace UpsGen

/-- The inverse cell. -/
theorem inv_cast (a b : Nat) (ha : a < ZkFormal.Algebra.P) (hb : b < ZkFormal.Algebra.P) (h : a ≠ b) :
    ((((a : Int) - (b : Int)) * (((Fp.ofNat a - Fp.ofNat b)⁻¹).toNat : Int) - 1 : Int) : Fp) = 0 := by
  rw [Lean.Grind.Ring.intCast_sub, Lean.Grind.Ring.intCast_mul, Lean.Grind.Ring.intCast_sub,
    Lean.Grind.Ring.intCast_natCast, Lean.Grind.Ring.intCast_natCast, Lean.Grind.Ring.intCast_natCast]
  show (Fp.ofNat a - Fp.ofNat b) * Fp.ofNat ((Fp.ofNat a - Fp.ofNat b)⁻¹).toNat - ((1 : Int) : Fp) = 0
  rw [Fp.ofNat_toNat, Fp.mul_inv_cancel (WalkLocal.fp_ne ha hb h)]
  rfl

theorem sum_cast : ∀ l : List Nat, (l.map fun n : Nat => (n : Int)).sum = ((l.sum : Nat) : Int)
  | [] => rfl
  | a :: l => by simp [sum_cast l]

theorem bm_bits (x : Nat) (h : x < 2 ^ 16) :
    ((List.range 16).map fun i => (2 ^ i : Int) * ((x / 2 ^ i % 2 : Nat) : Int)).sum = x := by
  have := WalkGen.bits_sum x 16
  rw [Nat.mod_eq_of_lt h] at this
  have e : ((List.range 16).map fun i => (2 ^ i : Int) * ((x / 2 ^ i % 2 : Nat) : Int)) =
      ((List.range 16).map fun j => 2 ^ j * (x / 2 ^ j % 2)).map (fun n : Nat => (n : Int)) := by
    simp [List.map_map]
  rw [e, sum_cast, this]

end UpsGen

end ZkFormal.NearV3.Render
