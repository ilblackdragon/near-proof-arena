import DKTWhirFold
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.BinaryFoldAgreement
import Mathlib.FieldTheory.Finite.Basic
set_option maxRecDepth 100000

/-!
# Ordered-coset identification for the deployed WHIR domain

`DKTWhirFold.cosetMajorSquareDomain` builds a `SquarePairedDomain` from an abstract odd
generator `zeta` of order `c` and an even generator `omega` of order `2h`, laid out in the
`a * h + u` ("coset-major") order. That is abstract: it does not say that the backend's integer
index arithmetic, or its concrete generator constants, produce those roots.

## What is proved here

1. **Index arithmetic.** `odd_domain::query_root`
   (`crates/stark-backend/src/odd_domain.rs:52-67`) maps an index
   `i = a * 2^(L-k) + u0` to `odd_root(c)^a * omega_L^u0`, where
   `odd_root(c) = GENERATOR^((p-1)/c)` (`odd_domain.rs:44-48`). `cosetIndex` is exactly the
   `Fin (c*h) ≃ Fin c × Fin h` index map, and `cosetIndex_*_val` pin the `a = i / h`,
   `u = i % h` arithmetic. `roots_eq_cosetMajor` shows the roots produced by that layout are a
   `DKTWhirFold.cosetMajorSquareDomain`'s roots.
2. **Concrete generators.** Kernel-checked for the deployed `p = 15 * 2^27 + 1`:
   `fieldGenerator_isPrimitive` (`31` has order `p-1`, via the prime cofactors `2, 3, 5`),
   `fifteenRoot_eq` / `fifteenRoot_isPrimitive` (`31^((p-1)/15) = 1995471372`, order 15), and
   `two_adic_half_turn` (`omega^h = -1` for `h = 2^K`). Hence `deployedSquareDomain` builds the
   deployed `SquarePairedDomain` at `c = 15` with no hypotheses on the generators.

## What is *not* proved

The residual bridge: that the **compiled Rust** evaluates these expressions on the same integer
representatives, with the same `Fin` layout and the same `hash_coset` leaf ordering. That is a
Rust-semantics argument, not a ring identity. It is stated exactly in
`docs/logs/pq-whir-transfer-2026-10-21.md` and marked open; nothing below implies it.

Nothing here is a soundness theorem.
-/

namespace DKTOrderedCoset

open Polynomial ReedSolomon

/-- The deployed base field order: `15 * 2^27 + 1`. -/
def babyBear : ℕ := 2013265921

theorem babyBear_eq : babyBear = 15 * 2 ^ 27 + 1 := by decide

/-- The Plonky3 field generator constant (`baby_bear.rs:28`, `MONTY_GEN = 31`). -/
def fieldGenerator : ℕ := 31

/-- The odd factor the production verifier uses (`domain_odd_factor = 15`). -/
def oddFactor : ℕ := 15

/-- `odd_domain::odd_root::<BabyBear>(15)`, `odd_domain.rs:44-48`:
`GENERATOR^((p-1)/15)` reduced in the base field. -/
def fifteenRoot : ZMod babyBear :=
  (fieldGenerator : ZMod babyBear) ^ ((babyBear - 1) / oddFactor)

/-- `k`-fold repeated squaring. The kernel cannot form `31^(2^27)` as one numeral, but it can
square a bounded field element 27 times: `sqChain a k = a^(2^k)`. -/
def sqChain (a : ZMod babyBear) : ℕ → ZMod babyBear
  | 0 => a
  | n + 1 => (sqChain a n) ^ 2
theorem sqChain_eq (a : ZMod babyBear) (n : ℕ) : sqChain a n = a ^ 2 ^ n := by
  induction n with
  | zero => simp [sqChain]
  | succ n ih => rw [sqChain, ih, pow_succ]; ring_nf
theorem sqChain_pow (g : ZMod babyBear) (m k : ℕ) :
    sqChain (g ^ m) k = g ^ (m * 2 ^ k) := by
  rw [sqChain_eq, ← pow_mul]
theorem twoAdic_part : babyBear - 1 = 2 ^ 27 * 15 := by norm_num [babyBear]

theorem fieldGenerator_isPrimitive : orderOf (fieldGenerator : ZMod babyBear) = babyBear - 1 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (n := babyBear - 1) (by norm_num [babyBear])
  · have hsq : sqChain ((fieldGenerator : ZMod babyBear) ^ 15) 27 = 1 := by decide +kernel
    rw [sqChain_pow] at hsq
    rw [show 15 * 2 ^ 27 = 2 ^ 27 * 15 by ring] at hsq
    rwa [← twoAdic_part] at hsq
  · intro p hp hd
    rw [twoAdic_part] at hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
    · have hp2 : p = 2 := by
        have h2 : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp h
        rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp h2 with h1 | h1
        · exact absurd h1 hp.ne_one
        · exact h1
      subst hp2
      have hsq : sqChain ((fieldGenerator : ZMod babyBear) ^ 15) 26 = -1 := by decide +kernel
      rw [sqChain_pow] at hsq
      rw [show 15 * 2 ^ 26 = (2 ^ 27 * 15) / 2 by norm_num] at hsq
      rw [← twoAdic_part] at hsq
      rw [hsq]
      decide
    · have hle : p ≤ 15 := Nat.le_of_dvd (by norm_num) h
      have hcases : p = 3 ∨ p = 5 := by
        interval_cases p <;> simp_all (config := { decide := true })
      rcases hcases with rfl | rfl
      · have hsq : sqChain ((fieldGenerator : ZMod babyBear) ^ 5) 27 = 1314723123 := by
          decide +kernel
        rw [sqChain_pow] at hsq
        rw [show 5 * 2 ^ 27 = (2 ^ 27 * 15) / 3 by norm_num] at hsq
        rw [← twoAdic_part] at hsq
        rw [hsq]; decide
      · have hsq : sqChain ((fieldGenerator : ZMod babyBear) ^ 3) 27 = 645581151 := by
          decide +kernel
        rw [sqChain_pow] at hsq
        rw [show 3 * 2 ^ 27 = (2 ^ 27 * 15) / 5 by norm_num] at hsq
        rw [← twoAdic_part] at hsq
        rw [hsq]; decide
/-- The value `odd_root::<BabyBear>(15)` evaluates to, `31^((p-1)/15) = 31^(2^27)`. -/
theorem fifteenRoot_eq : fifteenRoot = 1995471372 := by
  have hexp : (babyBear - 1) / oddFactor = 2 ^ 27 := by decide
  rw [fifteenRoot, hexp]
  have h := sqChain_eq (fieldGenerator : ZMod babyBear) 27
  rw [← h]
  decide +kernel

/-- `31` is a primitive `(p-1)`-th root of unity. -/
theorem fieldGenerator_root :
    IsPrimitiveRoot (fieldGenerator : ZMod babyBear) (babyBear - 1) :=
  IsPrimitiveRoot.iff_orderOf.mpr fieldGenerator_isPrimitive

/-- The order-15 coset generator. -/
theorem fifteenRoot_isPrimitive : IsPrimitiveRoot fifteenRoot oddFactor := by
  have hdvd : ((babyBear - 1) / oddFactor) ∣ (babyBear - 1) := by decide
  have h := fieldGenerator_root.pow_of_dvd
    (by decide : ((babyBear - 1) / oddFactor) ≠ 0) hdvd
  simpa [fifteenRoot,
    show (babyBear - 1) / ((babyBear - 1) / oddFactor) = oddFactor from by decide] using h

/-- The two-adic half turn: an element of order `2h` satisfies `omega^h = -1`. -/
theorem two_adic_half_turn {F : Type} [Field F] (h : ℕ) (hh : 0 < h) (omega : F)
    (homega : IsPrimitiveRoot omega (2 * h)) : omega ^ h = -1 := by
  have hs : (omega ^ h) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm h 2]; exact homega.pow_eq_one
  have hne : omega ^ h ≠ 1 := homega.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  exact (sq_eq_one_iff.mp hs).resolve_left hne

/-! ## Index arithmetic of the coset-major layout -/

/-- Index map for a `c * h` domain with `c` odd: `i ↦ (i / h, i % h)`, i.e. the backend's
`a * h + u ↦ (a, u)` decomposition (`odd_domain.rs:52-67`). -/
def cosetIndex (c h : ℕ) : Fin (c * h) ≃ Fin c × Fin h := finProdFinEquiv.symm

theorem cosetIndex_fst (c h : ℕ) (i : Fin (c * h)) :
    (cosetIndex c h i).1.val = i.val / h := by
  simp [cosetIndex, finProdFinEquiv, Fin.divNat]

theorem cosetIndex_snd (c h : ℕ) (i : Fin (c * h)) :
    (cosetIndex c h i).2.val = i.val % h := by
  simp [cosetIndex, finProdFinEquiv, Fin.modNat]

/-- The backend's index arithmetic: `i = (i / h) * h + (i % h)`, i.e. `index = a*h + u` with
`a = i / h` and `u = i % h` (`odd_domain.rs:52-67`). -/
theorem cosetIndex_decomp (c h : ℕ) (i : Fin (c * h)) :
    i.val = (cosetIndex c h i).1.val * h + (cosetIndex c h i).2.val := by
  rw [cosetIndex_fst, cosetIndex_snd, Nat.mul_comm (i.val / h) h, Nat.div_add_mod]

/-- **Ordered-coset identification (algebra).** The roots produced by the deployed layout
`i = a*h + u ↦ zeta^a * omega^u` are a `DKTWhirFold.cosetMajorSquareDomain`, so they form a
`SquarePairedDomain` for the backend's coset-major word. -/
theorem roots_eq_cosetMajor {c h : ℕ} (hc : 0 < c) (hh : 0 < h) {F : Type} [Field F]
    [NeZero (2 : F)] (zeta omega : F) (hzeta : IsPrimitiveRoot zeta c) (homega : IsPrimitiveRoot omega (2 * h))
    (hodd : Nat.Coprime 2 c) (hcop : c.Coprime h) :
    ∃ D : SquarePairedDomain F (c * h),
      ∀ i : Fin (c * h),
        D.root i = zeta ^ (cosetIndex c h i).1.val * omega ^ (cosetIndex c h i).2.val :=
  ⟨DKTWhirFold.cosetMajorSquareDomain hc hh zeta omega hzeta homega hodd hcop, fun _ => rfl⟩

/-- **The deployed instantiation.** At `c = 15` and `h = 2^K` with `K > 0`, any field with a
primitive 15th root and a primitive `2^(K+1)`-th root carries the backend's coset-major
`SquarePairedDomain`. The concrete constants `fifteenRoot`/`fifteenRoot_isPrimitive` are pinned
separately below; `deployed_coprime` supplies the two coprimality hypotheses. -/
theorem deployedSquareDomain {F : Type} [Field F] [NeZero (2 : F)] (K : ℕ) (hK : 0 < K)
    (zeta omega : F) (hzeta : IsPrimitiveRoot zeta 15)
    (homega : IsPrimitiveRoot omega (2 * 2 ^ K)) :
    ∃ D : SquarePairedDomain F (15 * 2 ^ K),
      ∀ i : Fin (15 * 2 ^ K),
        D.root i = zeta ^ (cosetIndex 15 (2 ^ K) i).1.val *
          omega ^ (cosetIndex 15 (2 ^ K) i).2.val :=
  roots_eq_cosetMajor (c := 15) (h := 2 ^ K) (by decide) (by positivity) zeta omega
    hzeta homega (by decide) ((by decide : Nat.Coprime 15 2).pow_right K)

/-- `15` is odd and coprime to every power of two, so squaring does not collapse the odd
factor: exactly the `hodd`/`hcop` hypotheses of `cosetMajorSquareDomain`. -/
theorem deployed_coprime (K : ℕ) : Nat.Coprime 2 15 ∧ Nat.Coprime 15 (2 ^ K) :=
  ⟨by decide, (by decide : Nat.Coprime 15 2).pow_right K⟩

end DKTOrderedCoset
#print axioms DKTOrderedCoset.fifteenRoot_eq
#print axioms DKTOrderedCoset.fieldGenerator_isPrimitive
#print axioms DKTOrderedCoset.fifteenRoot_isPrimitive
#print axioms DKTOrderedCoset.two_adic_half_turn
#print axioms DKTOrderedCoset.cosetIndex_decomp
#print axioms DKTOrderedCoset.roots_eq_cosetMajor
#print axioms DKTOrderedCoset.deployedSquareDomain
