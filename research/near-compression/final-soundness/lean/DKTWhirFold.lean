import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.BinaryFoldAgreement
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Backend fold identity for the DKT transfer

`backendFold_eq` identifies verifier/whir.rs:binary_k_fold's one-step algebra
with ArkLib's binaryFoldedWord. DKTG2FoldTransfer.lean composes this identity
with the 13 selected, kernel-checked measured FINAL subfold certificates.

This is not a theorem identifying the entire Rust loop or its ordered cosets,
nor an adaptive WHIR/game theorem. Those obligations remain explicit.
-/
namespace DKTWhirFold
open Polynomial ReedSolomon
set_option maxRecDepth 100000

variable {F : Type} [Field F] [NeZero (2 : F)] {n : ℕ}

/-- Verbatim algebraic operation in backend verifier/whir.rs:binary_k_fold. -/
def backendFold (domain : SquarePairedDomain F n)
    (word : Fin n × Fin 2 → F) (gamma : F) : Fin n → F := fun i =>
  word (i, 0) + (gamma - domain.root i) *
    (word (i, 0) - word (i, 1)) / (2 * domain.root i)

/-- The backend's operation is precisely the word consumed by ArkLib's
binary-fold reconstruction theorem. The domain roots must be nonzero. -/
theorem backendFold_eq (domain : SquarePairedDomain F n)
    (word : Fin n × Fin 2 → F) (gamma : F) :
    backendFold domain word gamma = binaryFoldedWord domain word gamma := by
  funext i
  have h2 : (2 : F) ≠ 0 := NeZero.ne 2
  have hx := domain.root_ne_zero i
  simp [backendFold, binaryFoldedWord, powerBatchedWord, Fin.sum_univ_two, binarySplitWord]
  field_simp
  ring

/-- Any multiplicative coset of even order has a valid square-paired domain.
This is independent of power-of-two smoothness. The backend's coset-major
enumeration must still be identified with these indices by a permutation. -/
def primitiveSquareDomain (hn : 0 < n) (g omega : F) (hg : g ≠ 0)
    (homega : IsPrimitiveRoot omega (2*n)) : SquarePairedDomain F n where
  root i := g * omega ^ i.val
  child := {
    toFun := fun i => (g * omega ^ i.val)^2
    inj' := by
      intro i j hij
      have hp : omega ^ (i.val * 2) = omega ^ (j.val * 2) := by
        simp only [mul_pow, ← pow_mul] at hij
        exact mul_left_cancel₀ (pow_ne_zero 2 hg) hij
      have he := homega.pow_inj (by omega : i.val * 2 < 2*n)
        (by omega : j.val * 2 < 2*n) hp
      apply Fin.ext
      omega }
  root_ne_zero i := mul_ne_zero hg (pow_ne_zero _ (homega.ne_zero (by omega)))
  root_sq _ := rfl

/-- The second point of each pair is the second half of the primitive-root
enumeration, so this construction really covers the original coset. -/
theorem primitive_half_turn (hn : 0 < n) (omega : F)
    (homega : IsPrimitiveRoot omega (2*n)) : omega^n = -1 := by
  have hs : (omega^n)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm n 2]
    exact homega.pow_eq_one
  have hne : omega^n ≠ 1 := homega.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  exact (sq_eq_one_iff.mp hs).resolve_left hne

/-- Coprime cyclic factors give an injective coset-major enumeration. -/
theorem coprime_product_injective {c h : ℕ} (hc : 0 < c)
    (zeta omega : F) (hzeta : IsPrimitiveRoot zeta c)
    (homega : IsPrimitiveRoot omega h) (hcop : c.Coprime h) :
    Function.Injective (fun i : Fin c × Fin h => zeta^i.1.val * omega^i.2.val) := by
  have hp (i : Fin c × Fin h) :
      (zeta^i.1.val * omega^i.2.val)^h = (zeta^h)^i.1.val := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
    rw [Nat.mul_comm i.1.val h, Nat.mul_comm i.2.val h]
    rw [pow_mul, pow_mul, homega.pow_eq_one, one_pow, mul_one]
  rintro ⟨a, u⟩ ⟨b, v⟩ heq
  have he : (zeta^h)^a.val = (zeta^h)^b.val := by
    exact (hp (a, u)).symm.trans ((congrArg (fun x : F => x^h) heq).trans (hp (b, v)))
  have hab : a = b := Fin.ext ((hzeta.pow_of_coprime h hcop.symm).pow_inj a.isLt b.isLt he)
  subst b
  have huv : omega^u.val = omega^v.val :=
    mul_left_cancel₀ (pow_ne_zero _ (hzeta.ne_zero hc.ne')) heq
  exact Prod.ext rfl (Fin.ext (homega.pow_inj u.isLt v.isLt huv))

/-- The backend's `a*h+u` coset-major root layout is square-paired whenever
the odd and two-adic generators have the declared orders. This avoids assuming
that the order-c factor disappears on squaring. Concrete generator constants
and the Rust integer-index operations still need implementation correspondence. -/
def cosetMajorSquareDomain {c h : ℕ} (hc : 0 < c) (hh : 0 < h)
    (zeta omega : F) (hzeta : IsPrimitiveRoot zeta c)
    (homega : IsPrimitiveRoot omega (2*h))
    (hodd : Nat.Coprime 2 c) (hcop : c.Coprime h) : SquarePairedDomain F (c*h) := by
  let e : Fin (c*h) ≃ Fin c × Fin h := finProdFinEquiv.symm
  let root := fun i : Fin (c*h) => zeta^(e i).1.val * omega^(e i).2.val
  refine { root := root
           child := { toFun := fun i => (root i)^2, inj' := ?_ }
           root_ne_zero := ?_
           root_sq := fun _ => rfl }
  · intro i j hij
    apply e.injective
    apply coprime_product_injective hc (zeta^2) (omega^2)
      (hzeta.pow_of_coprime 2 hodd) (IsPrimitiveRoot.pow (by omega) homega rfl) hcop
    simpa only [root, mul_pow, ← pow_mul, Nat.mul_comm] using hij
  · intro i
    exact mul_ne_zero (pow_ne_zero _ (hzeta.ne_zero hc.ne'))
      (pow_ne_zero _ (homega.ne_zero (by omega)))

end DKTWhirFold

#print axioms DKTWhirFold.backendFold_eq
#print axioms DKTWhirFold.primitiveSquareDomain
#print axioms DKTWhirFold.cosetMajorSquareDomain
