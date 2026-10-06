import ZkFormal.V2.PG.NpLocal3

/-!
# ZkFormal.V2.PG.NpFinal (P2 copy of `Prover.NpFinal` at `dp = pg g`) — the final polynomial and the commitment-chain fold
-/

namespace ZkFormal.Prover.Np.G

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

attribute [local instance] Semiring.natCast

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp) (cs : List Fp8)

/-- **The final layer is the line sent in the clear.** -/
theorem final_check (hok : headerOk A dp (hdr A tr) = true) (hlen : cs.length = nMsg A tr)
    (hz : ¬ (cZ cs).IsBase) (q : Nat) :
    word A cb tr cs (ell A tr) q = (finalPoly A cb tr cs).getD 0 0 +
      (finalPoly A cb tr cs).getD 1 0 * pt (n0 A tr) (n0 A tr - ell A tr) q := by
  obtain ⟨W, hW⟩ := word_poly A cb tr cs hok hlen hz (ell A tr) (Nat.le_refl _)
  have hn := n0_le A tr hok
  have hℓ : ell A tr = n0 A tr - 4 - 1 := rfl
  have h2 := two_ne_zero_fp8
  have i2 := Field.inv_mul_cancel h2
  unfold finalPoly
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [hW 0, hW 1, hW q]
  by_cases h5 : 5 ≤ n0 A tr
  · rw [show n0 A tr - 4 - ell A tr = 1 by omega]
    have hsib : pt (n0 A tr) (n0 A tr - ell A tr) 1 = - pt (n0 A tr) (n0 A tr - ell A tr) 0 := by
      rw [show n0 A tr - ell A tr = 4 + 1 by omega]; exact pt_sibling (by omega) 0
    have hy : domPoint (F := Fp) (K := Fp8) (n0 A tr) (n0 A tr - ell A tr) 0 ≠ 0 := by
      intro h
      exact pt_ne_zero (n0 := n0 A tr) (m := n0 A tr - ell A tr) (by omega) 0 (by rw [pt_ofBase, h]; rfl)
    have hy8 : pt (n0 A tr) (n0 A tr - ell A tr) 0 ≠ 0 := fun h => hy (Fp8.ofBase_inj (h.trans rfl))
    rw [hsib, ofBase_inv, Fp8.ofBase_mul, show Fp8.ofBase 2 = (2 : Fp8) from rfl, ← pt_ofBase]
    simp only [show (2 : Nat) ^ 1 = 1 + 1 from rfl, ev_succ, ev_zero]
    generalize pt (n0 A tr) (n0 A tr - ell A tr) 0 = y at hy8 ⊢
    have iy := Field.mul_inv_cancel (show (2 : Fp8) * y ≠ 0 from fun h => by
      rcases gp_mul_eq_zero h with h | h
      · exact h2 h
      · exact hy8 h)
    grind
  · rw [show n0 A tr - 4 - ell A tr = 0 by omega]
    rw [Nat.pow_zero]
    simp only [ev_succ, ev_zero]
    grind

end

/-- Folding along a commitment chain. -/
theorem chain_fold {β : Type} (R : Nat → Bool) (ℓ : Nat) (Pre : Nat → Fp8) (g : Nat × Nat → β)
    (F : Bool × Fp8 → (Nat × Nat) × β → Bool × Fp8)
    (hF : ∀ c0 a, 1 ≤ a → c0 + a ≤ ℓ → (∀ i, c0 < i → i < c0 + a → R i = false) →
      F (true, Pre c0) ((c0, a), g (c0, a)) = (true, Pre (c0 + a))) :
    ∀ (c0 : Nat) (l : List (Nat × Nat)), c0 ≤ ℓ → Chain R ℓ c0 l →
      (l.zip (l.map g)).foldl F (true, Pre c0) = (true, Pre ℓ)
  | c0, [], h, hc => by
    have : c0 = ℓ := by simp only [Chain] at hc; omega
    subst this; rfl
  | c0, (c', a) :: l, h, ⟨h1, h2, h3, h4, h5⟩ => by
    subst h1
    rw [List.map_cons, List.zip_cons_cons, List.foldl_cons, hF c' a h2 h3 h4]
    exact chain_fold R ℓ Pre g F hF (c' + a) l h3 h5

end ZkFormal.Prover.Np.G
