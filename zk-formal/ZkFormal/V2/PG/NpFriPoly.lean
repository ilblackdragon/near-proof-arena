import ZkFormal.V2.PG.NpLocal2

/-!
# ZkFormal.V2.PG.NpFriPoly (P2 copy of `Prover.NpFriPoly` at `dp = pg g`) — the honest FRI words are low-degree polynomials

`word_poly`: layer `i ≤ ℓ` is the evaluation of a polynomial of length `2^(n0-4-i)` on its
domain (folding halves the length; roll-ins add a DEEP batch of the same length).
-/

namespace ZkFormal.Prover.Np.G

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

attribute [local instance] Semiring.natCast

theorem two_ne_zero_fp8 : (2 : Fp8) ≠ 0 := fun h => absurd (congrArg Fp8.c0 h) (by decide +kernel)

theorem ev_split_ilv (m : Nat) (W : Nat → Fp8) (x : Fp8) :
    ev (2 * m) W x = ev m (fun k => W (2 * k)) (x * x) + x * ev m (fun k => W (2 * k + 1)) (x * x) := by
  rw [← ev_ilv]
  apply ev_congr
  intro k _
  simp only [ZkFormal.Udr.ilv]
  split
  · congr 1; omega
  · congr 1; omega

/-- One fold of a polynomial word at `±y`. -/
theorem fold_word_poly (m : Nat) (W : Nat → Fp8) (β : Fp8) (yF : Fp) (hy : yF ≠ 0) :
    (2 : Fp8)⁻¹ * (ev (2 * m) W (Fp8.ofBase yF) + ev (2 * m) W (-Fp8.ofBase yF)) +
      β * (ev (2 * m) W (Fp8.ofBase yF) - ev (2 * m) W (-Fp8.ofBase yF)) * Fp8.ofBase ((2 * yF)⁻¹) =
    ev m (fun k => W (2 * k) + β * W (2 * k + 1)) (Fp8.ofBase yF * Fp8.ofBase yF) := by
  rw [ev_split_ilv, ev_split_ilv, ev_add, ev_smul]
  have hy8 : Fp8.ofBase yF ≠ 0 := fun h => hy (Fp8.ofBase_inj (h.trans rfl))
  have h2 := two_ne_zero_fp8
  rw [ofBase_inv, Fp8.ofBase_mul, show Fp8.ofBase 2 = (2 : Fp8) from rfl]
  have e : -Fp8.ofBase yF * -Fp8.ofBase yF = Fp8.ofBase yF * Fp8.ofBase yF := by grind
  rw [e]
  generalize ev m (fun k => W (2 * k)) (Fp8.ofBase yF * Fp8.ofBase yF) = E
  generalize ev m (fun k => W (2 * k + 1)) (Fp8.ofBase yF * Fp8.ofBase yF) = O
  generalize Fp8.ofBase yF = y at hy8 ⊢
  have i2 := Field.mul_inv_cancel h2
  have iy := Field.mul_inv_cancel (show (2 : Fp8) * y ≠ 0 from fun h => by
    rcases gp_mul_eq_zero h with h | h
    · exact h2 h
    · exact hy8 h)
  grind

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp) (cs : List Fp8)

theorem n0_le (hok : headerOk A dp (hdr A tr) = true) : n0 A tr ≤ 26 :=
  ZkFormal.Stark.queryLog_le A dp (hdr A tr) hok

theorem pt_ofBase (n0' m p : Nat) : pt n0' m p = Fp8.ofBase (domPoint (K := Fp8) n0' m p) := rfl

theorem Bw_poly (hlen : cs.length = nMsg A tr) (hz : ¬ (cZ cs).IsBase) (m : Nat) (hm : m - 4 ≤ 27) :
    ∃ G : Nat → Fp8, ∀ p, Bw A cb tr cs m p = ev (2 ^ (m - 4)) G (pt (n0 A tr) m p) := by
  obtain ⟨G, hG⟩ := deepH_poly A cb tr cs (honCtx_ctx0 A cb tr cs hlen) hz m hm
  exact ⟨G, fun p => by rw [Bw_eq A cb tr cs hlen, pt_ofBase, hG]⟩

/-- **The FRI words are low-degree polynomials on their domains.** -/
theorem word_poly (hok : headerOk A dp (hdr A tr) = true) (hlen : cs.length = nMsg A tr)
    (hz : ¬ (cZ cs).IsBase) : ∀ i, i ≤ ell A tr → ∃ W : Nat → Fp8, ∀ q,
      word A cb tr cs i q = ev (2 ^ (n0 A tr - 4 - i)) W (pt (n0 A tr) (n0 A tr - i) q)
  | 0, _ => by
    obtain ⟨G, hG⟩ := Bw_poly A cb tr cs hlen hz (n0 A tr) (by have := n0_le A tr hok; omega)
    exact ⟨G, fun q => by simp only [word, Nat.sub_zero]; exact hG q⟩
  | i + 1, hi => by
    have hn := n0_le A tr hok
    have hℓ : ell A tr = n0 A tr - 4 - 1 := rfl
    obtain ⟨W, hW⟩ := word_poly hok hlen hz i (by omega)
    obtain ⟨G, hG⟩ := Bw_poly A cb tr cs hlen hz (n0 A tr - (i + 1)) (by omega)
    have e2 : 2 ^ (n0 A tr - 4 - i) = 2 * 2 ^ (n0 A tr - 4 - (i + 1)) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have hm : n0 A tr - i = (n0 A tr - (i + 1)) + 1 := by omega
    let β := (betaL A tr cs).getD i 0
    have hfold : ∀ q, (2 : Fp8)⁻¹ * (word A cb tr cs i (2 * q) + word A cb tr cs i (2 * q + 1)) +
        β * (word A cb tr cs i (2 * q) - word A cb tr cs i (2 * q + 1)) *
          Fp8.ofBase (((2 : Fp) * domPoint (F := Fp) (K := Fp8) (n0 A tr) (n0 A tr - i) (2 * q))⁻¹) =
        ev (2 ^ (n0 A tr - 4 - (i + 1))) (fun k => W (2 * k) + β * W (2 * k + 1))
          (pt (n0 A tr) (n0 A tr - (i + 1)) q) := by
      intro q
      have hsib : pt (n0 A tr) (n0 A tr - i) (2 * q + 1) = - pt (n0 A tr) (n0 A tr - i) (2 * q) := by
        rw [hm]; exact pt_sibling (by omega) q
      have hsq : pt (n0 A tr) (n0 A tr - i) (2 * q) * pt (n0 A tr) (n0 A tr - i) (2 * q) =
          pt (n0 A tr) (n0 A tr - (i + 1)) q := by
        rw [hm]; exact pt_sq (by omega) (by omega) q
      have hy : domPoint (F := Fp) (K := Fp8) (n0 A tr) (n0 A tr - i) (2 * q) ≠ 0 := by
        intro h
        exact pt_ne_zero (n0 := n0 A tr) (m := n0 A tr - i) (by omega) (2 * q) (by rw [pt_ofBase, h]; rfl)
      rw [hW, hW, hsib, e2, pt_ofBase, fold_word_poly _ W β _ hy, ← pt_ofBase, hsq]
    refine ⟨fun k => W (2 * k) + β * W (2 * k + 1) +
      (match (gammaL A tr cs).lookup (i + 1) with | some g => g * G k | none => 0), fun q => ?_⟩
    have hd : n0 A tr - (i + 1) - 4 = n0 A tr - 4 - (i + 1) := by omega
    simp only [word]
    rw [hfold q]
    cases (gammaL A tr cs).lookup (i + 1) with
    | none =>
      simp only
      rw [show (fun k => W (2 * k) + β * W (2 * k + 1) + 0) = (fun k => W (2 * k) + β * W (2 * k + 1)) from
        funext fun k => by grind]
    | some g =>
      simp only
      rw [hG, hd, ← ev_smul, ← ev_add]

end

end ZkFormal.Prover.Np.G
