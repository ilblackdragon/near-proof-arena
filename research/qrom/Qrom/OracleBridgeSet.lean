import Qrom.OracleBridge

/-!
# The multi-pair hash bridge: from one fixed pair to the set an execution uses

`Qrom.OracleBridge` fixes **one** pair `(m, y)` before the experiment starts and
proves `Pr[H(m) = y] = 1/|Y|`, hence the acceptance/failure trade-off
`1 - δ - 1/|Y|`. `PROOF.md` §7.3 says the piece still missing is the step to
*"the set of pairs actually used by an accepting execution"*, where that set is
not fixed in advance.

This file supplies the counting half of that step, and it is stronger than the
fixed-pair version because the count does not depend on *which* pairs are used:

* `agree_card` — with the oracle restricted to agree with a concrete function on
  a pair set `Q ⊆ D`, exactly `|Y|^(|D|-|Q|)` of the `|Y|^|D|` functions agree;
* `agree_count_mul` — the integer form the arena's `PrLE` consumes:
  `|agree| · |Y|^|Q| = |Y|^|D|`, i.e. probability exactly `|Y|^{-|Q|}`;
* `acceptance_le_agreement` — if acceptance requires agreement on `Q`, then
  `|accepted| ≤ |Y|^(|D|-|Q|)`;
* `acceptance_PrLE` — the same in the arena's `PrLE` shape:
  `|accepted| · |Y|^|Q| ≤ |Y|^|D|` (`den = |Y|^|Q|`);
* `delta_ge_one_sub_agreement` — with acceptance probability `≥ 1 - δ`,
  `δ ≥ 1 - |Y|^{-|Q|}`.

The consequence for the paper is a *negative* one, and it is quantified. At
384-bit answers and any nonempty `Q`, `|Y|^{-|Q|} = 2^{-384|Q|}`, so `δ ≥
1 - 2^{-384}`: a model in which the pairs an accepting execution used are
independent oracle answers cannot accept at any non-negligible probability. The
bound does not improve as `Q` grows — it gets *worse* for the identification,
because the acceptance ceiling shrinks. A runtime cap changes nothing: `|Q|` is
a count of pairs, not a time bound. This is the same obstruction as
`Qrom.OracleBridge`, now with the pair set adaptive and unbounded.

The premise is `hacc`: that acceptance requires agreement on `Q`. It is *not*
proved here, does not follow from SHA-384 collision resistance, and is exactly
what a (c)-endpoint must assume or a (d)-endpoint must build a model for. The
arena-`PrLE` counterpart, with the demand sequence made explicit as a function
of the answers consumed so far, is
`research/hash-bridge/HashBridge/Endpoint.lean`.
-/
namespace Qrom.OracleBridgeSet

open Finset

section Counting

variable {D Y : Type} [Fintype D] [Fintype Y] [DecidableEq D] [DecidableEq Y] [Nonempty Y]

/-- Functions agreeing with `v` on all of `Q` are exactly functions on the
complement of `Q`. -/
noncomputable def agreeEquiv (Q : Finset D) (v : D → Y) :
    {f : D → Y // ∀ d ∈ Q, f d = v d} ≃ (({d // d ∉ Q}) → Y) where
  toFun f d := f.1 d.1
  invFun g := ⟨fun d => if h : d ∈ Q then v d else g ⟨d, h⟩, by
    intro d hd
    simp [hd]⟩
  left_inv f := by
    apply Subtype.ext
    funext d
    by_cases hd : d ∈ Q
    · simp [hd, f.2 d hd]
    · simp [hd]
  right_inv g := by
    funext d
    simp [d.2]

/-- **The multi-pair count.** Exactly `|Y|^(|D|-|Q|)` oracles agree with a
concrete function `v` on every pair in `Q`. -/
theorem agree_card (Q : Finset D) (v : D → Y) :
    Fintype.card {f : D → Y // ∀ d ∈ Q, f d = v d} = Fintype.card Y ^ (Fintype.card D - Q.card) := by
  classical
  rw [Fintype.card_congr (agreeEquiv Q v), Fintype.card_fun]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_coe]

/-- **The integer form for `PrLE`.** The agreeing set has probability exactly
`|Y|^{-|Q|}`: `|agree| · |Y|^|Q| = |Y|^|D|`. -/
theorem agree_count_mul (Q : Finset D) (v : D → Y) :
    Fintype.card {f : D → Y // ∀ d ∈ Q, f d = v d} * Fintype.card Y ^ Q.card =
      Fintype.card Y ^ Fintype.card D := by
  rw [agree_card, ← pow_add, Nat.sub_add_cancel (Finset.card_le_univ Q)]

/-- The oracles that disagree somewhere on `Q`. -/
abbrev disagree (Q : Finset D) (v : D → Y) : Finset (D → Y) :=
  Finset.univ.filter fun f => ∃ d ∈ Q, f d ≠ v d

/-- **Acceptance is bounded by agreement.** If every accepting oracle must agree
with the concrete function on all of `Q`, then acceptance has probability at
most `|Y|^{-|Q|}`.

This is the *upper* bound, and it is the substantive one: it is what turns the
paper's `1 - δ` acceptance premise into the requirement
`1 - δ ≤ |Y|^{-|Q|}`. At 384-bit answers and `|Q| ≥ 1` that forces
`δ ≥ 1 - 2^-384`: a model in which the pairs an accepting execution used are
independent oracle answers cannot accept at any non-negligible probability. No
runtime cap changes this — `|Q|` is a count of pairs, not a time bound. -/
theorem acceptance_le_agreement (Q : Finset D) (v : D → Y)
    (accepted : Finset (D → Y))
    (hacc : ∀ f ∈ accepted, ∀ d ∈ Q, f d = v d) :
    accepted.card ≤ Fintype.card Y ^ (Fintype.card D - Q.card) := by
  classical
  have hsub : accepted ⊆ Finset.univ.filter (fun f : D → Y => ∀ d ∈ Q, f d = v d) := by
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hacc f hf
  have h1 : accepted.card ≤
      (Finset.univ.filter (fun f : D → Y => ∀ d ∈ Q, f d = v d)).card :=
    Finset.card_le_card hsub
  have h2 : (Finset.univ.filter (fun f : D → Y => ∀ d ∈ Q, f d = v d)).card =
      Fintype.card {f : D → Y // ∀ d ∈ Q, f d = v d} :=
    (Fintype.card_subtype _).symm
  rw [h2, agree_card] at h1
  exact h1

/-- **The trade-off, in integers.** If acceptance requires agreement on `Q` and
`B` of the `|Y|^|D|` oracles are accepting, then
`B · |Y|^|Q| ≤ |Y|^|D|` — exactly the `PrLE` shape with `num = 1`,
`den = |Y|^|Q|`. -/
theorem acceptance_PrLE (Q : Finset D) (v : D → Y)
    (accepted : Finset (D → Y))
    (hacc : ∀ f ∈ accepted, ∀ d ∈ Q, f d = v d) :
    accepted.card * Fintype.card Y ^ Q.card ≤ Fintype.card Y ^ Fintype.card D := by
  have h := acceptance_le_agreement Q v accepted hacc
  calc accepted.card * Fintype.card Y ^ Q.card
      ≤ Fintype.card Y ^ (Fintype.card D - Q.card) * Fintype.card Y ^ Q.card :=
        Nat.mul_le_mul_right _ h
    _ = Fintype.card Y ^ Fintype.card D := by
        rw [← pow_add, Nat.sub_add_cancel (Finset.card_le_univ Q)]

/-- **The real-valued trade-off.** Acceptance at `1 - δ` with required agreement
on `Q` gives `δ ≥ 1 - |Y|^{-|Q|}`. For `|Q| ≥ 1` and `|Y| = 2^384` this is
`δ ≥ 1 - 2^-384`: the premise and the model are incompatible for any meaningful
acceptance probability. -/
theorem delta_ge_one_sub_agreement (Q : Finset D) (v : D → Y)
    (accepted : Finset (D → Y)) (δ : ℝ)
    (hacc : ∀ f ∈ accepted, ∀ d ∈ Q, f d = v d)
    (haccept : 1 - δ ≤ (accepted.card : ℝ) / (Fintype.card (D → Y) : ℝ)) :
    δ ≥ 1 - 1 / ((Fintype.card Y : ℝ) ^ Q.card) := by
  have hcard : (accepted.card : ℝ) ≤
      (Fintype.card Y : ℝ) ^ (Fintype.card D - Q.card) := by
    exact_mod_cast acceptance_le_agreement Q v accepted hacc
  have hY : (0 : ℝ) < (Fintype.card Y : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hden : (0 : ℝ) < (Fintype.card (D → Y) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hD : Fintype.card D - Q.card + Q.card = Fintype.card D :=
    Nat.sub_add_cancel (Finset.card_le_univ Q)
  have hrew : (Fintype.card (D → Y) : ℝ) = (Fintype.card Y : ℝ) ^ Fintype.card D := by
    rw [Fintype.card_fun]; push_cast; ring
  have hratio : (accepted.card : ℝ) / (Fintype.card (D → Y) : ℝ) ≤
      1 / (Fintype.card Y : ℝ) ^ Q.card := by
    rw [hrew]
    have hq : ((Fintype.card Y : ℝ) ^ (Fintype.card D - Q.card)) /
        ((Fintype.card Y : ℝ) ^ Fintype.card D) =
        1 / (Fintype.card Y : ℝ) ^ Q.card := by
      have e : (Fintype.card Y : ℝ) ^ Fintype.card D =
          (Fintype.card Y : ℝ) ^ (Fintype.card D - Q.card) *
            (Fintype.card Y : ℝ) ^ Q.card := by
        rw [← pow_add, hD]
      rw [e]
      field_simp
    calc (accepted.card : ℝ) / (Fintype.card Y : ℝ) ^ Fintype.card D
        ≤ (Fintype.card Y : ℝ) ^ (Fintype.card D - Q.card) /
            (Fintype.card Y : ℝ) ^ Fintype.card D :=
          div_le_div_of_nonneg_right hcard (by positivity)
      _ = 1 / (Fintype.card Y : ℝ) ^ Q.card := hq
  linarith

end Counting

/-! ## The 384-bit instance -/

/-- At 384-bit answers, `ℓ` pairs agree with probability `2^{-384ℓ}`:
`(2^384)^ℓ = 2^(384ℓ)` in the denominator. -/
theorem bits_384 (ℓ : ℕ) : ((2 ^ 384 : ℕ) ^ ℓ) = 2 ^ (384 * ℓ) := by
  rw [← Nat.pow_mul]

/-- The 42-byte (336-bit) narrow-digest instance: `(2^336)^ℓ = 2^(336ℓ)`; this is
the alphabet the paper's `ℓ_V / 2^336` term uses, not the arena's `2^256`. -/
theorem bits_336 (ℓ : ℕ) : ((2 ^ 336 : ℕ) ^ ℓ) = 2 ^ (336 * ℓ) := by
  rw [← Nat.pow_mul]

end Qrom.OracleBridgeSet

#print axioms Qrom.OracleBridgeSet.agree_card
#print axioms Qrom.OracleBridgeSet.agree_count_mul
#print axioms Qrom.OracleBridgeSet.acceptance_le_agreement
#print axioms Qrom.OracleBridgeSet.acceptance_PrLE
#print axioms Qrom.OracleBridgeSet.delta_ge_one_sub_agreement
#print axioms Qrom.OracleBridgeSet.bits_384
#print axioms Qrom.OracleBridgeSet.bits_336
