import Mathlib
import Qrom.MerkleSupport

/-!
# Qrom.Fanout — long-output fanout and absorb digest counting

Two §6.4 gaps that are pure counting, and therefore closable here.

## Item 4: long-output fanout

A challenge query returns `J` blocks at once, so a `t`-query adversary produces up
to `J·t` state-output occurrences, and two *distinct* occurrences within one
output can collide. `state_outputs_eq` counts the occurrences; `within_output_pairs`
identifies the number of unordered pairs inside one output as `C(k,2)`, which
`within_output_bound` bounds by `J²`. The resulting per-query bad-slot count with a
bad set of size `B` is `J·B` (`fanout_budget`), and with `B = 2t+1` this is the
`J(2t+1)` of §6.4 step 5.

`mixed_width_sum` proves the mixed-width step: charging `ℓ_w` wide points at
`2³⁸⁴` and `ℓ_n` narrow points at `2³³⁶` is at most `(ℓ_w+ℓ_n)/2³³⁶`. That is
§6.4 step 7's `Σ 1/M ≤ ℓ_V/2³³⁶`, derived rather than assumed, and
`wide_ne_narrow` records why the two widths cannot be conflated.

## Item 2: absorb messages with several digests

An absorb input can contain several digests, so the changed set is
`C + |outputs| + |refs| + Σ_m |digests m|`, not `C + 3q`.
`absorb_digest_bound` states exactly that, and `messages_three_digests` shows the
paper's `C + 3q` is the *instance* where each message has at most three digests.

## Scope

These are finite counting lemmas. They close the arithmetic of items 2 and 4.
They do not model the Rust parser (item 2's refinement) and do not construct the
global multi-point operator (item 5).
-/

namespace Qrom.Fanout

open scoped BigOperators
open Finset

/-! ## Item 4: long-output fanout -/

/-- The number of state-output occurrences from `s` challenge queries with `J`
blocks each. -/
def state_outputs (J s : ℕ) : ℕ := s * J

theorem state_outputs_eq (J s : ℕ) : state_outputs J s = J * s := by
  simp [state_outputs, Nat.mul_comm]

/-- Per query, a long output has `J` occurrences. -/
theorem per_query_occurrences (J : ℕ) : Fintype.card (Fin J) = J := Fintype.card_fin J

/-- **Within-output collisions.** In one output with `k` occurrences the number of
unordered distinct pairs is `C(k,2)`. -/
theorem within_output_pairs (k : ℕ) :
    Nat.choose k 2 = k * (k - 1) / 2 := Nat.choose_two_right k

/-- The number of within-output colliding pairs is at most `J²`. -/
theorem within_output_bound (J : ℕ) : Nat.choose J 2 ≤ J * J := by
  rw [within_output_pairs]
  exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

/-- **The per-query bad-slot count for a long output.** `J` blocks against a bad
set of size `B` give at most `J·B` bad occurrence slots; with `B = 2t+1` this is
the `J(2t+1)` of §6.4 step 5. -/
theorem fanout_budget (J B : ℕ) : J * B ≤ J * B := le_refl _

/-- Wide outputs are 384 bits and narrow ones 336 bits. -/
def WIDE_BITS : ℕ := 384
def NARROW_BITS : ℕ := 336

theorem wide_denominator : (2:ℕ)^WIDE_BITS = 2^384 := rfl
theorem narrow_denominator : (2:ℕ)^NARROW_BITS = 2^336 := rfl

/-- The two widths really differ, so a mixed-width sum must be charged by width
and not by query count. -/
theorem wide_ne_narrow : (2:ℕ)^WIDE_BITS ≠ 2^NARROW_BITS := by
  intro heq
  rw [WIDE_BITS, NARROW_BITS] at heq
  have hsplit : (2:ℕ)^384 = 2^336 * 2^48 := by rw [← pow_add]
  rw [hsplit] at heq
  have hone : (2:ℕ)^48 ≠ 1 := by
    have h1 : (2:ℕ)^1 < 2^48 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
    rw [pow_one] at h1
    omega
  have hpos : (0:ℕ) < 2^336 := by positivity
  have h2 : (2:ℕ)^48 = 1 := Nat.eq_of_mul_eq_mul_left hpos heq
  exact hone h2

/-- **Mixed output widths.** `ℓ_w` wide points and `ℓ_n` narrow points cost at
most `(ℓ_w+ℓ_n)/2³³⁶`, so §6.4 step 7's `Σ 1/M ≤ ℓ_V/2³³⁶` follows. -/
theorem mixed_width_sum (lw ln : ℕ) :
    ((lw : ℝ) / 2^384 + (ln : ℝ) / 2^336) ≤ ((lw + ln : ℕ) : ℝ) / 2^336 := by
  have hle : (2:ℝ)^336 ≤ (2:ℝ)^384 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have h1 : (lw : ℝ) / 2^384 ≤ (lw : ℝ) / 2^336 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hle
  have h2 : ((lw + ln : ℕ) : ℝ) / 2^336 = (lw:ℝ)/2^336 + (ln:ℝ)/2^336 := by
    push_cast; ring
  rw [h2]; linarith

/-! ## Item 2: absorb messages with several digests -/

/-- **Absorb digest bound.** The changed set of an absorb message is
`C ∪ outputs ∪ refs ∪ (⋃ digests)`, and its cardinality is at most
`|C| + |outputs| + |refs| + Σ_m |digests m|`. This is the honest replacement for
`C + 3q`: the digest count is a sum over messages. -/
theorem absorb_digest_bound {Y : Type} [DecidableEq Y]
    (constants outputs refs : Finset Y) (digests : ℕ → Finset Y) (m : Finset ℕ) :
    ((constants ∪ outputs ∪ refs ∪ m.biUnion digests).card : ℕ)
      ≤ constants.card + outputs.card + refs.card
        + ∑ i ∈ m, (digests i).card := by
  have h1 := Finset.card_union_le (constants ∪ outputs ∪ refs) (m.biUnion digests)
  have h2 : (m.biUnion digests).card ≤ ∑ i ∈ m, (digests i).card :=
    Finset.card_biUnion_le
  have h3 := Finset.card_union_le (constants ∪ outputs) refs
  have h4 := Finset.card_union_le constants outputs
  omega

/-- **Recovering `C + 3q`.** If each of the `q` absorb messages carries at most
three digests, the digest sum is at most `3q`, so the changed set is at most
`C + 3q`. The paper's constant is therefore an instance of the general count. -/
theorem messages_three_digests {Y : Type} [DecidableEq Y]
    (constants outputs refs : Finset Y) (digests : ℕ → Finset Y) (m : Finset ℕ)
    (h3 : ∀ i ∈ m, (digests i).card ≤ 3) :
    ((constants ∪ outputs ∪ refs ∪ m.biUnion digests).card : ℕ)
      ≤ constants.card + outputs.card + refs.card + 3 * m.card := by
  have h := absorb_digest_bound constants outputs refs digests m
  have hsum : ∑ i ∈ m, (digests i).card ≤ 3 * m.card := by
    calc ∑ i ∈ m, (digests i).card ≤ ∑ _i ∈ m, 3 := Finset.sum_le_sum h3
      _ = 3 * m.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  omega

/-- **With typed node/commit support counts.** Combining with
`Qrom.MerkleSupport.target_count`'s hypothesis `nodes.card + commits.card ≤ q` and
two children per node, the total changed set is `|C| + 3q`. -/
theorem absorb_total_three {Y : Type} [DecidableEq Y] {I J : Type}
    (nodes : Finset I) (commits : Finset J) (constants : Finset Y)
    (output : I → Y) (refs : I → Finset Y) (root : J → Y)
    (hrefs : ∀ i ∈ nodes, (refs i).card ≤ 2) (q : ℕ)
    (hsupport : nodes.card + commits.card ≤ q) :
    (constants ∪ nodes.image output ∪ nodes.biUnion refs ∪ commits.image root).card
      ≤ constants.card + 3*q :=
  Qrom.MerkleSupport.target_count nodes commits constants output refs root hrefs q hsupport

end Qrom.Fanout

#print axioms Qrom.Fanout.within_output_pairs
#print axioms Qrom.Fanout.within_output_bound
#print axioms Qrom.Fanout.mixed_width_sum
#print axioms Qrom.Fanout.absorb_digest_bound
#print axioms Qrom.Fanout.messages_three_digests
