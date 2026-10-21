import Mathlib

/-!
# Backward-cone gate counting for G-P1-C

Only the finite circuit-cone count is formalized here. The quantum causal-cone
interpretation and random-access-code information bound are stated and proved/
cited in aic-research/LEMMA.md; they are not formalized by this module.
-/
namespace Qrom.QueryCost
variable {W : Type} [DecidableEq W]

def step (cone gate : Finset W) : Finset W :=
  if (cone ∩ gate).Nonempty then cone ∪ gate else cone

theorem step_card (cone gate : Finset W) (hg : gate.card ≤ 2) :
    (step cone gate).card ≤ cone.card + 1 := by
  unfold step
  split_ifs with h
  · have hi := Finset.card_pos.mpr h
    have hu := Finset.card_union_add_card_inter cone gate
    omega
  · omega

def traceBack (cone : Finset W) : List (Finset W) → Finset W
  | [] => cone
  | gate :: rest => traceBack (step cone gate) rest

theorem traceBack_card (gates : List (Finset W))
    (h : ∀ gate ∈ gates, gate.card ≤ 2) (cone : Finset W) :
    (traceBack cone gates).card ≤ cone.card + gates.length := by
  induction gates generalizing cone with
  | nil => simp [traceBack]
  | cons gate rest ih =>
    have hg := h gate (by simp)
    have hr := ih (fun g hm => h g (by simp [hm])) (step cone gate)
    have hs := step_card cone gate hg
    simp only [traceBack, List.length_cons]
    omega

/-- Conditional on the information lower bound, an output cone cannot recover
n independent bits with fewer than n-1 two-wire gates. -/
theorem gates_lower_bound (gates : List (Finset W))
    (h : ∀ gate ∈ gates, gate.card ≤ 2) (output : W) (n : ℕ)
    (hinfo : n ≤ (traceBack {output} gates).card) : n ≤ gates.length + 1 := by
  have hc := traceBack_card gates h {output}
  simp only [Finset.card_singleton] at hc
  omega

/-- The same argument for a fixed multi-bit answer register. -/
theorem gates_lower_bound_many (gates : List (Finset W))
    (h : ∀ gate ∈ gates, gate.card ≤ 2) (outputs : Finset W) (n : ℕ)
    (hinfo : n * outputs.card ≤ (traceBack outputs gates).card) :
    (n - 1) * outputs.card ≤ gates.length := by
  have hc := traceBack_card gates h outputs
  rw [Nat.sub_mul, one_mul]
  omega

/-- Cost-model consequence for 2^64 calls and 336-bit outputs, using half
for the independent prefix and half for repeat queries. -/
theorem headline_cost_exceeds_time_cap :
    2^128 < 336 * (2^63 : ℕ) * (2^63 - 1) := by norm_num

end Qrom.QueryCost
#print axioms Qrom.QueryCost.traceBack_card
#print axioms Qrom.QueryCost.gates_lower_bound

#print axioms Qrom.QueryCost.gates_lower_bound_many
#print axioms Qrom.QueryCost.headline_cost_exceeds_time_cap
