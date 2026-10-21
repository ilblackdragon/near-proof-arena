import ArenaCore.Security.Prob

/-!
# ArenaCore.Bridge.BridgeCost — what "the reduction runs in time τ" has to mean

`PROOF.md` §6.3 Lemma 6.3 says a `t`-query algorithm with oracle access to `H`
can be simulated by a **`2t`-query** algorithm with oracle access to the
counter-mode function `G(κ) = (H(5, κ‖1), …, H(5, κ‖J))`. `PROOF.md` §7.3 and
paper §C.3 state the corresponding warning: the `q → 2q` substitution does not
by itself preserve a *running-time* bound, and the old `τ = 2^128` number is
not enough until the simulation cost is charged.

This file makes that warning arithmetic. It is a **cost model**, not a theorem
about the implementation:

* `simBlocks J t` — counter-mode simulation of `t` queries needs `2·J·t`
  oracle-block evaluations (produce `J` blocks into the ancilla, XOR, uncompute
  with a second `J`-block evaluation). `Lemma 6.3`'s "`2t` queries" counts
  *`G`-calls*, not the `J` blocks each `G`-call expands to; the ratio is `J`.
* `totalCost` — the reduction's charged cost: adversary time, initialisation,
  simulation (block evaluation plus one database touch per query), measurement,
  and extraction. This is the shape `PROOF.md` §7.3 / `LEMMA.md` §5 give.

The two proved comparisons below are deliberately opposite in direction, and
both matter for honesty:

* `blockCost_fits_128` — at `t = 2^64`, `J = 2^20`, counter-mode simulation costs
  `2^85` block evaluations, which **is** within a `2^128` budget. So a `τ = 2^128`
  claim is *not* refuted by the simulation cost alone;
* `headline_gate_bound_exceeds_128` (restated from `research/qrom`) — the
  *universal exact fixed-interface circuit* simulator of G-P1-C needs
  `336·2^63·(2^63−1) > 2^128` two-qubit gates at `q = 2^64`, `336`-bit outputs.

The two statements are about different resources (oracle-block evaluations in a
query model vs. ordinary two-qubit gates in a causal-cone model). The honest
conclusion is therefore narrow: `τ = 2^128` cannot be justified by counting
queries, needs the simulation cost *and* the database/extraction cost charged
explicitly, and is contradicted in the G-P1-C model but not by the block count.
-/

namespace ArenaCore.Bridge

/-- Oracle-block evaluations for counter-mode simulation of `t` queries with
`J` blocks per challenge: produce `J`, XOR, uncompute `J`. -/
def simBlocks (J t : Nat) : Nat := 2 * J * t

/-- The `q → 2q` query substitution, in `G`-calls: `2t`. -/
def simCalls (t : Nat) : Nat := 2 * t

/-- The reduction's charged cost, in the shape of `PROOF.md` §7.3:
adversary time `T_A`, initialisation, block-evaluation simulation, one database
touch per simulated query, measurement, extraction. -/
def totalCost (T_A T_init J t T_measure T_extract : Nat) : Nat :=
  T_A + T_init + simBlocks J t + t + T_measure + T_extract

/-- The `2t` figure counts `G`-calls; the block count is `J` times larger. -/
theorem simBlocks_eq_J_mul_calls (J t : Nat) : simBlocks J t = J * simCalls t := by
  unfold simBlocks simCalls
  rw [← Nat.mul_assoc, Nat.mul_comm 2 J, Nat.mul_assoc]

/-- At `t = 2^64`, `J = 2^20`: `2^85` block evaluations. -/
theorem blockCount_at_headline : simBlocks (2 ^ 20) (2 ^ 64) = 2 ^ 85 := by
  unfold simBlocks
  decide

/-- `2^85 ≤ 2^128`: the counter-mode block count is **inside** a `2^128` budget.
So the simulation cost alone does not refute a `τ = 2^128` claim. -/
theorem blockCost_fits_128 : simBlocks (2 ^ 20) (2 ^ 64) ≤ 2 ^ 128 := by
  rw [blockCount_at_headline]
  exact Nat.pow_le_pow_right (by decide) (by decide)

/-- G-P1-C's exact-simulation gate count at `q = 2^64`, `336`-bit outputs:
`336·2^63·(2^63−1)`, which exceeds `2^128`. Restated so the two directions are
visible side by side; the argument is in `aic-research/LEMMA.md` §6. -/
theorem headline_gate_bound_exceeds_128 :
    2 ^ 128 < 336 * (2 ^ 63 : Nat) * (2 ^ 63 - 1) := by
  decide

/-- **Cost accounting is additive and cannot be skipped.** If every charge has
its own bound, the total has the sum. A bound on `q` alone therefore says
nothing about `totalCost` unless the simulation, database, measurement and
extraction slots are bounded too. -/
theorem totalCost_le {T_A T_init J t T_measure T_extract τA τI τS τD τM τE : Nat}
    (hA : T_A ≤ τA) (hI : T_init ≤ τI) (hS : simBlocks J t ≤ τS)
    (hD : t ≤ τD) (hM : T_measure ≤ τM) (hE : T_extract ≤ τE) :
    totalCost T_A T_init J t T_measure T_extract ≤ τA + τI + τS + τD + τM + τE := by
  unfold totalCost
  omega

/-- Consequently: a claimed `totalCost ≤ 2^128` at the headline parameters
requires `T_extract ≤ 2^128 - (2^85 + t + …)`; extraction cannot be treated as
free. Written with extraction and measurement set to `0` to isolate the point. -/
theorem extraction_budget_at_headline_strict {T_extract : Nat}
    (h : totalCost 0 0 (2 ^ 20) (2 ^ 64) 0 T_extract ≤ 2 ^ 128) :
    T_extract ≤ 2 ^ 128 - 2 ^ 85 - 2 ^ 64 := by
  unfold totalCost at h
  rw [blockCount_at_headline] at h
  have h85 : (2:Nat) ^ 85 = 2 * 2 ^ 20 * 2 ^ 64 := by decide
  rw [h85] at h
  omega

end ArenaCore.Bridge

/-! ## Axiom guards -/

#print axioms ArenaCore.Bridge.simBlocks_eq_J_mul_calls
#print axioms ArenaCore.Bridge.blockCount_at_headline
#print axioms ArenaCore.Bridge.blockCost_fits_128
#print axioms ArenaCore.Bridge.headline_gate_bound_exceeds_128
#print axioms ArenaCore.Bridge.totalCost_le
#print axioms ArenaCore.Bridge.extraction_budget_at_headline_strict
