# QROM bound components and their instantiation boundary

Updated 2026-10-21 after the paper soundness review. Research package using Mathlib;
not part of the admitted `zk-formal` certificate or its package whitelist.

The package proves conditional mathematical lemmas. It does **not** yet prove the
paper's recursive protocol secure, and is not closed except for two cited facts.

## Checked components

| File | Result | Premises and scope |
|---|---|---|
| `Transition.lean` | Three Frobenius block estimates | Actual squared-entry function; finite-entry bound only off diagonal; source/target blocks disjoint. Zero-frequency identity blocks vanish. |
| `Operator.lean` | Complex matrix action bounded by its Frobenius block sum; `complex_block_finite` composes the repaired entry bound | Equality between actual matrix norm squares and `EntryBounds.entry` is explicit. The global compressed-oracle operator is not constructed. |
| `Instantiate.lean` | `mass_recurrence` from contractive operators, idempotent projectors, decomposition and block bounds | Generic normed-space lemma, plus illustrative real coordinate projections. |
| `Path.lean` | `path_bound`: the amplitude is at most `Ahat` | Abstract nonnegative transition weights and initial condition. |
| `FactA.lean` | `Replacement` and `fact_a` use CFHL21's square-root form | The replacement theorem is cited, not proved. Finite counting lemmas do not establish it. |
| `Main.lean` | `PotentialEvolution.recurrence`, `amplitude_bound`, `qrom_bound`, `qrom_binary_bound` | Recurrence is derived from operator premises; measured bad-event probability is bounded by the **squared** projection norm. Result: `p ≤ (Ahat + sqrt slack)^2`, or `(t*g + sqrt slack)^2` for a Boolean potential. |
| `Transcript.lean` | Honest chain edge is not `WideBad`; safe accepting transcript yields a witness | Deterministic part only. No bound on probability of verifier flips is asserted. |
| `MerkleSupport.lean` | Unreferenced node insertion preserves graph reachability; reference targets bounded by `fixedRoots + 3*q` under typed support counts | Native parser/extractor correspondence and wide-query bounds remain open. |
| `OracleBridge.lean` | A fixed concrete output matches one independent uniform oracle output with probability `1/card Y`; acceptance minus that marginal lower-bounds consistency failure | Includes a general probability-space inequality. Protocol fixed-pair occurrence and completeness must still be supplied; no concrete forgery is asserted. |
| `Sampler.lean` | Every accepted residue has exactly two preimages below `2*p`, hence conditional probability `1/p` | Finite counting only; adaptive oracle selection, rejection-loop length and runtime are separate obligations. |
| `Adaptive.lean` | History-dependent bad-set cardinalities give a union bound over uniformly sampled challenge trajectories | Classical uniform challenges; the actual sampler and QROM game still need reduction to this experiment. |
| `Peeling.lean` | Correct scalar peeling bound, regression against the omitted cross term, and quadratic scan count | Simulation, extraction and protocol premises remain explicit. |
| `QueryCost.lean` | Backward-cone cardinality and conditional gate lower bound | Quantum causality and the random-access-code information bound in G-P1-C are not formalized here. |
| `Audit.lean` | Counterexamples to the old probability-additive replacement premise and full-entry matrix model; one-query amplitude regression; axiom output | Included in the default build. |
| `Instance.lean` | Complex database-register Hilbert space; coordinate projections (real and complex linear), idempotence, contraction, nesting | One oracle point. No adversary workspace or Fourier register. |
| `Reflection.lean` | Reflection in `ℂ ∙ w` with `‖w‖² = 2`: a **real linear isometry** whose squared entries are `0, 1/M, 1/M, 1/M² ≤ 9/M²`, so `EntryBounds` is inhabited by an actual unitary; exact rank-one block identity; `Chg` bound `2|Chg|/M` | The operator is the one-point `cO_{xŷ}`, not the lifted `Σ_{x,ŷ} \|x,ŷ⟩⟨x,ŷ\| ⊗ cO_{xŷ}`. |
| `ConcreteInstance.lean` | `concreteEvolution`: a `PotentialEvolution` with every field discharged; `concrete_qrom_bound` applies `qrom_binary_bound` end to end, with the measured-event inclusion **proved** (`le_refl`) rather than assumed | The level function and `Chg` are supplied, not the transcript potential. One repeated query operator. `Replacement` remains cited. |
| `Extraction.lean` | Canonical extraction as a filter on `(digest, children)` nodes: singleton uniqueness, insert-fresh, erase, replace, and the two honest children-reassignment statements | A model of the database; no refinement from the Rust parser. |
| `Fanout.lean` | Long-output occurrence counts, `C(k,2)` within-output pairs, `J(2t+1)` fanout, mixed-width `≤ ℓ/2³³⁶`, and the absorb digest sum that yields `C + 3q` only when each message has at most three digests | Counting only; the counts still have to enter a lifted operator's `G`. |

No new axioms or `sorry` are used. Kernel axioms are `propext`, `Classical.choice`,
and `Quot.sound` (some results use fewer).

## What changed in the repair

1. The old `qrom_bound` assumed `p' ≤ Ahat`, did not use its computed mass bound,
   and confused an amplitude with a probability. The new theorem actually uses
   the operator-derived recurrence and projection-event relation.
2. CFHL21 Corollary 4.2 states `sqrt p ≤ sqrt p' + sqrt(ℓ/N)`;
   it does not state `p ≤ p' + ℓ/N`. The cross term is retained.
3. CFHL21 Lemma 4.3 bounds finite **off-diagonal** entries by `3/M`.
   Diagonal entries are unrestricted by this bound, and the zero-frequency
   query is the identity. The old constant-entry model could not be unitary.
4. A state output used as the next input is a legitimate transcript edge.
   Only distinct-output collisions and return to the initial state enter the
   illustrative `WideBad` predicate. A full family potential must also include
   narrow collisions and first verifier flips, with canonical extraction defined.

## Remaining protocol work

To instantiate `PotentialEvolution` for the paper, construct or rigorously reduce:

* the complex compressed-oracle state, including adversary workspace and Fourier
  query register; support bounds and commutation with database projectors;
* a finite, canonically framed verifier family, and unambiguous transcript parsing;
* canonical Merkle extraction and the Boolean potential on all database states,
  including deletion/reassignment of entries;
* every block estimate for that potential (absorb, narrow, long-output challenge,
  zero-frequency), with exact root counts and long-output fanout;
* the measured-event inclusion, plus a valid invocation of CFHL21 replacement
  for adaptive verifier queries and mixed output widths;
* the resulting numerical constants and a separate recursive hash-model bridge.

`EntryBounds` and `Replacement` are two external interfaces, but the list above
contains additional protocol-specific obligations. No theorem here discharges them
by naming them. `Main.lean` exposes this boundary explicitly.

**Partial progress (2026-10-21, `lane/pq-family-qrom`).** The list above is no
longer entirely open:

* `EntryBounds` is now *inhabited*: `Reflection.qopEntries` is the squared-entry
  function of an explicit complex linear isometry.
* `PotentialEvolution` has a compiled instance (`ConcreteInstance`), with the
  measured-event inclusion proved rather than assumed, and a `Chg` block
  constant of `2|Chg|/M` instead of the interface's `10|Chg|/M`.
* Canonical extraction is defined and its insertion/deletion/reassignment
  behaviour is proved on a node model (`Extraction`).
* Long-output fanout, the mixed-width sum, and the per-message absorb digest
  count are proved as arithmetic (`Fanout`), making `C + 3q` an instance.

Still open: the global multi-point compressed-oracle operator and its commutation
with database projectors, the base layer's state function, the Rust parser
refinement, and `Replacement` itself. See
`../../../docs/logs/pq-family-qrom-2026-10-21.md` for the item-by-item table.

## Validation

The 2026-10-21 family-instantiation build passes (**8,728 jobs**); source
hashes and scope are recorded in `VALIDATION.json`. The `lane/pq-family-qrom`
track adds five modules (`Instance`, `Reflection`, `ConcreteInstance`,
`Extraction`, `Fanout`); the earlier figure in this line (8,722) predates them. Run `lake build` in this directory. `Qrom.Audit` is a default-library import, so
its regression proofs and axiom checks are included. On the shared development
host use the repository's `heavy` wrapper and reserved non-benchmark CPUs.
The pinned Mathlib path in `lakefile.toml` is machine-local; clean standalone
reproduction also requires packaging that dependency pin.

Primary reference: Chung–Fehr–Huang–Liao, [Corollary 4.2 and Lemma 4.3](https://arxiv.org/pdf/2010.11658).

### Tight-height kernel component

`Qrom/Stacking.lean` proves the exact univariate-skip chunk rotation correction
at arbitrary evaluation points, including Boolean predecessor wraparound.
`STACKING-VALIDATION.json` records the checked declarations and pinned backend
source hashes. The source mapping is in `final-soundness/PROOF.md` §3.7.
This is a polynomial theorem; the Rust/NV execution connection remains open.
