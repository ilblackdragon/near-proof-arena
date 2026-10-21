# Re-check of the four remaining paper blockers (2026-10-21)

Scope: verify, against the actual artifacts, the four blockers named after the
`fix/pq-paper-soundness` review:

1. actual family-QROM instantiation
2. full WHIR composition
3. arbitrary-trace NV/base semantics
4. a justified recursive hash bridge

Branch state: paper branch `fix/pq-paper-soundness` @ `84bf5c73e`; `main` @
`d030cd4b5`. The paper branch is 14 commits behind main and touches disjoint
files, so `git merge-tree` reports **no conflicts**. Main carries the host
work (`wasm_base_exec_host`, `host_hst`, `host_hch`) the NV/base track needs.

## 0. What the audited paper now claims (and does not)

The 2026-10-21 draft is honest: `security_established: false` in
`research/qrom/VALIDATION.json` and `final-soundness/lean/G2-VALIDATION.json`,
and `calc/bound.py --require-security` / `audit_g2.py --require-security`
exit 2. The headline is a target, not a result. That is correct and must not
be weakened or "restored" by any of the tracks below.

## 1. Family-QROM instantiation — OPEN, and the gap is concrete

Proved and checked (`research/qrom`, Mathlib, 8,723 jobs, axioms ⊆
{propext, Classical.choice, Quot.sound}):

* `Transition.lean` — three Frobenius block estimates on the **squared-entry**
  function; off-diagonal `3/M`, disjointness hypotheses, zero-frequency
  identity block vanishes.
* `Operator.lean` — complex matrix action bounded by Frobenius block sum;
  `complex_block_finite` composes the repaired entry bound.
* `Instantiate.lean` — `mass_recurrence` from contractive operators,
  idempotent projectors, decomposition, block bounds.
* `Path.lean` — `path_bound` (`a_t ≤ Â_t`).
* `Main.lean` — `PotentialEvolution.recurrence`, `amplitude_bound`,
  `qrom_bound`, `qrom_binary_bound`; result is
  `p ≤ (q·g + √slack)²` — amplitude vs probability kept distinct.
* `Transcript.lean` — `honest_edge_not_bad` (counterexample to the withdrawn
  predicate), `first_flip_extract` (deterministic K1/K2/K4 only).
* `MerkleSupport.lean` — `orphan_preserves_reach`, `target_count`
  (`|constants ∪ outputs ∪ refs| ≤ C + 3q` under typed support counts).
* `FactA.lean` — `Replacement` interface (CFHL21 Cor 4.2 square-root form).
* `Sampler.lean`, `Adaptive.lean`, `Peeling.lean`, `QueryCost.lean`,
  `OracleBridge.lean`, `Stacking.lean`, `Audit.lean`.

Missing, and this is the blocker in its precise form (`PROOF.md` §6.4,
"what must be proved before substituting a numerical g", 5 items):

* the **global compressed-oracle operator** for this verifier family: the
  state lives in a complex Hilbert space including adversary workspace and
  the Fourier query register; support bounds and commutation with database
  projectors are not constructed;
* the **family instantiation** of `PotentialEvolution`: `G i j`, `q`, the
  measured event and the replacement premise are parameters, not derived;
* the **measured-event inclusion** — failed extraction contained in the bad
  subspace — is a hypothesis (`hmeasured`);
* canonical Merkle extraction under insertion/deletion/reassignment of one
  entry (only reachability and a cardinality bound are proved);
* long-output fanout: up to `Jq` state-output occurrences, and
  within-output collisions, unaccounted;
* `Replacement` itself is cited, not proved (CFHL21 Cor 4.2).

So the size of the gap: the *algebraic skeleton* is machine-checked, the
*protocol instantiation* is entirely absent. `VALIDATION.json` says exactly
this.

## 2. Full WHIR composition — OPEN, and this one is worse than the paper's
phrasing

New on the paper branch:

* `final-soundness/lean/DKTWhirFold.lean` — `backendFold_eq` identifies the
  backend's `binary_k_fold` algebra with ArkLib's `binaryFoldedWord`;
  `primitiveSquareDomain` builds a `SquarePairedDomain` from any even-order
  coset; `cosetMajorSquareDomain` handles the `a·h+u` root layout.
* `DKTG2FoldCerts.lean` — 13 kernel-checked measured-FINAL scalar fold
  certificates.
* `DKTG2FoldTransfer.lean` — 13 scalar transfers, each with a parent
  reconstruction, plus `finalScalarFoldBudget_fraction_lt`
  (`sum/|Ext12| < 2^-283`).
* `check_g2_folds.sh` pins ArkLib `a5aa2677fee4` and asserts the axiom set.

Also corrected on the paper branch: `zk-formal/ZkFormal/Udr/McaToGap.lean` is
**demoted** — its header now says the file is a unique-decoding utility, that
`mca_count_to_gap` is a definitional restatement, that `strong_from_mca`
needs `2e < d` (so it cannot apply at Johnson radii), that `fold_union` is
arithmetic on supplied bounds, and adds
`johnson_example_not_unique` as a kernel regression. That is the right
correction: the previous "S-28 lift done" claim in the obligation ledger is
now known to have over-read the file.

Missing:

* **adaptive composition.** The 13 transfers are separate scalar folds. There
  is no theorem that conditioning on earlier random challenges preserves the
  per-fold bounds; `fold_union` explicitly does not establish that.
* **all rounds, all subcodes.** Only the measured FINAL's selected folds are
  covered. Inner layers, round 0 batching curves and the other sub-codes are
  not transferred.
* **ordered coset identification.** `cosetMajorSquareDomain` is an abstract
  construction; the mapping to the backend's concrete integer index
  operations and generator constants is unproved (stated in the file).
* **interleaving and list products** (DKT26 Cor 7.7/7.8 direction) for the
  actual subcodes.
* **the round-by-round state**: WHIR's per-move terms still have nothing that
  consumes the RS-level results. The 2^-283 figure is a **scalar budget for
  one layer's folds**, not a total security bound — the paper says so.

## 3. Arbitrary-trace NV/base semantics — OPEN, no Lean model of NV exists

`research/near-compression/results/pq-recursion-nv/FAITHFUL.md` now opens with
a review header: it is "a source audit and test record, not a completed
accepted-trace-to-execution theorem", with a six-component table (SHA/GLUE,
transcript, program/public tape, verifier arithmetic, LogUp, composition).
`FAITHFUL.md` is right that tamper tests cannot discharge the implication.

Confirmed by inspection:

* there is **no Lean model of the NV AIR at all** — no `NvAir` value, no
  constraint list, nothing in `zk-formal` or `research/near-compression`;
  `grep -rln "NvAir\|NvCircuit"` over `*.lean` returns nothing;
* so "the NV circuit arithmetises `V_{i−1}`" (Lemma 7.1 F1–F6) cannot be
  stated, let alone proved;
* `Qrom.Stacking` proves the tight-chunk univariate-skip rotation identity as
  a **polynomial** theorem; the mapping to the pinned Rust (`poly_common.rs`,
  `stacked_pcs.rs`, `stacked_reduction.rs` hashes recorded in
  `STACKING-VALIDATION.json`) is a written mapping, not a formal refinement.

Base side, now further along on main (not on the paper branch):

* `wasm_base_exec_host` proved, with `hst` (`host_hst`) and `hch`
  (`host_hch`) discharged from `Holds`; `HostBus.lean` has the
  `actListHost` split lemmas. `wasm_base_sound_host` — the packaged
  statement — still does not exist;
* `hostActRows` was silently selecting **no** host rows (`rowAct (chipT 22)`
  is `default`, not `Host.table`); fixed in `47630d6c5`. That bug would have
  made the theorem vacuous over host traces;
* `HOSTB` `(ptr,len)`, `RealStoreMatchesTables`, `UpsV3AppliesLog` still open
  (`docs/HANDOVER.md` lanes 6–7).

## 4. Recursive hash bridge — OPEN, and the paper's rewrite is a *negative*
result, not a plan

The paper branch withdraws Assumption 7.3 as a justification: "adding a time
cap does not justify that identification". `Qrom.OracleBridge` proves the
finite marginal argument (`consistent_card`, `acceptance_le_failure_add_fiber`,
`consistency_probability`, `bridge_failure_lower_bound`,
`bridge_failure_measure`) — i.e. for a fixed pair `(m, SHA384(m))` an
independent oracle agrees with probability `2^-384`, so literal A-IC is not
recoverable by capping runtime. `aic-research/LEMMA.md` §0 and §6 now mark
Theorem O as conditional (H-ex(C), recursive-witness completeness, outer
completeness) and G-P1-C as a written-but-unformalised quadratic gate bound.

So the four possible endpoints the paper lists are:

* (a) an outer-layer QROM reduction to **computational** soundness of the
  concrete inner system, with the extractor's efficiency and full simulation
  cost charged — no such reduction exists, and `Peeling.bound` is only the
  scalar shape;
* (b) a new construction where the inner verification relation and the oracle
  semantics are linked by a theorem — not designed, not measured;
* (c) an explicit assumption named as such, giving a conditional endpoint —
  acceptable but must not be called "proven recursive security";
* (d) an idealized arithmetized-oracle model with a valid reduction — i.e.
  prove `A-IC` for a *specified* model rather than identify concrete SHA-384.

None of these is a proof today. This track is research, and its honest
deliverable is a decision among (a)–(d) with the loss quantified, not a
theorem.

## 5. What is *not* a blocker, and should be explicitly de-scoped

* NEAR-specific join, contract-data storage, `Joint → RelD3`, Ed25519:
  instance-only. The paper is scoped to the tail and says so. Do not let a
  track spend time here.
* Program pinning: implemented, tested, and its necessity is a proved
  proposition (`Proposition 7.3`) plus the measured 776-row forgery.
* The `293,077 B` size measurement: valid as a measurement with binding on.
  It is not a security statement.
* G-P1-C: a limitation on one simulator model, already written as a
  conditional lower bound. Reviewing it is useful; treating it as a proof of
  necessity is not.

## 6. Track split and shared ground rules

| track | branch | worktree | package | deliverable |
|---|---|---|---|---|
| A family-QROM | `lane/pq-family-qrom` | `nearproof-wt/pq-family-qrom` | `research/qrom` (Mathlib) | a concrete family instantiation *or* a precise statement of what cannot be instantiated and why |
| B WHIR transfer | `lane/pq-whir-transfer` | `nearproof-wt/pq-whir-transfer` | ArkLib companion + `final-soundness/lean` | all measured FINAL subcodes + adaptive composition, or the exact missing bridge |
| C NV/base semantics | `lane/pq-nv-faithful` | `nearproof-wt/pq-nv-faithful` | `wasm-base-lean`, `zk-formal` | a Lean NV AIR model and an accepted-trace statement, or the reason a model is out of reach |
| D hash bridge | `lane/pq-hash-bridge` | `nearproof-wt/pq-hash-bridge` | `research/qrom` | a decided endpoint (a)–(d) with quantified loss and an explicit assumption ledger row |

Ground rules for every track:

1. **Never weaken or "repair" the security conclusion.** `security_established:
   false` stays until a theorem exists. If a premise cannot be discharged,
   state it as a named premise; do not rename it `faithful` and call it done.
2. Axioms ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no
   `native_decide`, no custom axioms in any file that a claim depends on.
3. Do not re-pin ArkLib or Mathlib. ArkLib stays at `a5aa2677fee4`.
4. Builds: `export PATH=$HOME/.elan/bin:$PATH`; heavy builds through
   `/data/illia/nearproof-deps/bin/heavy` with `HEAVY_MEM`, pinned to
   CPUs `8-15,24-31` (0–7 and 16–23 belong to the live benchmark worker).
5. Do not edit `formulacheck` pins, `challenges/`, `oracle/v3`, or another
   track's files. Progress notes go to `docs/logs/`, one file per track.
6. Report the *distinction between checked components and a closed theorem*
   in the deliverable, in the same style the audited draft now uses.
