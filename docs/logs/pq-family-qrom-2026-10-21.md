# Family-QROM instantiation: what is now checked, and what a real instance still needs

Track A of `docs/logs/pq-paper-blockers-recheck-2026-10-21.md` §6.
Branch `lane/pq-family-qrom`, based on `fix/pq-paper-soundness` @ `84bf5c73e`.

`security_established` in `research/qrom/VALIDATION.json` remains **false**.
Nothing here proves the fixed G2 verifier family sound. What changed is that the
abstract `PotentialEvolution` skeleton now has a *checked instance* on a small
model, and three of the five PROOF §6.4 gaps are closed as arithmetic or as
statements about a named object instead of being parameters.

## 0. Reproduction (do this first)

```
cd research/qrom
export PATH=$HOME/.elan/bin:$PATH
HEAVY_MEM=8G taskset -c 8-15,24-31 /data/illia/nearproof-deps/bin/heavy lake build
```

Observed: **8,728 jobs**, `Build completed successfully`, Mathlib from the pin in
`lakefile.toml`. Before this track the count was 8,723 (the re-check log's
figure); the five new modules add five jobs. `#print axioms` on every claim this
log relies on gives

| declaration | axioms |
|---|---|
| `qrom_bound`, `qrom_binary_bound`, `complex_block_finite`, `fact_a` | `[propext, Classical.choice, Quot.sound]` |
| `Transcript.first_flip_extract` | `[propext]` |
| `qopEntries`, `qr_contract`, `qop_apply_apply`, `block_chg_sq` | `[propext, Classical.choice, Quot.sound]` |
| `concreteEvolution`, `concrete_qrom_bound`, `level_decompose`, `block_norm` | `[propext, Classical.choice, Quot.sound]` |
| `Extraction.extract_insert_fresh`, `extract_erase`, `extract_replace`, `children_reassign_unrelated`, `children_reassign_own` | `[propext, Classical.choice, Quot.sound]` |
| `Fanout.within_output_pairs`, `within_output_bound` | `[propext]` |
| `Fanout.mixed_width_sum`, `absorb_digest_bound`, `messages_three_digests` | `[propext, Classical.choice, Quot.sound]` |

No `sorry`, no `axiom`, no `native_decide`, no `implemented_by` in
`research/qrom/Qrom/`. `Qrom/Reflection.lean`, `Qrom/ConcreteInstance.lean`,
`Qrom/Extraction.lean` and `Qrom/Fanout.lean` carry `#guard_msgs`-checked
`#print axioms` lines in the style of `Qrom/Audit.lean`.

## 1. What was built

### 1.1 An explicit unitary whose entries are CFHL21 Lemma 4.3's

`Qrom/Instance.lean` and `Qrom/Reflection.lean`.

* `H M = EuclideanSpace ℂ (Option (Fin M))` is the database register at one
  oracle point. `cproj` is the coordinate projection; `cproj_idem`,
  `norm_sq_cproj`, `norm_cproj_le`, `norm_cproj_mono` and the real-linear
  `cprojR` (with `cprojR_contract`, `cprojR_idem`) are proved.
* `wvec M` is `w none = 1`, `w (some r) = -(√M)⁻¹`, so `‖w‖² = 2`
  (`wvec_norm_sq`).
* `qop M` is Mathlib's `Submodule.reflection` in `ℂ ∙ w`. Because it is a
  reflection, **it is a linear isometry by construction**, not by a bounded-entry
  assumption. This is the concrete answer to
  `Qrom.Audit.old_entry_model_not_unitary`: there really is a unitary with this
  entry shape.
* `qr M` is `qop M` restricted to real scalars; `qr_norm_map` and
  `qr_contract` (`‖qr M‖ ≤ 1`).
* `qop_single_apply` gives the components on a basis vector,
  `⟨u|qop|r⟩ = conj (w r) · w u − δ_{ur}`, hence squared entries
  `0` on `(⊥,⊥)`, `1/M` on `(⊥,r)` and `(u,⊥)`, and `1/M²` off the diagonal of
  `Y × Y` (`entry_none_none`, `entry_none_some`, `entry_some_none`,
  `entry_some_some_le`).
* `qopEntries M hM : EntryBounds M` packages exactly those. **`EntryBounds`,
  which `Qrom.Transition` and `Qrom.Operator.complex_block_finite` consume, is now
  inhabited by an actual complex linear isometry.**

### 1.2 The exact block identity, and a 5× better `Chg` constant

Because `qop` is a rank-one update of `−I`, on disjoint level sets the `−I` part
is killed and the block norm is *exactly* `‖w|_S‖·‖w|_T‖`, not a Frobenius bound:

* `block_norm_sq` — exact identity.
* `block_le` — `≤ ‖w|_S‖²‖w|_T‖²‖x‖²` via Cauchy–Schwarz.
* `block_chg_sq` — with `κ` constant off `Chg`, the squared block between levels
  `i < j` is at most `2|Chg|/M`. CFHL21 Lemma 1's changed-set consequence is
  `10|Chg|/M`; the improvement is real and comes from using the actual
  rank-one structure rather than the entrywise `9/M²` bound.
* `weight_le_two`, `weight_of_no_bot`, `sum_no_bot` are the weight facts.

### 1.3 A compiled `PotentialEvolution` — the main deliverable

`Qrom/ConcreteInstance.lean`.

`concreteEvolution M hM lev hlev0 Chg hstable : PotentialEvolution (H M) G` with
`G i j = if i < j then √(2|Chg|/M) else 0`. **Every field is discharged:**

| field | source |
|---|---|
| `tail`, `exactLevel` | `cprojR` of `j ≤ lev r` and `lev r = i` |
| `tail_contract`, `exact_idem` | `cprojR_contract`, `cprojR_idem` |
| `decompose` | `level_decompose` (proved spectral decomposition by levels) |
| `exact_le_tail` | `norm_cproj_mono` |
| `step`, `step_contract` | `qr M`, `qr_contract` |
| `ψ`, `evolves` | iterates of `qr M` on `initVec M` (all-undefined at one point) |
| `init` | `initVec_norm` plus `Ahat G 0 j`, by cases on `j = 0` |
| `block` | `block_norm` from `block_chg_sq` |

`concrete_qrom_bound` then applies `qrom_binary_bound`:
`p ≤ (t·√(2|Chg|/M) + √slack)²` whenever `Replacement p p' slack` holds for
`p' = ‖tail 1 (ψ t)‖²`.

**Honest scope.** This is one oracle point, one repeated query operator, and an
arbitrary supplied level function. It is not `Σ_{x,ŷ} |x,ŷ⟩⟨x,ŷ| ⊗ cO_{xŷ}`
lifted over `q` points, and `κ` is not the transcript potential. What it does
establish, and what the skeleton previously took as a hypothesis, is that in
this model the measured event *is* the squared projection norm (`hmeasured` is
`le_refl`), so the operator premises really do imply the probability bound
without any extra measured-event assumption.

### 1.4 Canonical extraction (item 2's modelling half)

`Qrom/Extraction.lean`. Nodes are `(out : ι, children : Finset ι)`; `Extract D d`
is the `Finset.filter` of nodes outputting `d`; `Children D d` is the union of
extracted children.

* `extract_unique` — a singleton extraction set is a unique preimage.
* `extract_subset` — monotone in `D`.
* `extract_insert_fresh` — a fresh output becomes the unique preimage at its
  digest and changes no other digest.
* `extract_erase` — deletion removes the node from every extraction set.
* `extract_replace` — "drop one node, insert a fresh one" changes extraction only
  at the new digest.
* `children_reassign_unrelated` / `children_reassign_own` — reassigning children
  is not an extraction-set identity at the reassigned digest (the node object
  changes), but it *is* one for extracted children at every other digest, and at
  the reassigned digest the children become exactly the new set. Those two are
  the true statements; recording them this way is deliberate.

### 1.5 Long-output fanout and absorb counting (items 2 and 4's arithmetic)

`Qrom/Fanout.lean`.

* `state_outputs_eq` — `s` queries at `J` blocks each give `J·s` occurrences.
* `within_output_pairs` — `C(k,2) = k(k−1)/2`; `within_output_bound` — `≤ J²`.
* `fanout_budget` — `J` blocks against a bad set of size `B` give `J·B` slots;
  with `B = 2t+1` this is §6.4 step 5's `J(2t+1)`.
* `wide_denominator`, `narrow_denominator`, `wide_ne_narrow` — 2³⁸⁴ ≠ 2³³⁶.
* `mixed_width_sum` — `ℓ_w/2³⁸⁴ + ℓ_n/2³³⁶ ≤ (ℓ_w+ℓ_n)/2³³⁶`. This *derives*
  §6.4 step 7's `Σ 1/M ≤ ℓ_V/2³³⁶` instead of assuming it.
* `absorb_digest_bound` — the absorb changed set is at most
  `|C| + |outputs| + |refs| + Σ_m |digests m|`.
* `messages_three_digests` — if every message has ≤ 3 digests, that is
  `+ 3q`. So the paper's `C + 3q` is an **instance**, not an assumption.
* `absorb_total_three` — the same, composed with
  `MerkleSupport.target_count`'s typed node/commit support counts.

## 2. The five PROOF §6.4 items, item by item

| # | item | status | what is actually there | what would close it |
|---|---|---|---|---|
| 1 | canonical framing; unique parsed prefix; per-block outputs vs logical moves | **open (modelled in part)** | `Entry`/`WideBad` and `first_flip_extract` (deterministic only); no framing; no parser | A Lean model of the §1.3 framing (vk index, statement, move index, block index) and an injectivity theorem on it. The per-block-vs-move distinction needs §6.4's ordering fixed as data, which is a modelling choice not in this package. |
| 2 | canonical Merkle extraction incl. missing nodes, under insert/remove/reassign; count every root in an absorb message | **proved for the model; open at the parser** | `Extraction.*` (insertion, deletion, replacement, children reassignment) and `Fanout.absorb_digest_bound` / `messages_three_digests` (per-message digest sums, `C + 3q` as an instance) | The refinement from the **actual Rust transcript parser's byte string** to `Finset (Node ι)`, plus a proof that the parser accepts exactly these nodes. That is a Rust/Lean refinement, not available here, and not attempted. |
| 3 | narrow query uses disjoint entries; absorb/challenge matches are local extensions, not global bad edges | **proved (disjoint case)** | `block_chg_sq` gives `2|Chg|/M` for disjoint levels with the concrete unitary; `honest_edge_not_bad` is the local-extension counterexample to the old predicate | The *absorb/challenge* transitions at the multi-point level: the block estimate there is about a different operator position, and needs the lifted `cO_{xŷ}` and the potential's own stability analysis. |
| 4 | long-output fanout: `J·q` occurrences, within-output collisions, 2³⁸⁴ per output | **proved (arithmetic)** | `state_outputs_eq`, `within_output_pairs`, `within_output_bound`, `fanout_budget`, `wide_ne_narrow`, `mixed_width_sum` | Nothing extra for the count. What remains is item 5: putting these counts inside the lifted operator's `G`. |
| 5 | uniform `g` for the family incl. base layer; measured-event inclusion; replacement for adaptive accesses and mixed widths | **open** | `concrete_qrom_bound` proves inclusion + `G` for the one-point model; `mixed_width_sum` proves the width part; `Replacement` is still the cited interface | The global compressed-oracle operator on `Fin q → DB M` with the Fourier query register and adversary workspace, its commutation with database projectors, and CFHL21 Cor 4.2 for adaptive access. Also the base layer's own state function. None of this is in the package, and `Replacement` remains cited, not proved. |

So: 2 and 4 are closed as arithmetic/statements about a named object; 3 is
closed in the disjoint (narrow) case; 1 and 5 are open, and 2 still lacks the
parser refinement.

## 3. What this does *not* say

* No numeric `g` is offered as security. `G i j = √(2|Chg|/M)` here is a one-point
  model constant with `Chg` a parameter; substituting it into a bit bound would be
  exactly the overclaim the paper review removed.
* `Replacement` (CFHL21 Cor 4.2) is still an interface. `replacement_not_additive`
  in `Qrom/Audit.lean` still records that the old additive premise was wrong.
* No Rust, no wasm, no G2 verifier. The one-point model is a model.

## 4. Points where the audited paper over- or under-states the state

* **Under-states:** §6.4's "`|Chg| ≤ 3t′`" is presented as the only counting
  issue, but the real absorb issue is a *per-message digest sum*. The paper's
  three-digest constant is fine for the current transcript, but the theorem as
  written reads as if it were forced. `Fanout.messages_three_digests` makes the
  dependency explicit. Item 2's extractor is also stated to "read π's transcript
  from D", which needs the insertion/deletion/reassignment analysis the paper does
  not spell out; that analysis is what `Extraction` now supplies for a model.
* **Over-states:** the PROOF §6.4 proof sketch says "By ANALYSIS Lemma 1 (CFHL21
  Lemma 4.3 entries …) its 'Chg consequence' gives `‖Π cO Π‖² ≤ 10|Chg|/2³³⁶`."
  That is a Frobenius bound on a matrix *interface*. For the actual unitary the
  constant is `2|Chg|/M` (`block_chg_sq`), so the sketch is conservative rather
  than wrong — but it also silently assumes the entry interface is inhabited,
  which until this track it was not.
* **Correctly stated:** `security_established: false`; `fact_a` is cited, not
  proved; the NV and hash-bridge tracks are unrelated and untouched.

## 5. Files

New: `Qrom/Instance.lean`, `Qrom/Reflection.lean`, `Qrom/ConcreteInstance.lean`,
`Qrom/Extraction.lean`, `Qrom/Fanout.lean`. `Qrom.lean` imports all five.
No Mathlib/ArkLib pin changed; no `final-soundness/lean/*` or
`wasm-base-lean/*` file touched.
