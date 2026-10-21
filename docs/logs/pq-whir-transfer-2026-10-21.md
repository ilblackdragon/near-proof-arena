# WHIR transfer: what is now composed, and where the bridge still breaks (2026-10-21)

Track B of `docs/logs/pq-paper-blockers-recheck-2026-10-21.md` §6.
Worktree `/data/illia/nearproof-wt/pq-whir-transfer`, branch `lane/pq-whir-transfer`,
based on `fix/pq-paper-soundness` @ `84bf5c73e`.

`security_established` stays **`false`**. Nothing below is a security bound. The numbers in
this document are *fold-only scalar budgets for named rounds*, never a total.

---

## 0. Harness reproduction (Step 0)

`research/near-compression/final-soundness/lean/check_g2_folds.sh <ArkLib> <external build dir>`,
run as

```
export PATH=$HOME/.elan/bin:$PATH
research/near-compression/final-soundness/lean/check_g2_folds.sh \
  /data/illia/nearproof-deps/arklib-dkt/ArkLib  /tmp/opencode/g2build
```

Result: **PASS**, exit 0.

| check | result |
|---|---|
| ArkLib pin | `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, working tree clean (`git diff --quiet HEAD`) |
| regeneration, `DKTG2FoldCerts` | byte-identical (`cmp`) |
| regeneration, `DKTG2FoldTransfer` | byte-identical (`cmp`) |
| regeneration, `DKTG2FoldCoverageCerts` | byte-identical (`cmp`) |
| regeneration, `DKTG2FoldCoverage` | byte-identical (`cmp`) |
| dependencies (`BinaryFoldAgreement` + Mathlib closure) | `lake build` OK, 1,993 jobs |
| `DKTG2FoldCerts` | exit 0, 13 declarations, axioms ⊆ {propext, Classical.choice, Quot.sound} |
| `DKTWhirFold` | exit 0, 3 declarations (`backendFold_eq`, `primitiveSquareDomain`, `cosetMajorSquareDomain`), axioms OK |
| `DKTG2FoldTransfer` | exit 0, 14 declarations (13 transfers + `finalScalarFoldBudget_fraction_lt`), axioms OK |
| `DKTAdaptive` | exit 0, 5 declarations, axioms OK |
| `DKTOrderedCoset` | exit 0, 7 declarations, axioms OK |
| `DKTG2FoldCoverageCerts` | exit 0, 14 declarations, axioms OK |
| `DKTG2FoldCoverage` | exit 0, 28 declarations, axioms OK |
| `DKTRoundCompose` | exit 0, 5 declarations, axioms OK |

Total: **89 declarations**, every one with axioms ⊆ {propext, Classical.choice, Quot.sound}.

The harness was **not** broken. It was extended (see §5) to cover the new modules; the
extension is byte-compare-strict in the same way and additionally greps the new sources for
`sorry`, `native_decide`, `implemented_by`.

Two notes from running it:

* `DKTG2FoldCerts` is the expensive module (about 15 GB RSS peak, ~20 minutes). Kernels of the
  size in `DKTCertsO2_*.lean` must be built under `HEAVY_MEM=48G` when the host is otherwise
  busy; 24 GB gets OOM-killed while another agent holds `zkbuild.slice`.
* `maxRecDepth` matters: `decide +kernel` on `31^(p-1)` directly exceeds the kernel's numeral
  limit and recurses. The generator checks in `DKTOrderedCoset.lean` therefore use a repeated
  squaring chain (§4), which keeps every intermediate a bounded field element. Two traps found
  the hard way: a top-level `instance : Fact (Nat.Prime babyBear)` makes Lean unfold the
  primality proof in every later `Field (ZMod p)` search (minutes, then OOM), so the instance is
  kept local; and `decide +kernel` on `31 ^ 134217728` hangs, while `sqChain 31 27` is instant.

---

## 1. Per-move sampling / conditioning table (Step 1)

Sources: `PROOF.md` §6.5, and the **pinned production tree**
`/data/illia/nearproof-deps/pq-stream/stark-backend-unified` at `fc1f9e4` (`release v2.0.1` +
the nearproof base patch), i.e. the tree that has WHIR-Y and the x15 odd-domain patch.
File hashes:

| file | sha256 |
|---|---|
| `crates/stark-backend/src/verifier/whir.rs` | `84634f20d7dfb2fadbd5cb4407104f68a5407c1d417e522421c65b07178510ff` |
| `crates/stark-backend/src/odd_domain.rs` | `427e8d73770cc03beb9b7b1153b9233637f12755a7c492d6065945b294540162` |
| `crates/stark-backend/src/hasher.rs` | `10c530c66d800826597defaab20fcef27fd8c5705404e914351b34df4b6e09c8` |
| `crates/stark-backend/src/config.rs` | `250e5d9f248c6b6daae9f04972e22e68f30c72b2513e50043de4606d5bd60f83` |
| `crates/stark-backend/src/transcript/traits.rs` | (transcript API; `sample_ext` = 12 iid base draws) |

Note this is *not* the `stark-backend/` sub-tree (sha `595f4309…`, no WHIR-Y, no odd-domain);
`PROOF.md:40` and `GAPS.md:63` require the unified tree. `whir.rs` in the unified tree is 541
lines, so the line numbers in the older `PROOF.md` §6.5 table (which range to 326 for γ) are
stale — the table below re-derives them.

Rounds: `k_whir = params.whir.k_round(round)` (`whir.rs:130`), so the FINAL's measured
`(1, 4, 4, 4)` is a runtime value, not a constant in the code.

| # | verifier move | sampled? | from | absorbed / conditioned on | `whir.rs` |
|---|---|---|---|---|---|
| 0 | odd-domain factor | no | constant | `S::F::from_usize(15)` absorbed | 49-52 |
| 1 | μ-PoW witness | no (checked) | prover witness | `check_witness(mu_pow_bits, w)`; bits = 0 in the measured configs (`run.log:45,47`) | 55-57 |
| 2 | **μ** (column batching) | yes | `Ext12` uniform, `sample_ext` | statement, all stacking openings, root `c` | 59 |
| 3 | round header: `k_whir` | no | `config` | — | 130 |
| 4 | sumcheck `ev1, ev2` (per subfold) | no (absorbed) | prover | absorbed before the fold challenge | 139-140 |
| 5 | folding PoW (per subfold) | no (checked) | prover witness | absorbed before `alpha`; bits = 0 measured | 143-145 |
| 6 | **α_{i,s}** (fold challenge), `s = 0..k_i-1` | yes | `Ext12` uniform, `sample_ext` | `ev1, ev2` for this subfold, and everything absorbed before, and `claim` (a function of prior alphas) | 146-151 |
| 7 | final-poly coefficients (final round) ‖ codeword commitment `g_{i+1}` (others) | no (absorbed) | prover | absorbed before `z0` / queries | 154-165 |
| 8 | **z_{i+1,0}** (OOD point) | yes | `Ext12` uniform, `sample_ext` | `g_{i+1}` | 166-167 |
| 9 | `y0` = OOD claim | no (absorbed) | prover | absorbed before queries | 170-171 |
| 10 | query-phase PoW | no (checked) | prover witness | absorbed before query indices | 174-185 |
| 11 | **query indices** `z_{i,·}` | yes | `sample_query_index` → `sample_index_exact(15·2^{L-k})` for `c = 15` | the PoW witness and everything above | 187-196, `odd_domain.rs:71-81` |
| 12 | Merkle / multiproof checks on opened rows | no (checked) | prover path | — | 219-312 |
| 13 | **γ_i** (WHIR-Y) | yes | `Ext12` uniform, `sample_ext` | `y_{i,·}` absorbed first when `levers.whir_y` | 316-326 |
| 14 | final `claim` check | no | — | — | 370-400 |

**Can the scalar fold result be consumed at each move?**

| move | consumed by | how |
|---|---|---|
| 6, α_{i,s} | `DKTG2FoldCoverage.{role}_r{i}_s{s}` (previously `DKTG2FoldTransfer`) | **yes, exactly.** Sub-code `s` of round `i` is the code the fold acts on, and the exceptional set is taken over the challenge the verifier samples at `whir.rs:146`. |
| 2, μ | not by these transfers | μ batches *columns*, so it needs the μ-batching/correlated-agreement curve term (`PROOF.md` Lemma 4.2), not a binary FoldAgreement statement. |
| 8, z0 | no | OOD needs the list bound ℓ_i (`PROOF.md` Lemma 4.4), which `DKTCertsO2_*` *does* supply as `listQ`/`list0`, but the OOD probability statement is not formalised here. |
| 11, queries | no | shift/final query terms need `(1-δ)^t` and exactly-uniform indices (`PROOF.md` Lemma 4.5, x15 `SOUNDNESS.md`). Not formalised here. |
| 13, γ_i | no | the γ combination term is `ℓ_{i+1}(t+1)/|F|` (Lemma 4.6); not formalised here. |

So: **the fold moves are the only WHIR moves for which a machine-checked per-move error
exists**, and they are now composed adaptively (§2). OOD, shift-query, γ and μ remain
paper-level.

One conditioning subtlety the table makes explicit: the α's within a round are **not**
independent of each other in the proof-theoretic sense that the old transfers could use —
`claim` between them is a function of prior alphas, and the adversary's next committed word can
depend on them. That is precisely the gap §2 closes.

---

## 2. Adaptive composition (Step 2) — PROVED

New file `research/near-compression/final-soundness/lean/DKTAdaptive.lean`.

### Statement

```lean
theorem DKTAdaptive.badRuns_probability [Nonempty F]
    (bad : List F → Finset F) (E : ℕ → ℚ)
    (hE : ∀ hist, ((bad hist).card : ℚ) ≤ E hist.length)
    (hist : List F) (n : ℕ) :
    ((badRuns bad hist n).card : ℚ) / (Fintype.card F : ℚ) ^ n ≤
      budgetSum E hist.length n / (Fintype.card F : ℚ)
```

`bad : List F → Finset F` takes the **whole preceding challenge history**; `hE` bounds its
cardinality as a function of `hist.length`. No independence is assumed between stages, no
"the bad set is fixed before the run" assumption is made, and the adversary may pick the word
committed before each draw as any function of the history.

Supporting statements, all kernel-checked with axioms ⊆ {propext, Classical.choice, Quot.sound}:

* `badRuns_card` — the same bound as an absolute cardinality, `|bad| ≤ |F|^{n-1} Σ E`.
* `badRuns_probability_const` — constant budget `E`: total `≤ n·E/|F|`.
* `allGood_probability` — complementary form, `1 - (Σ E)/|F| ≤ Pr[all good]`, written with the
  good set as the complement of `badRuns` so no decidability hypothesis on the good predicate is
  needed.
* `notMem_badRuns_iff_allGood` / `allGood` — the semantic "every draw good at its own history"
  predicate is *proved* to be the complement of the counting set, so the counting bound is not
  vacuous or over-strong.
* `badOfWord_bound` — discharges `hE` from a family of certificates of the
  `∃ ex, |ex| ≤ E ∧ ∀ γ ∉ ex, Good word γ` shape, which is exactly the shape of every
  `final_r{r}_s{s}` theorem. The adversary's word is an arbitrary function of the history; since
  the certificate family quantifies over *all* words with the *same* budget, no assumption on the
  adversary is added.

### Reusability check of `Qrom.Adaptive.badRuns_probability`

`research/qrom/Qrom/Adaptive.lean` proves the same shape over `ℕ` budgets
(`badRuns_card`, `badRuns_probability`, with `budgetSum` in `ℕ`). It **is** applicable in
principle. Two reasons for the separate file rather than an import:

1. the hard rule forbids touching `research/qrom/**`, another track owns it;
2. the QROM file's normalized bound divides by `|F|^n` and compares to `budgetSum/|F|`, which is
   the same inequality, but its budgets are `ℕ` and the WHIR consumption needs `ℚ` because the
   certificate budgets are `ℚ` (`(exceptional.card : ℚ) ≤ 6483461178158842957708865`).

Both files are now duplicated logic. If the QROM track is willing, `DKTAdaptive` can be replaced
by a `ℚ`-valued sibling in `research/qrom` and imported; no proof content would change.

### Round-level join

New file `DKTRoundCompose.lean`:

* `roundFold_probability` — a round of `k` subfolds with per-step budgets `E 0..E(k-1)` has bad
  probability `≤ budgetSum E · k / |Ext12|`; the `badAt s hist` family is history-dependent.
* `roundFold_probability_empty` — the same starting from the empty history, i.e. round start.
* `roundFold_probability_uniform` — constant-budget corollary `k·E/|Ext12|`.
* `roundGood_probability` — complementary form for a verifier soundness argument.
* `stepBudgets_of_certificates` — re-export of `badOfWord_bound` at `ℚ`/`Ext12`.

`|Ext12| = 2013265921^12` (`extCard`), matching the denominator used by
`DKTG2FoldTransfer.finalScalarFoldBudget_fraction_lt`. `sample_ext` is genuinely uniform on
`Ext12` (`transcript/traits.rs:29-31`: twelve independent base draws), so this denominator is
the right one for α, z0, γ and μ — unlike the query indices, which are uniform on
`15·2^{L-k}` and use `sample_index_exact`.

### Honest limits of §2

* It is a **classical finite-sampling** union bound. It does not model Fiat–Shamir or the QROM
  compilation; it takes "the verifier's challenge is uniform on `Ext12`" as a hypothesis about
  the sampler, which `sample_ext` supports but which is not proved against the sponge.
* It composes **one round's folds**. It deliberately says nothing about μ, OOD, queries or γ.
* It does not make the 2^-283 figure a security bound. See §6.

---

## 3. Coverage beyond the 13 measured folds (Step 3) — PARTIAL

New generator `calc/g2_fold_coverage.py` (certs and transfers modes, same discipline as
`g2_fold_certificates.py`: it *selects* existing kernel-proved blocks from
`DKTCertsO2_[0-7].lean`, renames them, and byte-compares). New files
`DKTG2FoldCoverageCerts.lean` (14 *new* certificates — the sub-code-0 ones and all of PARENT;
the 13 already in `DKTG2FoldCerts` are imported and reused, so no proof is duplicated) and
`DKTG2FoldCoverage.lean` (27 transfers + `coverageFoldBudget_sum`).

Coverage now:

| layer | round | regime | sub-codes transferred | note |
|---|---|---|---|---|
| FINAL | r0 | O-2 | `s = 0, 1` (**s=0 is new**) | r0's own sub-code `s=0` had no transfer before |
| FINAL | r1 | O-2 | `s = 0..4` (**s=0 is new**) | |
| FINAL | r2 | O-2 | `s = 0..4` (**s=0 is new**) | |
| FINAL | r3 | O-2 | `s = 0..4` (**s=0 is new**) | |
| PARENT (inner layer) | r1 | O-2 | `s = 0..4` (**all new**) | first inner-layer shape |
| PARENT | r2 | O-2 | `s = 0..4` (**all new**) | |
| FINAL | — | — | full FINAL round structure: **all 4 rounds, all sub-codes** | |
| PARENT | r0, r3 | **Johnson** | none | no O-2 certificate exists (`run.log:46`, `first_order=false`); needs the `DKTGlue` Johnson route |
| base/app layer | — | — | none | beyond this track's scope |

Worst-case per-round fold budget, as an exact rational over `|Ext12|`:

| round | folds | `log2(Σ E / \|Ext12\|)` |
|---|---:|---:|
| FINAL r0 | 2 | −286.14 |
| FINAL r1 | 5 | −285.63 |
| FINAL r2 | 5 | −284.17 |
| FINAL r3 | 5 | −280.94 |
| PARENT r1 | 5 | −283.84 |
| PARENT r2 | 5 | −282.01 |
| all 27 | 27 | **−280.11** |

These are **sums of independent scalar budgets for folds only**. They exclude every other WHIR
move. `log2` above the 2^-283 figure of the older 13-fold set is expected: adding sub-code
`s=0` adds the *base* (non-folded) code's exceptional count, which is the largest one.

---

## 4. Ordered-coset identification (Step 4) — PARTIAL (ring algebra proved, Rust extraction open)

New file `DKTOrderedCoset.lean`.

**Proved** (all kernel-checked, no hypotheses on the generators at the deployed instantiation):

* `fifteenRoot_eq` — `odd_root::<BabyBear>(15) = 31^((p-1)/15) = 1995471372`, via a repeated
  squaring chain (`sqChain`, `sqChain_eq`) so the kernel never builds a `2^27`-bit numeral.
* `twoAdic_part` — `p - 1 = 2^27 * 15`.
* `fieldGenerator_isPrimitive` — `orderOf (31 : ZMod p) = p - 1`, via
  `orderOf_eq_of_pow_and_pow_div_prime` reduced to the three prime cofactors `2, 3, 5`, each a
  kernel `decide +kernel`.
* `fifteenRoot_isPrimitive` — `IsPrimitiveRoot fifteenRoot 15`.
* `two_adic_half_turn` — for any even order `2h`, `omega^h = -1`. This is the `−x ∈ L`
  property (`SOUNDNESS.md` P1).
* `cosetIndex` + `cosetIndex_fst`/`cosetIndex_snd`/`cosetIndex_decomp` — the backend's integer
  arithmetic `index = a·h + u ↦ (a, u)` is `i ↦ (i / h, i % h)` exactly
  (`odd_domain.rs:52-67`).
* `roots_eq_cosetMajor` — the roots produced by that layout are exactly a
  `DKTWhirFold.cosetMajorSquareDomain`'s roots, so they form a `SquarePairedDomain` for the
  backend's coset-major word.
* `deployedSquareDomain` — the `c = 15`, `h = 2^K` instantiation in any field with a primitive
  15th root and a primitive `2^(K+1)`-th root, **unconditional** in those roots. (The concrete
  `ZMod p` instantiation is not stated because it would force `Field (ZMod p)`, whose instance
  search unfolds the primality proof in every use; `fifteenRoot_isPrimitive` supplies the root
  hypothesis instead, so nothing is lost.)

**Open — the exact statement, not proved:**

> Let `whir.rs`/`odd_domain.rs` be compiled with the pinned toolchain and `F = BabyBear`
> (`p = 2013265921`, `GENERATOR = 31`). Then for every `L`, `k` with `k ≤ L`,
> `crate::odd_domain::query_root::<BabyBear>(15, L, k, i)` returns, as a canonical base-field
> element, `fifteenRoot ^ (i >> (L-k)) * two_adic_generator(L) ^ (i & (2^(L-k) - 1))`,
> and the coset-major leaf at index `a * 2^L + u0 + j * 2^(L-k)` is the evaluation at
> `fifteenRoot^a * omega_L^(u0 + j·2^(L-k))`, with `hash_coset` hashing the `2^k` rows in the
> order `t = 0..2^k` (`hasher.rs:43-51`).

This needs either a Rust-semantics/refinement argument or extraction of the compiled constants;
it is a statement about a concrete program, not a ring identity. `SOUNDNESS.md` argues it in
prose and the tests in `research/near-compression/x15-domains/` exercise it, but neither is a
proof. **Marked open.** (Independently, the `hash_coset` coset-leaf layout is what makes the
Merkle binding a function of the *ordered* coset, so this open item also gates the Merkle
binding statement, not just the domain statement.)

Also still open, and separate: the *other* Rust index operations (the `opened_values[query_idx]`
ordering in `whir.rs:257-262`, and the `mu_pows` flattening order in `whir.rs:97-101`), which
determine whether the batch the *verifier* folds is the batch `binarySplitWord` describes.

---

## 5. Axioms, harness, artifacts

* Axioms of every new declaration ⊆ {propext, Classical.choice, Quot.sound}; asserted
  per-declaration by `check_g2_folds.sh` step 3.
* No `sorry`, `axiom`, `native_decide`, `implemented_by` in the new modules; asserted by
  `check_g2_folds.sh` step 4.
* `G2-VALIDATION.json` updated with the new hashes and declaration counts; companion
  `PAIRING-VALIDATION.json` records the backend file hashes above and the pin (`fc1f9e4`).
* `check_g2_folds.sh` now byte-compares all four generated files and builds eight modules.

---

## 6. Item-by-item status

| # | item | status | what closes it |
|---|---|---|---|
| 1 | adaptive composition | **PROVED** (`DKTAdaptive`, `DKTRoundCompose`) | — (classical finite-sampling model; FS/QROM is item 7 of the QROM track) |
| 2 | all rounds and sub-codes | **PARTIAL**: full FINAL (4 rounds × all sub-codes) + PARENT r1, r2 | Johnson rounds (FINAL r3 is O-2 here, so this is done for `first_order=true`; `first_order=false` rounds r0/r3 of PARENT need `DKTGlue.johnson_tensorFold` applied to the *actual* layer parameters, which is a new generator entry), plus the base/app layer |
| 3 | ordered coset identification | **PARTIAL**: ring algebra + concrete generators + index arithmetic proved; Rust extraction open | the exact Rust statement in §4 |
| 4 | interleaving / list products (DKT26 Cor 7.7/7.8) | **OPEN** at the actual sub-codes | `DKTGlue.johnson_tensorFold` only covers the *Johnson* regime; the O-2 sub-codes need `uniformExactInterleavedPowerAgreement_of_scalar_arbitrary` applied to each `DKTCertsO2.mca_i`. Not done here: the coverage certificates are scalar, and the interleaved lift needs the `FullSetLevelWitness` shape, which the generator does not emit. Round-0 multi-commitment list product × Johnson fallback (`PROOF.md` §6.3) also unformalised. |
| 5 | round-by-round state | **PARTIAL**: `DKTRoundCompose` builds the per-round fold state and its bad event; nothing consumes OOD/query/γ/μ | a per-move state machine covering moves 2, 8, 11, 13 of §1, each with its own error term from `PROOF.md` Lemmas 4.2, 4.4, 4.5, 4.6 |

### The 2^-283 figure

`DKTG2FoldTransfer.finalScalarFoldBudget_fraction_lt` still proves
`243070745342134118005592704 / 2013265921^12 < 2^-283`, and that is all it proves: the *sum of
thirteen scalar fold budgets for one layer's folds, divided by `|Ext12|`*. It is not
`Pr[forgery]`, it does not include the other 14 sub-codes now transferred (whose sum is
`log2 ≈ −280.11`), and it does not include OOD, queries, γ, μ, the Johnson rounds, other
layers, or the QROM loss. `security_established` stays `false`. The generator and the doc string
in `DKTG2FoldTransfer.lean` say so; keep them saying so.

---

## 7. What in the paper / `McaToGap.lean` still overstates

`zk-formal/ZkFormal/Udr/McaToGap.lean` was demoted on this branch and its header is now
accurate (unique-decoding utility; `strong_from_mca` needs `2e < d`; `fold_union` is arithmetic
on supplied bounds; `johnson_example_not_unique` is a kernel regression). No further overstatement
found there.

Remaining overstatements/ambiguities outside it:

1. **`PROOF.md` §4, Lemma 4.3** says "the fold word is a line in the 2-interleaved code, so
   Cor 7.7 transfers `E` with no width factor", citing `DKTGlue.johnson_tensorFold`. That works
   for the O-1/Johnson sub-codes. It does **not** cover the O-2 sub-codes, which are the ones
   the measured FINAL actually uses (`run.log:48` `first_order=true` everywhere). §4 should say
   that the O-2 interleaved lift is `uniformExactInterleavedPowerAgreement_of_scalar_arbitrary`
   and that it is *not* in `DKTGlue`.
2. **`PROOF.md` §6.5** line numbers (`whir.rs:146` for α, `:166` for z0, `:326` for γ) are
   correct for the *unified* tree but the table's other entries (`:187-196` queries,
   `45`/`59` μ) must be read against the 541-line unified file, not the 412-line
   `stark-backend/` file. The doc should name `stark-backend-unified` explicitly; `PROOF.md:40`
   does, the §6.5 table does not.
3. **`PROOF.md` §4, Lemma 4.1 / `x15-domains/SOUNDNESS.md`** describes the ordered-coset
   identification as "designed and implemented below" and "Nothing is open at the level of
   theorems". The *theorem level* claim is fine (conditions on abstract generators), but the
   identification of those generators with the compiled constants and the `hash_coset` leaf
   order is a Rust statement, still open (§4 here). `SOUNDNESS.md`'s "Gate 1 verdict: PASS"
   should carry the same qualifier.
4. **§6.5's "no missing absorption"** conclusion is stated as a code audit. It is true for
   absorption order, and `DKTAdaptive` does not need more than that for the fold moves — but the
   doc should not be read as saying the *error terms* compose adaptively; that was the gap, and
   it is now closed only for folds.
5. **`GAPS.md` S-28** ("the step from the RS-level statements to the WHIR round-by-round errors
   is paper-level") remains exactly right for OOD/query/γ/μ. It should be narrowed to say the
   **fold** step is now machine-checked per round with adaptive conditioning.
