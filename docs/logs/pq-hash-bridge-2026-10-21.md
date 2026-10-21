# PQ track D — the justified recursive hash bridge (2026-10-21)

Branch `lane/pq-hash-bridge` (worktree `nearproof-wt/pq-hash-bridge`), based on
`fix/pq-paper-soundness` @ `84bf5c73e`. Track D of
`docs/logs/pq-paper-blockers-recheck-2026-10-21.md` §6.

**Deliverable:** a decision among endpoints (a)–(d), the loss quantified, the
assumption ledger rows the lead should paste, and what is genuinely provable
about the recommended one. Full adjudication:
`research/near-compression/aic-research/ENDPOINTS.md`.

**Verdict: (c), stated as a conditional endpoint.**
`security_established` stays **false**. No claim of recursive security is made
anywhere in this lane.

---

## 1. Build reproduction and axiom output

All builds with `export PATH=$HOME/.elan/bin:$PATH`, through
`/data/illia/nearproof-deps/bin/heavy` with `HEAVY_MEM=8G` on
`taskset -c 8-15,24-31`.

| package | command | result |
|---|---|---|
| `research/qrom` | `lake build` | **8,724 jobs**, success; Mathlib pin `/data/illia/nearproof-deps/arklib-dkt/ArkLib/.lake/packages/mathlib` (Lean v4.33.1) |
| `formal-core` | `lake build` | **33 jobs**, success (Lean v4.34.1), unchanged by this lane |
| `research/hash-bridge` (new) | `lake build` | **18 jobs**, success (Lean v4.34.1, requires `ArenaCore` by path) |

`research/qrom` was 8,723 jobs before this lane; the new
`Qrom/OracleBridgeSet.lean` is the +1.

`#print axioms` on the pre-existing declarations named in the brief, re-run
unchanged (all ⊆ `{propext, Classical.choice, Quot.sound}`):

```
'Qrom.OracleBridge.consistent_card'                [propext, Classical.choice, Quot.sound]
'Qrom.OracleBridge.accepted_consistent_card'       [propext, Classical.choice, Quot.sound]
'Qrom.OracleBridge.acceptance_le_failure_add_fiber'[propext, Classical.choice, Quot.sound]
'Qrom.OracleBridge.consistency_probability'        [propext, Classical.choice, Quot.sound]
'Qrom.OracleBridge.bridge_failure_lower_bound'     [propext, Classical.choice, Quot.sound]
'Qrom.OracleBridge.bridge_failure_measure'         [propext, Classical.choice, Quot.sound]
'Qrom.Peeling.bound'                               [propext, Classical.choice, Quot.sound]
'Qrom.Peeling.old_peeling_bound_fails'             [propext, Classical.choice, Quot.sound]
'Qrom.QueryCost.gates_lower_bound'                 [propext, Classical.choice, Quot.sound]
'Qrom.QueryCost.headline_cost_exceeds_time_cap'    [propext, Classical.choice, Quot.sound]
```

New declarations:

```
'Qrom.OracleBridgeSet.agree_card'                    [propext, Classical.choice, Quot.sound]
'Qrom.OracleBridgeSet.agree_count_mul'               [propext, Classical.choice, Quot.sound]
'Qrom.OracleBridgeSet.acceptance_le_agreement'       [propext, Classical.choice, Quot.sound]
'Qrom.OracleBridgeSet.acceptance_PrLE'               [propext, Classical.choice, Quot.sound]
'Qrom.OracleBridgeSet.delta_ge_one_sub_agreement'    [propext, Classical.choice, Quot.sound]
'Qrom.OracleBridgeSet.bits_384'                      [propext]
'Qrom.OracleBridgeSet.bits_336'                      [propext]

'ArenaCore.Bridge.PrLE.or'                           [propext, Classical.choice, Quot.sound]
'ArenaCore.Bridge.romWins_iff'                       [propext, Classical.choice, Quot.sound]
'ArenaCore.Bridge.romWins_subset'                    [propext, Classical.choice, Quot.sound]
'ArenaCore.Bridge.inner_computational_soundness'     [propext, Classical.choice, Quot.sound]
'ArenaCore.Bridge.inner_perfect_soundness'           [propext, Classical.choice, Quot.sound]
'ArenaCore.Bridge.inner_bad_empty_of_pointwise'      [propext, Classical.choice, Quot.sound]
'ArenaCore.Bridge.romSound_iff_R'                    [propext, Classical.choice, Quot.sound]
'ArenaCore.Bridge.lazyAnswer_length'                 [propext]
'ArenaCore.Bridge.lazyAnswer_ne_of_length_42'        [propext]
'ArenaCore.Bridge.roRange_mismatch'                  [propext, Classical.choice, Quot.sound]
'ArenaCore.Bridge.roRange_gaps'                      [propext]
'ArenaCore.Bridge.consistency_probability_multi'     [propext, Classical.choice, Quot.sound]
'ArenaCore.Bridge.failure_lower_bound_multi'         [propext, Classical.choice, Quot.sound]
'ArenaCore.Bridge.failure_single_pair'               [propext, Classical.choice, Quot.sound]

'ArenaCore.Bridge.simBlocks_eq_J_mul_calls'          [propext]
'ArenaCore.Bridge.blockCount_at_headline'            (none)
'ArenaCore.Bridge.blockCost_fits_128'                (none)
'ArenaCore.Bridge.headline_gate_bound_exceeds_128'   (none)
'ArenaCore.Bridge.totalCost_le'                      [propext, Quot.sound]
'ArenaCore.Bridge.extraction_budget_at_headline_strict' [propext, Quot.sound]
```

No `sorry`, no `axiom`, no `native_decide`, no `implemented_by` in any file
this lane adds (`grep` over `research/hash-bridge` and the new `Qrom` file
returns nothing).

---

## 2. Adjudication of (a)–(d)

| endpoint | what must be true | proved today | loss term | decisive reason |
|---|---|---|---|---|
| **(a)** outer-layer QROM reduction to computational soundness of the concrete inner system | an explicit, efficient reduction `B` with charged simulation + extraction cost | only the scalar shape `Peeling.bound` and the finite cone count `QueryCost` | `ε_inner` (unquantified), `ε_outer_bad`, `δ_sim`, `ℓ_V/2^336` | `B` does not exist; `Replacement` is a cited interface; G-P1-C obstructs the natural simulator, and `T_extract` is unbudgeted. **Absent theorem, not a modelling choice.** |
| **(b)** new construction linking inner relation and oracle semantics | a redesigned protocol, its quantum proof, a new size measurement | nothing; the 293,077-byte artifact measures the *current* design | unknown / not expressible | a research programme, not a decision among existing artifacts. **Not reachable here.** |
| **(c)** explicit assumption → conditional endpoint | a named hypothesis on the concrete inner system, in the *same* game as the outer theorem | the **reduction shape**, kernel-checked: `inner_computational_soundness` | `numInner/den` (peeling: `ε_inner`) | reachable precisely because it needs no absent theorem. The residual is one quotable assumption. **Recommended.** |
| **(d)** idealised arithmetized-oracle model with a valid reduction | a specified model `M`, `A-IC(M)`, and a reduction from the deployed system | `RomSoundR` makes the alphabet a parameter; the counting obstruction is proved for the multi-pair case | not small: the counting statements are *lower* bounds on inconsistency | the reduction from the deployed pairs is blocked: `δ ≥ 1 − 2^{-384\|Q\|}` at `\|Y\| = 2^384` for any nonempty pair set. **(d) is legitimate only if the paper is re-scoped to model `M`.** |

Short form: **(a) needs a missing reduction; (b) needs a new protocol; (d) needs
a re-scoping; (c) needs only an honest sentence.** (c) is the endpoint.

### Why a referee accepts (c)

1. The outer theorem can only prove `L_air` (membership in the concrete NV AIR
   relation). The paper already says this (PROOF §7.2); (c) does not contest it.
2. The withdrawn A-IC is *false as an identification*, and the obstruction is
   quantified and monotone in the number of pairs (§4). Runtime capping cannot
   rescue it.
3. The only honest remaining object is the concrete inner system's soundness.
   Naming it is exactly what (c) permits, and it is strictly weaker than the
   pointwise inclusion the repo's `SemSound` vocabulary would need
   (`inner_bad_empty_of_pointwise` is the stronger sufficient condition).
4. The *shape* is machine-checked, so the residual gap is a named hypothesis
   with an error term, not a paragraph.
5. The `Cost.lean` arithmetic shows why `τ = 2^128` cannot be assumed: `2^85`
   blocks fit, but the extraction slot must be budgeted explicitly.

---

## 3. Recommended endpoint and the exact assumption

> **INNER-SOUND(c).** Fix the outer adversary `A`, its oracle implementation,
> and the deployed verifier run of `ArenaCore.Security.ROM`. Let `L_air` be
> membership in the concrete NV AIR relation and `L_rec` base truth. There is a
> number `numInner` such that, over the same uniform tape of `n` answers in
> `[0, roRange)`, the event "the verifier accepts a claim in `L_air` that is not
> in `L_rec`" has probability at most `numInner/den`, for every `A` within the
> outer query budgets `qH`, `qP`. Equivalently, in the peeling vocabulary of
> `PROOF.md` §7.3: `ε_inner = numInner/den`, with `ε_outer_bad` and `δ_sim`
> supplied by the family-QROM track.

It is **not** collision resistance of SHA-384, **not** implied by a runtime
cap, **not** literal A-IC, and **not** proved in this repository. It is assumed;
its error term is `numInner/den` (peeling: `ε_inner`). The paper must write
"conditional on INNER-SOUND(c)", never "proven recursive security".

---

## 4. What was proved

### 4.1 The conditional endpoint (the reduction shape)

`research/hash-bridge/HashBridge/Endpoint.lean` (namespace `ArenaCore.Bridge`,
package `HashBridge`, imports `ArenaCore.Security.ROM`/`ROMLemmas`):

```lean
theorem inner_computational_soundness {S : ChallengeSpec} {L_air L_rec : Bytes → Prop}
    {v : OracleVerifier} {P : OracleProver S} {pub : Bytes}
    {qH qP n den numOuter numInner : Nat}
    (hOuter : RomSound S L_air v P pub qH qP n numOuter den)
    (hInner : ∀ A : RomAdversary S,
      OracleComp.QueryBound hashWeight A qH →
      OracleComp.QueryBound proveWeight A qP →
      PrLE n roRange (romInnerBad S L_air L_rec v P pub A) numInner den) :
    RomSound S L_rec v P pub qH qP n (numOuter + numInner) den
```

- `Endpoint.lean:147`. **Premises remaining:** `hOuter` (the family-QROM
  track's target), `hInner` (= INNER-SOUND(c)).
- `Endpoint.lean:176` `inner_perfect_soundness`: the `numInner = 0` shape.
- `Endpoint.lean:165` `inner_bad_empty_of_pointwise`: pointwise
  `∀ cb, L_air cb → L_rec cb` empties the residual event — the only
  unconditional discharge, and exactly what collision resistance does **not**
  give.
- Support: `romWins_iff` (`:106`), `romWins_subset` (`:123`), `PrLE.or` (`:66`),
  `PrLE.mono_num` (`:82`).

This is the value the brief asked for: the reduction's *shape* is
machine-checked and the missing piece is one clearly named assumption stated
over the arena's actual `RomSound`/`PrLE` vocabulary.

### 4.2 The adaptive multi-pair bridge (the piece the paper said was missing)

`Endpoint.lean`, model: a tape is the answers to *distinct* fresh inputs; a
`Demands` function reads the answers consumed so far and either requires the
next fresh answer to be a specific symbol or requires nothing.

- `Endpoint.lean:325` `consistency_probability_multi`:
  `count (allTapes n R) (allMet req) * R^ℓ ≤ R^n` whenever each of the first
  `ℓ` steps makes a demand — the demanded symbols may depend on **every earlier
  answer**. At `R = 2^384` this is `2^{-384ℓ}`; at the arena's `roRange` it is
  `2^{-256ℓ}`.
- `Endpoint.lean:401` `failure_lower_bound_multi`, `:421`
  `failure_single_pair`: if acceptance implies consistency and `B` tapes are
  accepting, at least `B − R^{n−ℓ}` are inconsistent. The `ℓ = 1` case **is**
  the paper's `1 − δ − 2^{-384}`.
- **Premises remaining:** `hsome` (the execution really makes a demand at each
  of the first `ℓ` steps — a statement about the extracted trace, not about
  `PrLE`) and `hacc` (acceptance requires the agreement). Both are named in the
  statement and neither is derived.

The same fact in the Mathlib/Qrom package, where `OracleBridge` lives:

- `research/qrom/Qrom/OracleBridgeSet.lean:70` `agree_card`, `:79`
  `agree_count_mul`: exactly `|Y|^(|D|−|Q|)` oracles agree with the concrete
  function on `Q`; equivalently probability `|Y|^{-|Q|}`.
- `:98` `acceptance_le_agreement`, `:120` `acceptance_PrLE`:
  `|accepted| · |Y|^{|Q|} ≤ |Y|^{|D|}`.
- `:135` `delta_ge_one_sub_agreement`: acceptance at `1 − δ` with required
  agreement on `Q` forces `δ ≥ 1 − |Y|^{-|Q|}`.
- `:176` `bits_384`, `:181` `bits_336`: `(2^384)^ℓ = 2^{384ℓ}`,
  `(2^336)^ℓ = 2^{336ℓ}`.
- **Premise remaining:** `hacc` only — that acceptance requires agreement with
  the concrete function on `Q`. No fixpoint/adaptivity gap.

**Direction is important and was got right here:** these are *upper* bounds on
acceptance (equivalently *lower* bounds on inconsistency). They say the
identification is impossible, not that it is unlikely. They do **not** bound a
recursive attack.

### 4.3 Time/advice accounting for `q → 2q`

`research/hash-bridge/HashBridge/Cost.lean` (explicit cost model, not a theorem
about the implementation):

- `Cost.lean:45` `simBlocks J t = 2*J*t` — counter-mode simulation: produce `J`
  blocks, XOR, uncompute. Lemma 6.3's "`2t` queries" counts **`G`-calls**, and
  `Cost.lean:57` proves `simBlocks J t = J * simCalls t`: the block count is
  `J` times the advertised figure.
- `Cost.lean:62` `blockCount_at_headline`: at `t = 2^64`, `J = 2^20`, the
  simulation is **`2^85`** block evaluations.
- `Cost.lean:68` `blockCost_fits_128`: `2^85 ≤ 2^128`. **So the simulation cost
  alone does not refute `τ = 2^128`** — this corrects the natural reading of
  paper §C.3.
- `Cost.lean:75` `headline_gate_bound_exceeds_128`: G-P1-C's
  `336·2^63·(2^63−1) > 2^128` two-qubit gates, restated kernel-checked so the
  two directions are visible side by side. The two are about different
  resources (oracle-block evaluations in a query model vs. ordinary two-qubit
  gates in a causal-cone model).
- `Cost.lean:83` `totalCost_le`: cost accounting is additive over
  `T_A + T_init + simBlocks + T_db + T_measure + T_extract`; a bound on `q`
  alone says nothing.
- `Cost.lean:93` `extraction_budget_at_headline_strict`: `totalCost ≤ 2^128` at
  the headline parameters forces `T_extract ≤ 2^128 − 2^85 − 2^64`. **`T_extract`
  cannot be treated as free**, which is exactly what U-12's `τ = 2^128` claim
  needs and the paper's §C.3 already warns about.

**Premise remaining:** the numbers `J = 2^20`, `t = 2^64` are the paper's stated
parameters; `simBlocks`'s shape (`2Jt`) assumes the produce/XOR/uncompute
simulation and a counter-mode index space of size `J`. The model is a `[M]`
choice, and is labelled as such in the file.

---

## 5. The `roRange` / 384-bit mismatch

Proved, not asserted (`Endpoint.lean`):

- `:208` `lazyAnswer_length`: `(LazyRO.answer t).length = 32`.
- `:212` `lazyAnswer_ne_of_length_42`: the arena's oracle answer can **never**
  equal a 42-byte digest. The deployed `hash` relation and `LazyRO`'s answer
  relation are *disjoint on every query* — not merely unlikely to agree.
- `:220` `roRange_mismatch`: `roRange = 2^256 ∧ 2^256 < 2^336 ∧ 2^336 < 2^384`.
- `:228` `roRange_gaps`: `2^256·2^80 = 2^336`, `2^336·2^48 = 2^384`.
- `:201` `romSound_iff_R`: `RomSound` **is** `RomSoundR roRange` — the alphabet
  is a parameter, and the deployed game is the `2^256` instance.

**What it implies.** `PrLE` is a counting statement over `[0,R)^n`; changing
`R` changes the sample space. Therefore:

1. A `RomSound` bound is a statement about a **different oracle object** from
   the deployed 384-bit one, and the difference on answers is qualitative
   (disjoint ranges), not a constant factor.
2. The *shape* of the endpoint is alphabet-agnostic; only the arithmetic
   changes.
3. The paper must name `RomSoundR (2^336)` (42-byte digests) or
   `RomSoundR (2^384)` (transcript) and re-derive its numbers there. Importing
   `2^256` numbers into PQ-stack claims without this step is using a statement
   about a different object.

---

## 6. Ledger rows for the lead to paste (verbatim)

The paper's §9 (`docs/research/pq-proven-soundness-paper-draft.md` on
`fix/pq-paper-soundness`) currently has, in §9.1 "Used":

> | A-IC | the SHA-384 evaluations certified in-circuit are modelled as oracle
> evaluations on that witness | additional proposed bridge;
> the architecture-specific obstruction is conditional. A precise time-bounded
> game and error budget are required |

and, in §9.2 "Not used":

> | efficient extraction | not needed for a purely existential relation claim;
> required and not yet costed for the computational peeling reduction |

**Replace the A-IC row** in §9.1 with these three rows:

```markdown
| **INNER-SOUND(c)** (assumed) | the concrete inner system is computationally sound: over the outer QROM tape, for the outer adversary `A` and the deployed verifier run, "accepts a claim in the concrete NV AIR relation that is not base truth" has probability ≤ `numInner/den` (peeling form: `ε_inner`) | **assumed, explicitly; not proved.** It is the conditional endpoint of §7.3 and the only one of (a)–(d) reachable without a new reduction or a new protocol. It is strictly weaker than the pointwise `SemSound` inclusion. Kernel-checked *shape*: `ArenaCore.Bridge.inner_computational_soundness` (`research/hash-bridge/HashBridge/Endpoint.lean`). Error term: `numInner/den` (= `ε_inner`), summed into the outer numerator by `PrLE` |
| **conditional reduction shape** (proved) | `RomSound L_air` + the INNER-SOUND(c) bound ⇒ `RomSound L_rec` with numerator `numOuter + numInner` | kernel-checked, axioms ⊆ {propext, Classical.choice, Quot.sound}. Composes with `Qrom.Peeling.bound`'s `(√(ε_inner + ε_outer_bad + δ_sim) + √(ℓ_V/2^336))²`. It does **not** prove INNER-SOUND(c), recursion, or composition |
| **oracle alphabet** (modelling decision) | statements about the random-oracle game are made at `RomSoundR (2^336)` (42-byte digests) or `RomSoundR (2^384)` (transcript), not at the arena core's `roRange = 2^256` | `RomSound` **is** `RomSoundR roRange`, and `LazyRO.answer` is exactly 32 bytes, so a 42-byte digest is outside its range entirely (`lazyAnswer_ne_of_length_42`). Transporting a `2^256`-game bound to the PQ parameters is a choice of game, **not** a theorem; each numeric bound must be re-derived at the deployed `R` |
```

**Replace the "efficient extraction" row** in §9.2 with:

```markdown
| efficient extraction | **used and not discharged.** The peeling endpoint needs an explicit, efficiently computable reduction with its runtime charged (`ArenaCore.Bridge.totalCost_le`); the counter-mode simulation costs `2^85` block evaluations at `t = 2^64`, `J = 2^20` (`blockCount_at_headline`), which fits `2^128`, **but** `totalCost ≤ 2^128` forces `T_extract ≤ 2^128 − 2^85 − 2^64` (`extraction_budget_at_headline_strict`), so extraction cannot be treated as free. G-P1-C's `>2^128` two-qubit-gate bound applies in its own fixed-interface circuit model, not to the block count. Endpoint (a) remains open |
```

**Add these rows** to §9.2 ("Not used"):

```markdown
| literal A-IC / concrete-SHA ≡ independent oracle | **false as an identification, in a quantified sense.** For one fixed pair, and for the adaptive pair set an execution uses, an independent oracle agrees on `ℓ` pairs with probability `≤ |Y|^{-ℓ}`; hence required agreement plus acceptance at `1−δ` forces `δ ≥ 1 − |Y|^{-|Q|}` (`OracleBridgeSet.delta_ge_one_sub_agreement`), and the arena-vocabulary version is `failure_single_pair` / `failure_lower_bound_multi` (`research/hash-bridge/HashBridge/Endpoint.lean`). More pairs make it *worse*, and no runtime cap changes a count of pairs |
| time cap ⇒ A-IC(τ) | **not used and not valid.** `|Q|` is a number of pairs, not a time; capping `τ` leaves the counting obstruction intact. This is unchanged from the withdrawn Assumption 7.3 |
| G-P1-C as a lower bound on every reduction | **not used in that form.** It applies to the universal online fixed-interface ordinary-gate circuit simulator; QRAM/QRAG, uncharged classical feedback, adversary-specific recompilation and computational simulation lie outside it (`LEMMA.md` §6). Only the finite cone count is kernel-checked |
```

Also update the §7.3 sentence that introduces the peeling bound so it reads
(proposed exact text):

> The scalar implication is checked in `Qrom/Peeling.lean`, and the reduction's
> *shape* in the arena vocabulary — `RomSound` at the concrete AIR relation
> plus one named inner-soundness hypothesis implies `RomSound` at base truth —
> is checked in `research/hash-bridge/HashBridge/Endpoint.lean`
> (`inner_computational_soundness`). Neither file constructs the extractor or
> discharges the inner hypothesis; `numInner` is an assumed error term.

### Ledger discipline check

No row above reads as a hidden conjecture: the three new §9.1 rows are labelled
**assumed**, **proved**, and **modelling decision** respectively; the §9.2 rows
are all **not used**. In particular the ledger contains no row whose status
column would let a referee infer a recursive guarantee: every row that mentions
recursion names `INNER-SOUND(c)` as assumed, and `security_established: false`
stays.

---

## 7. Files

| path | role |
|---|---|
| `research/hash-bridge/` (new package: `lakefile.toml`, `lean-toolchain`, `HashBridge.lean`, `HashBridge/Endpoint.lean`, `HashBridge/Cost.lean`) | conditional endpoint + adaptive multi-pair counting + cost accounting, in the arena's `PrLE`/`RomSound` vocabulary. Not imported by `ArenaCore`; kept in `research/` so the judge-trusted library gains no dependency |
| `research/qrom/Qrom/OracleBridgeSet.lean` (new) | fixed-pair-set count and trade-off in the Mathlib package where `OracleBridge` lives |
| `research/qrom/Qrom.lean` | +1 import |
| `research/near-compression/aic-research/ENDPOINTS.md` (new) | adjudication (a)–(d), recommendation, `roRange` finding |
| `research/near-compression/aic-research/LEMMA.md` | status header addendum only (no rewrite of another author's analysis) |
| `docs/logs/pq-hash-bridge-2026-10-21.md` (this file) | log, statements, ledger rows |

Not touched: `final-soundness/lean/**`, `wasm-base-lean/**`, `PQ/Join/**`,
ArkLib/Mathlib pins, `research/qrom/VALIDATION.json`,
`docs/research/pq-proven-soundness-paper-draft.md`, branch
`lane/pq-family-qrom`, and the main checkout.

`security_established` remains **false**; `research/qrom/VALIDATION.json` is
unchanged (this lane adds no `Qrom` declaration that any claim in the paper
depends on; the new file is additive and self-guarded).

---

## 8. Honest verdict

The recursive hash bridge is **not closed**, and this lane does not close it.
What is established:

1. **(c) is the endpoint.** (a) needs a reduction that does not exist and whose
   natural simulator G-P1-C obstructs; (b) needs a new protocol; (d) needs the
   paper to be re-scoped to a model. (c) needs one honest sentence, and its
   reduction shape is now kernel-checked.
2. The missing piece is **one named assumption**, `INNER-SOUND(c)`, with error
   term `numInner/den` (`ε_inner` in peeling form), stated over the arena's real
   vocabulary.
3. The fixed-pair obstruction extends to **the adaptive pair set an accepting
   execution actually uses**, with the adaptivity made explicit, and it gets
   *stronger* with the number of pairs. Adding a runtime cap cannot help.
4. `τ = 2^128` is **not** justified by counting queries: the counter-mode block
   count is `2^85` and fits, but the extraction slot must be budgeted
   explicitly, and G-P1-C contradicts the circuit-model simulator.
5. The arena's `roRange = 2^256` game is a **different oracle object** from the
   deployed 384-bit stack, and the paper must say so and re-derive numbers at
   the deployed alphabet.

**Single most misleading remaining statement** in the paper or `LEMMA.md`:
paper §7.3/Appendix C.3's framing of `τ = 2^128` as the outstanding question
("A time-bounded A-IC claim must specify the bound *after* those reductions; the
old `τ = 2^128` number alone is insufficient"). It is *right* about the cost,
but it still reads as though a sufficiently clever time-bounded INNER-SOUND
could rescue literal A-IC. It cannot: `delta_ge_one_sub_agreement` shows the
consistency premise fails at *any* acceptance probability above `2^{-384}`, and
`|Q|` — not `τ` — controls it. The sentence should say that a time-bounded
*computational inner assumption* is the candidate endpoint, and that literal
A-IC is not a time-bounded question at all.
