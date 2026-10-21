# The recursive hash bridge: adjudicating endpoints (a)–(d)

Lane `lane/pq-hash-bridge`, 2026-10-21. Companion to
`../final-soundness/PROOF.md` §7 (cited as PROOF §7), the paper's §7.3 and
Appendix C.3 (`docs/research/pq-proven-soundness-paper-draft.md`), the
re-check note `docs/logs/pq-paper-blockers-recheck-2026-10-21.md` §4, and the
A-IC analysis `LEMMA.md` in this directory.

**Bottom line.** Recommend **(c)**: keep the implementation, state an explicit
computational-soundness assumption for the concrete inner system, and describe
the result as a *conditional* endpoint. The reduction shape is now
machine-checked (`research/hash-bridge/HashBridge/Endpoint.lean`), the missing
piece is one named hypothesis, and the loss is quantified. (a) is not reachable
here because the extractor and its simulation cost do not exist; (b) is a
construction nobody has designed or measured; (d) is reachable only *as a
model*, and that model is not the deployed system. None of (a)–(d) yields
unconditional recursive security, and the withdrawn A-IC is false as an
identification.

Everything below distinguishes three kinds of claim, in the style the audited
draft now uses:

* **[P]** kernel-checked in this lane;
* **[W]** written proof or cited theorem, not formalised;
* **[M]** modelling / definitional choice (legitimate, but not a theorem).

---

## 0. The two events that must not be confused

For the tail there are two languages over the same deployed verifier `V`:

* `L_air` — **membership in the concrete NV AIR relation.** An accepted trace
  certifies that `V_{i-1}` — the native verifier with concrete SHA-384, 42-byte
  Merkle digests and the `T*` transcript (PROOF Lemma 7.1 F1–F6) — accepts
  `(x_{i-1}, π_{i-1})`. This is exactly what the outer QROM argument can
  establish: it proves the *concrete* inner verifier's acceptance computation.
* `L_rec` — **base truth**: the end-to-end relation the recursion tail claims.

The outer theorem gives `RomSound … L_air`. Recursive semantics needs
`RomSound … L_rec`. The gap is the event

```
romInnerBad := (V accepts) ∧ L_air(claim) ∧ ¬ L_rec(claim)
```

— "the concrete inner proof system accepted a false inner statement" —
together with the tape-overflow branch of the ROM game, which `RomSound`
already charges. `Endpoints` need not touch `L_air`'s definition; the point is
that **the outer theorem's conclusion is a statement about `L_air`, not about
`L_rec`**, and the difference is irreducible.

The withdrawn Assumption 7.3 tried to close the gap by *identification*: treat
the concrete SHA-384 evaluations inside the trace as answers of the independent
oracle `H`. That identification is false in a precise, quantified sense (§2,
endpoint (d)); it is not merely unproved.

---

## 1. What is proved today

Kernel-checked in this lane, axioms ⊆ `{propext, Classical.choice, Quot.sound}`
(all `#print axioms` guards are in the files):

| statement | file:line | content |
|---|---|---|
| `inner_computational_soundness` | `HashBridge/Endpoint.lean:147` | `RomSound L_air` + `PrLE (romInnerBad)` bound ⇒ `RomSound L_rec` with denominator sum |
| `inner_perfect_soundness` | `Endpoint.lean:176` | the same with `numInner = 0` |
| `inner_bad_empty_of_pointwise` | `Endpoint.lean:165` | pointwise `L_air ⊆ L_rec` empties the residual event |
| `romWins_subset` | `Endpoint.lean:123` | `¬L_rec ⊆ ¬L_air ∪ (L_air ∧ ¬L_rec)` on the tape model, overflow split off |
| `romWins_iff` | `Endpoint.lean:106` | `romWins` = overflow ∨ accepted-outside-language |
| `PrLE.or` | `Endpoint.lean:66` | union bound over a common denominator |
| `romSound_iff_R` | `Endpoint.lean:201` | `RomSound = RomSoundR roRange`, i.e. the game's alphabet is a parameter |
| `lazyAnswer_length` | `Endpoint.lean:208` | the core's oracle answer is exactly **32 bytes** |
| `lazyAnswer_ne_of_length_42` | `Endpoint.lean:212` | it can never be a 42-byte digest |
| `roRange_mismatch` | `Endpoint.lean:220` | `2^256 < 2^336 < 2^384` |
| `roRange_gaps` | `Endpoint.lean:228` | `2^256·2^80 = 2^336`, `2^336·2^48 = 2^384` |
| `consistency_probability_multi` | `Endpoint.lean:325` | `count·R^ℓ ≤ R^n` for an adaptive demand sequence |
| `failure_lower_bound_multi` | `Endpoint.lean:401` | `B − R^{n−ℓ} ≤ #(accepted ∧ inconsistent)` |
| `failure_single_pair` | `Endpoint.lean:421` | the `ℓ = 1` case, at any `R` |
| `simBlocks_eq_J_mul_calls` | `Cost.lean:57` | `2Jt = J·(2t)` |
| `blockCount_at_headline` | `Cost.lean:62` | `simBlocks 2^20 2^64 = 2^85` |
| `blockCost_fits_128` | `Cost.lean:68` | `2^85 ≤ 2^128` (simulation alone fits) |
| `headline_gate_bound_exceeds_128` | `Cost.lean:75` | `2^128 < 336·2^63·(2^63−1)` |
| `totalCost_le` | `Cost.lean:83` | cost accounting is additive over the slots |
| `extraction_budget_at_headline_strict` | `Cost.lean:93` | `totalCost ≤ 2^128` forces `T_extract ≤ 2^128 − 2^85 − 2^64` |
| `agree_card` | `qrom/Qrom/OracleBridgeSet.lean:70` | `\|Y\|^{(\|D\|-\|Q\|)}` oracles agree with `v` on `Q` |
| `agree_count_mul` | `OracleBridgeSet.lean:79` | `\|agree\|·\|Y\|^{\|Q\|} = \|Y\|^{\|D\|}` |
| `acceptance_le_agreement` | `OracleBridgeSet.lean:98` | acceptance ⇒ `\|accepted\| ≤ \|Y\|^{\|D\|-\|Q\|}` |
| `acceptance_PrLE` | `OracleBridgeSet.lean:120` | `\|accepted\|·\|Y\|^{\|Q\|} ≤ \|Y\|^{\|D\|}` (`PrLE` shape) |
| `delta_ge_one_sub_agreement` | `OracleBridgeSet.lean:135` | acceptance at `1−δ` ⇒ `δ ≥ 1 − \|Y\|^{−\|Q\|}` |
| `bits_384` / `bits_336` | `OracleBridgeSet.lean:176,181` | `(2^384)^ℓ = 2^{384ℓ}`, `(2^336)^ℓ = 2^{336ℓ}` |

Reproduced from the paper branch (`research/qrom`: 8,724 jobs; `formal-core`:
33 jobs; `research/hash-bridge`: 18 jobs). Existing declarations re-checked
unchanged: `OracleBridge.{consistent_card, accepted_consistent_card,
acceptance_le_failure_add_fiber, consistency_probability,
bridge_failure_lower_bound, bridge_failure_measure}`, `Peeling.{bound,
old_peeling_bound_fails}`, `QueryCost.{gates_lower_bound,
headline_cost_exceeds_time_cap}` — all ⊆ `{propext, Classical.choice,
Quot.sound}`.

---

## 2. The four endpoints

### (a) Outer-layer QROM reduction to computational soundness of the concrete inner system

**What must be true.** There is an explicit reduction `B`, runnable by anyone,
which turns an accepted false outer statement into either (i) a satisfying NV
trace whose extracted inner proof the *concrete* verifier accepts, or (ii) a
successful attack on a named computational game for the inner system. `B` must
be efficient under a charged budget, and the outer adversary's *entire* work
must pass through `B` without extra oracle access that `B` cannot simulate.

**What is proved.** Only the scalar shape `p ≤ (√(ε_inner + ε_outer_bad +
δ_sim) + √(ℓ_V/2^336))²` (`Qrom.Peeling.bound` [P], plus
`old_peeling_bound_fails` [P]). `Qrom.QueryCost.gates_lower_bound` [P] and
`headline_cost_exceeds_time_cap` [P] are the finite cone count in G-P1-C.

**The loss term.** `ε_inner` (unquantified), `ε_outer_bad` (the family-QROM
track's open measured-event inclusion), `δ_sim` (an approximate-simulation
error), `ℓ_V/2^336`.

**Decisive reason it is not reachable in this repo.**
1. **No `B` exists.** `Qrom.Peeling.bound` is an implication whose hypothesis
   `Replacement` (`FactA.lean`) is itself a cited interface, and `hrepl`/`hextract`
   are premises; nothing constructs the extractor. The paper says the same
   (PROOF §7.3, §C.3).
2. **The extractor's efficiency is exactly what G-P1-C obstructs.** G-P1-C [W]
   gives a quadratic lower bound `336·2^63·(2^63−1) > 2^128` two-qubit gates for
   the universal exact fixed-interface online simulator at `q = 2^64`. A
   *computational* inner assumption with `τ = 2^128` needs the simulator to run
   inside `τ`; the only such simulator anyone has written is outside that budget
   in the model where the bound applies. `Cost.lean` makes the accounting
   precise: the counter-mode *block* count is only `2^85` [P]
   (`blockCost_fits_128`), so the query model does not refute `τ = 2^128`; but
   `extraction_budget_at_headline_strict` [P] shows the budget must be split
   explicitly, and the G-P1-C gate bound exists in the model where the
   simulation is a circuit.
3. **Extraction cost is unbudgeted.** `T_extract = poly(n)` independent of the
   measured database is not established anywhere in the repo (`LEMMA.md` §5).

So (a) is not a decision we can make this week: it needs a reduction that has
not been written and a cost bound that G-P1-C says is hard in the natural model.
**(a) is not reachable. Not a modelling decision — an absent theorem.**

### (b) A new construction linking the inner relation and the oracle semantics

**What must be true.** A protocol change (e.g. the inner verifier itself queries
the outer oracle on each certified pair, CGSY24 §6.3/Thm 6.5 style, or an AROM
with the argument using the algebraic structure, CCGOS23 Def 4.1) together with
a proof that the new verification relation *implies* the oracle's answers, and a
quantum proof for the new construction.

**What is proved.** Nothing. There is no such construction in this repo; the
293,077-byte artifact measures the *current* design and does not apply.

**The loss term.** Unknown, and not expressible in the present terms, because
the protocol and its security game do not exist.

**Decisive reason it is not reachable.** (b) is a research programme spanning a
protocol redesign, its quantum proof, and a new measurement. It is not a
decision among existing artifacts, and it would invalidate the measured size
headline. **Not reachable in this repo.** It is a legitimate future direction; it
is not the honest endpoint for *this* artifact.

### (c) An explicit assumption, named as such, giving a conditional endpoint

**What must be true.** A named hypothesis on the *concrete* inner system, in the
same game as the outer theorem: for the outer adversary `A` and the same oracle
and verifier run, the event "`V` accepts a claim in `L_air` that is not in
`L_rec`" has probability at most `numInner/den`. The reduction from the outer
bound to `RomSound L_rec` is then pure arithmetic.

**What is proved.** Exactly that reduction, **[P]**:

```
theorem inner_computational_soundness
    (hOuter : RomSound S L_air v P pub qH qP n numOuter den)
    (hInner : ∀ A, QueryBound hashWeight A qH → QueryBound proveWeight A qP →
      PrLE n roRange (romInnerBad S L_air L_rec v P pub A) numInner den) :
    RomSound S L_rec v P pub qH qP n (numOuter + numInner) den
```

(`Endpoint.lean:147`), with `inner_perfect_soundness` (`:176`) recovering the
`numInner = 0` shape and `inner_bad_empty_of_pointwise` (`:165`) identifying
*what* would discharge `hInner` unconditionally (a pointwise inclusion, i.e.
`SemSound`-strength). The bad-event decomposition is `romWins_subset` (`:123`);
the union bound is `PrLE.or` (`:66`). Every premise is a hypothesis in the
statement, and `#print axioms` shows only the three kernel axioms.

**The error term.** `numInner` in the numerator of the outer denominator. In the
peeling vocabulary the composed bound has the `Peeling.bound`/`PROOF.md` §7.3
shape `(√(ε_inner + ε_outer_bad + δ_sim) + √(ℓ_V/2^336))²`. The two statements
are consistent: `Endpoint`'s endpoint is the *shape of the reduction*, and the
peeling form is the *shape of the loss* once `ε_inner` is instantiated. Both
must be quoted together; neither alone is the theorem.

**Decisive reason (c) is reachable and correct.** It requires no absent theorem.
The one thing it requires — that a referee can read the assumption as a
*statement*, not a conjecture dressed up as a lemma — is satisfiable because
*every* ingredient the assumption mentions (`RomAdversary`, `romImpl`,
`romWins`, `PrLE`, the tape model, the query budgets, `roRange`) is already
defined in `formal-core`. It also does **not** claim more than (c) is allowed to
claim: `security_established: false` stays, and the result is "conditional on
ASSUMPTION INNER-SOUND". This is what the paper's §7.2 first bullet already
says; the contribution here is that the shape is now machine-checked.

### (d) An idealised arithmetized-oracle model with a valid reduction

**What must be true.** A *specified* model `M` in which the certified relation
`C` is defined arithmetically (the AROM of CCGOS23, or an oracle the verifier
itself queries), together with a valid reduction from the deployed system into
`M`, or `A-IC` proved *for `M`* rather than identified with SHA-384.

**What is proved.** The model is *statable* — `RomSoundR` (`Endpoint.lean:201`)
already parameterises the answer alphabet, and `romSound_iff_R` [P] shows the
deployed game is the `roRange` instance. But:

* the counting obstruction applies to the deployed system's side of any such
  reduction. `Qrom.OracleBridgeSet` proves **[P]** that if acceptance requires
  agreement with the concrete function on `Q`, then
  `#accepted·|Y|^{|Q|} ≤ |Y|^{|D|}` (`acceptance_PrLE:120`) and hence
  `δ ≥ 1 − |Y|^{−|Q|}` (`delta_ge_one_sub_agreement:135`). At 384-bit answers
  and `|Q| ≥ 1` this is `δ ≥ 1 − 2^{-384}`. So *any* reduction that exhibits the
  deployed concrete pairs as independent `M`-answers fails at the first pair;
* `research/hash-bridge` proves the same in the arena's `PrLE` vocabulary with an
  **adaptive** demand sequence (`consistency_probability_multi:325`,
  `failure_lower_bound_multi:401`, `failure_single_pair:421`): the demanded
  symbols may depend on every earlier answer, and the bound is still
  `count·R^ℓ ≤ R^n`;
* no `M` with a valid reduction to the deployed verifier exists in this repo.

**The loss term.** Not a small error: the counting statements are *lower* bounds
on inconsistency, so a reduction whose loss is "the concrete pairs are
independent oracle answers" has loss ≈ 1. There is no small error to charge.

**Decisive reason (d) is not reachable as *the endpoint for this artifact*.**
(d) is a legitimate research direction — specify `M`, prove `A-IC(M)` — but it
does not connect to the deployed verifier without exactly the reduction the
counting obstruction forbids. It would be honest only if the paper were
re-scoped to "security of the recursive tail in model `M`", which abandons the
claim about the deployed system. That is a user-level scoping decision, not
something this track may take.

---

## 3. Recommendation

**Adopt (c), stated as (c) is defined: a conditional endpoint.** The reasoning a
referee would accept:

1. The outer theorem can only prove `L_air` (PROOF §7.2). **This is not in
   dispute in the paper.** (c) accepts that and does not pretend to close it.
2. The withdrawn A-IC is *false* as an identification, and §2/(d) shows the
   obstruction is quantified and monotone in the number of pairs: more pairs do
   not help. So no amount of runtime capping rescues (a) or (d)-as-identification.
3. The only honest remaining object is the concrete inner system's soundness.
   Naming it as an assumption is exactly what (c) permits, and it is strictly
   weaker than what the repo's `SemSound`-style pointwise formulation would need
   (`inner_bad_empty_of_pointwise` [P] is the stronger sufficient condition).
4. The *shape* of the reduction is now machine-checked, so the residual gap is
   one named hypothesis with a stated error term — not a paragraph of prose.
5. The G-P1-C cost obstruction and the `Cost.lean` accounting show why (a)'s
   natural `τ = 2^128` framing cannot be assumed to be enough: `2^85` blocks
   fit, but the extraction slot must be budgeted explicitly
   (`extraction_budget_at_headline_strict` [P]).

**Exact assumption (quotable).**

> **INNER-SOUND(c).** Fix the outer adversary `A`, its oracle implementation,
> and the deployed verifier run of `ArenaCore.Security.ROM`. Let `L_air` be
> membership in the concrete NV AIR relation and `L_rec` base truth. There is a
> number `numInner` such that, over the same uniform tape of `n` answers in
> `[0, roRange)`, the event "the verifier accepts a claim in `L_air` that is not
> in `L_rec`" has probability at most `numInner/den`, for every `A` within the
> outer query budgets `qH`, `qP`. Equivalently, in the peeling vocabulary:
> `ε_inner = numInner/den` with `ε_outer_bad`, `δ_sim` supplied by the
> family-QROM track.

**What this assumption is not.** It is not collision resistance of SHA-384, not
a consequence of a runtime cap, not literal A-IC, and not a theorem in this
repo. It is a substantive cryptographic assumption about the concrete inner
proof system, whose *status* is "assumed"; its *error term* is `numInner/den`
(peeling form: `ε_inner`). The paper must say "conditional on INNER-SOUND(c)",
never "proven recursive security".

---

## 4. The `roRange` / 384-bit mismatch, quantified

This matters and was previously implicit.

* `ArenaCore.Security.ROM` fixes `roRange := 2^256` and `LazyRO.answer t =
  Bytes.beN 32 t`, i.e. the oracle answers are **32-byte** values
  (`lazyAnswer_length` [P]).
* The PQ stack's Merkle digests are **42 bytes = 336 bits**, and the transcript
  state is **384 bits**; the paper's replacement slack is `ℓ_V/2^336` and the
  fixed-pair statement is `2^-384`.
* Consequences proved in this lane:
  * `lazyAnswer_ne_of_length_42` [P]: the arena's oracle answer can **never**
    equal a 42-byte digest. So the deployed `hash-call` relation and the arena's
    `LazyRO` answer relation are *disjoint* on every query, not merely unlikely.
  * `roRange_mismatch` [P]: `2^256 < 2^336 < 2^384`; `roRange_gaps` [P]:
    exactly `2^80` and `2^48` multiplicative gaps.
  * `romSound_iff_R` [P]: `RomSound` *is* `RomSoundR roRange`. A bound proved in
    the arena's `2^256` game is a bound at `2^256`, **not** at the PQ parameters.
    Transporting it to `2^336`/`2^384` is a `[M]` modelling decision
    (`RomSoundR (2^336)` / `RomSoundR (2^384)`), not a theorem: `PrLE` is a
    counting statement over `[0,R)^n`, and changing `R` changes the sample
    space, not just a constant.
  * `bits_384`/`bits_336` [P]: the `ℓ`-pair consistency probabilities are
    `2^{-384ℓ}` / `2^{-336ℓ}`, so the multi-pair statement at the PQ parameters
    is not the `2^{-384}` of the fixed-pair note; it is `ℓ` times that in the
    exponent.

**What it implies — and which direction.** The *shape*
(`inner_computational_soundness`) is alphabet-agnostic; only the arithmetic
changes, so the endpoint statement survives re-parameterisation. The *numbers*
do not transfer for free, and the direction is not uniform:

* the **answer-length** mismatch is qualitative, not a factor. The arena's
  oracle answers are 32 bytes; a 42-byte digest is not in its range at all, so
  the deployed `hash` relation and the arena's `LazyRO` relation are **disjoint**
  on every query (`lazyAnswer_ne_of_length_42` [P]). A `RomSound` number is
  therefore a statement about a *different* oracle object, not a loose bound on
  the deployed one.
* the **alphabet-size** mismatch (`2^256` vs `2^336`/`2^384`) makes a
  fixed-density collision term *smaller* on the PQ side, so re-deriving at
  `2^336`/`2^384` can only help collision-style upper bounds. But "can only
  help" is a proof obligation, not an inference: each `PrLE` bound must be
  re-established at the deployed `R`, and a `RomSound` bound at `2^256` does not
  imply one at `2^336` by any monotonicity of `PrLE` itself.
* the **fixed-pair / multi-pair** terms move the other way: the paper's
  `2^{-384}` becomes `2^{-384ℓ}` (`bits_384` [P]), i.e. *smaller* as a
  consistency probability — which is exactly why `delta_ge_one_sub_agreement`
  makes the consistency premise *harder* to satisfy with more pairs, not easier.

Any paper text that cites `RomSound` numbers as PQ-stack numbers without (i)
naming `RomSoundR (2^336)` or `RomSoundR (2^384)` and (ii) re-deriving the bound
there is using a statement about a different object. This must be in the ledger.

---

## 5. What remains unproved, per endpoint

| endpoint | remaining premise | can it be discharged here? |
|---|---|---|
| (a) | an explicit extractor `B`; `Replacement` (CFHL21 Cor 4.2); simulation cost inside `τ`; `T_extract` | No — absent construction, and G-P1-C obstructs the natural model |
| (b) | the new construction, its quantum proof, a new size measurement | No — a redesign |
| (c) | `INNER-SOUND(c)` (§3), plus the family-QROM `ε_outer_bad` | No — but it is *named*, machine-checked shape, quantified error |
| (d) | a specified `M`, `A-IC(M)`, and a reduction from the deployed system | No — the counting obstruction blocks the reduction for the deployed pairs |

Also still external for *any* endpoint: NV faithfulness (Lemma 7.1 F1–F6, the
NV/base track), the family-QROM measured-event inclusion and family potential
(the family-QROM track), and the full WHIR transfer (the WHIR track).
`Endpoint.lean` deliberately does not assume any of them — it takes `hOuter` as
a hypothesis precisely so the endpoint can be stated before those land.

---

## 6. Honest verdict

`security_established` remains **false**. What changed is that the recursive
composition's *reduction shape* is now machine-checked in the arena's own
vocabulary, the residual assumption is a single quotable statement, its error
term is named in both the `PrLE` and peeling vocabularies, the adaptive
multi-pair counting is proved rather than asserted, the `roRange`/384-bit
mismatch is proved as a factor rather than glossed, and the `τ = 2^128` cost
claim is split into a proved block count (`2^85`, fits) and a proved
extraction slot requirement (must be budgeted; G-P1-C contradicts it in the
circuit model).
