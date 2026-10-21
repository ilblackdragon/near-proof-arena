# Removing A-IC: research report

> **2026-10-21 update:** G-P1 is now the authorized, narrowly scoped research
> priority. See `LEMMA.md` §§5–7 for the corrected peeling bound, cost-model
> investigation and the model-specific G-P1-C lower bound. Earlier claims here that a simulator
> upper bound or BHT collision complexity proves inner-system insecurity are
> withdrawn: neither supplies a concrete accepted-proof attack. The family QROM
> instantiation and NV faithfulness remain independent open premises. No new
> recursive architecture or relaxation of SHA-384/U-7 is authorized.


Lane `lane/pq-aic-research` (from `lane/pq-final-soundness`), 2026-10-18. Question: is there a
**proven** bound for the recursive SWIRL stack without A-IC (PROOF.md Assumption 7.3), at
≤ 2⁻¹²⁸ against ≤ 2⁶⁴ quantum queries (U-2, U-6)? Failing that, what is the weakest assumption,
with a proof?

**Answer: no, and this is now a theorem rather than a gap.** LEMMA.md Thm O [T] says that in every
oracle model where native verification uses a random H and adversaries are bounded only in
H-queries (the model of PROOF Thm 6.4), the depth-d ≥ 1 system is insecure. One adversary
succeeds with probability ≈ 1 using ≤ 2⁴⁶ queries, as soon as the base verifier run with the
in-circuit hash accepts one proof of one false statement. That condition holds for 1 − 2⁻¹¹⁹⁹⁰ of
all functions (Lemma E.3 [S]). Corollary O.1: any proof of the U-6 statement as worded (queries
only, no time bound) for the recursive claim would show that V₀ with concrete SHA-384 is
perfectly sound. **Recommendation: close the "proven bound" goal.** Keep A-IC, restated with a
time bound, and adopt the two zero-cost hygiene items in §5.

Sources: full texts read by three research agents (ePrint PDFs via Wayback). Theorem numbers are
given below; anything not verified in the full text is marked.

---

## 1. Direction 1: Barbara–Chiesa–Guan, TCC 2025 (ePrint 2024/728)

**What it rules out.**
* **Model.** A relativized relation R^U = {R_u} (Def 3.5). In a relativized NARG (Def 3.14),
  P^f, V^f and R_f share one random f. Soundness (Def 3.13) is against q-query, t-time adversaries.
  The model is classical only; no quantum model appears.
* **Thm 4.1 / Cor 4.2:** DTIME^O[t] ⊄ NARG^O[vq = o(t)].
* **Thm 5.1 / Cor 5.2:** NTIME^O[t] ⊄ NARG^O[as = o(t)], even with vq = poly.
* **Thm 6.1 / Cor 6.2:** NTIME^O[t] ⊄ NARG^O[vq = o(t)], proved directly.
* **Interactive versions:** Thms 7.5, 7.8, 7.11.
* **Quantifiers:** ∀t ∃ one specific hard relation ∀ arguments. The hard relations are Def 4.3
  (XOR of t oracle bits) and Def 5.3 (∀i ≤ t: f(w‖i)₁ = 0). The hypothesis is non-vacuous only
  when the relation makes many more queries than the verifier (t > vq/p).
* **Proof idea (§2.4):** flip f at one point q₀ of the relation's query set that the verifier
  never reads. The map (f, q₀) ↦ g is a bijection. Honest acceptance under f then becomes
  acceptance of a false instance under g.
* **The paper's own remarks:** relativized IVC/PCD in the ROM do not exist. Ruling out
  *non-relativized* IVC/PCD in the ROM is left open. Relativized SNARGs do exist in the AROM,
  LDROM and SROM.

**Does our structure escape it?**
* **Fixed depth d ≤ 7, fixed statement, one verifier, bounded layers.** The *theorems* do not
  apply. Our per-layer relation "V_{i−1} accepts" makes about vq queries, the regime t ≈ vq where
  the hypotheses are empty. HN23 (ePrint 2022/542, Thms 1–2: IVC verifier linear in ℓ) is also
  vacuous for constant ℓ.
* **This does not help.** We do not need BCG's relation-level impossibility, because Thm O applies
  directly to our system and covers both readings of the in-circuit hash:
  * **Case (b), unconstrained "oracle gates":** this is BCG's relativized setting. H-ex holds
    unconditionally (Lemma E.1).
  * **Case (a), concrete SHA-384:** H-ex holds for all but 2⁻¹¹⁹⁹⁰ of functions (Lemma E.3).
* The BCG agent independently derived the same conclusion from the §2.4 flip technique: "in-circuit
  evaluations are recorded queries" is false as a property of the ROM. That derivation is not a
  theorem stated in BCG.

**Verdict:** BCG does not literally rule out our fixed relation. The stronger, system-specific
obstruction Thm O does, and fixed depth, fixed statement and a single verifier do not escape it:
the adversary of Thm O uses all of them.

## 2. Direction 2: relativized / arithmetized oracle models (AROM, ePrint 2023/587)

* **AROM (Def 4.1).** ro is uniform; wo holds the hash's wire values; vô is a uniformly random
  polynomial of individual degree d ≥ 2 that agrees with the validity predicate on the cube.
  * **Instantiation (§2.2):** vô ↦ the Cook–Levin arithmetization P_H of the hash, of total degree
    O(|H|). The paper calls this heuristic: a real P_H is not a random extension. It notes degree
    ≥ 2²⁵ for widely used hashes.
* **Results.**
  * Thm 6.5: ROM security is preserved in the AROM.
  * Lemma 9.1, Cor 9.3: straightline extraction for Micali.
  * **Thm 9.4:** zk-PCD of unbounded depth relative to ARO, asymptotic and classical.
  * Thm 8.1, the accumulation step: soundness O(√(t·d·(n+ℓ)(m+λ+w)/|F|)). The square root comes
    from a forking-lemma (rewinding) proof of Lemma 7.1.
* **Quantum.** §1.1 leaves a quantum-accessible AROM to future work. No QAROM paper was found
  through 2026.
* **Arnon–Yogev (ePrint 2025/329).** A relativized ROM with f-gates (Defs 4.1–4.2). XFS is proven
  only for 3-message protocols (Thm 5.6). Multi-round is open, and the authors cite BCG as an
  inherent limit.

**Cost if we switched.**
* The per-step circuit must interpolate over m+λ+w coordinates for each hash query and commit to a
  polynomial of degree (m+λ+w)·d·(n+2ℓ+1).
* The accumulator is about 2(m+λ+w+1) field elements. With w ≈ 10⁵ wires for a SHA-sized circuit
  in Ext12 that is roughly 10 MB (the agent's estimate, not measured). That is ≫ the 299 KB final
  layer, before the decider.
* An algebraic hash would shrink w, but it breaks U-7 (SHA-384 throughout), and the model's
  random-extension assumption is still not satisfied by any real hash.
* The classical √-loss would need |F| ≳ 2²⁵⁶·t·d·n·w. Ext12 (2³⁷⁰·⁹) is borderline even
  classically.

**Verdict: close.** There is no quantum theorem. The idealisation is no more justified than A-IC.
It does not fit SHA-384 or 300 KB.

## 3. Direction 3: accumulation and PCD in the ROM/QROM

| work | theorem | model | PCD status |
|---|---|---|---|
| BCMS20 (2020/499) | Thm 5.2; §3.3–3.4 | ROM pieces, PCD in the standard model | heuristic instantiation; "we do not prove post-quantum security of any construction in the ROM" |
| BCLMS21 (2020/1618) | Thm 5.3 | same | heuristic, constant depth |
| Fractal (2019/1076) | Thm 10.1 (QROM, one SNARG); Thm 11.5 | URS | recursion heuristic (fn 3) |
| CGSY24 (2023/1646) | Thm 5.1 (κ_PCD ≤ κ_ARG, no depth loss); Remark 5.2; §6.3 / Thm 6.5 | any oracle, classical, straightline (Def 3.6) | proven only for the **weak relativized NARK**, which puts every in-circuit query/answer pair in the proof (non-succinct). The real scheme rests on the §2.3 **conjecture** "attacks on the real scheme are no more effective than on the idealised one". |
| Arc (2024/1731) | Thms 4.3, 5.9, 7.1, 7.4 | ROM, classical | heuristic |
| BMNW (2024/474) | Thm 6.5; Remark 3.2; fn 4 | ROM, not QROM | heuristic, bounded depth |
| WARP (2025/753) | Thm 10.3 | ROM | heuristic; QROM conjectured (fn 1) |
| CMS19 (2019/834) | Thm 8.6 | QROM, one BCS proof | no composition |
| CDHZ (2025/2166) | Thm 11.3 | QROM, one step | no composition |
| osROM (2025/1663), Symphony (2025/1905) | — | classical, curve- or lattice-based | not hash-only |

**Verdict:** none proves hash-based PCD/IVC in any oracle model with a succinct proof, and none is
quantum. The only proven route, CGSY's weak relativized NARK, would carry all in-circuit hash
inputs of every layer. That is at least |π₀|, so it is dominated by simply sending π₀ (PROOF
Cor 6.5, ≫ 300 KB). CGSY §2.3's conjecture is the literature's name for what A-IC states.

## 4. Direction 4: standard-model Fiat–Shamir

* **CI-based Fiat–Shamir** needs a keyed, trapdoor hash and a *statistically sound* base proof:
  * Canetti et al. (2018/1004) Thm 5.8, with rbr soundness Def 5.3;
  * Peikert–Shiehian (2019/158) Thm 5.1;
  * HLR21 (2021/286) Thms 5.12 and 6.13;
  * JKKZ (2020/980) Thm 4.5, Cors 5.3 and 6.6, for GKR as a proof without a PCS;
  * CJJ (2021/808) Thm 1;
  * Guan–Yogev (2025/2328) Thm 1, non-adaptive and using iO-strength commitments.
* **HLR21 Remark 1.3:** these results do not apply to Kilian/BCS because of the Merkle
  commitment, and FS for Kilian "remains a fundamental open problem".
* **BBHMR19 (2019/997).**
  * Thm 4.1: an IOP for NP whose FS-Kilian is unsound for *every* hash.
  * Thm 3.5 / Cor 3.6: generic collision resistance of the Merkle hash cannot suffice.
* **Gentry–Wichs (2010/610) Thm 5.1:** no black-box reduction from any falsifiable assumption to
  adaptive SNARG soundness for NP.
* **No CI result exists for any unkeyed hash** (and CGH rules out CI for all sparse relations).

**Verdict: close.** SHA-384 cannot be used with any known standard-model instantiation. Any
standard-model statement about our system is a non-falsifiable SNARG-soundness assumption
(GW11).

**Related finding (KRS, ePrint 2025/118).**
* Thms 1–2, 9, 10: practical any-hash attacks on FS-GKR when the circuit computes the FS hash
  of its own transcript.
* §5: the exploited property is that "the prover does not commit to the full computation trace".
* Remark 3: canonical lookup/grand-product GKR circuits "do not seem" attackable.
* Our LogUp-GKR is a fixed fractional-sum tree run after the trace commitment, and SHA lives in
  the committed AIR. So the attack does not apply as written. This is worth an explicit audit
  line (§5, H-2).

## 5. Current focused investigation: G-P1

`LEMMA.md` §§5–7 is the current technical result. It separates three questions:

1. **Query-only obstruction.** Theorem O lifts an existing false concrete inner
   proof to an outer forgery, under explicit witness/inner completeness and
   outer query/completeness bounds. Its old numerical cap estimates and its
   universal “any oracle model” wording are withdrawn. A time restriction may
   exclude this route, but does not make concrete SHA equal an independent RO.
2. **Peeling.** The correct probability expression is
   `(sqrt(epsilon_inner + epsilon_outer_bad + delta_sim) + sqrt(slack))^2`.
   Its scalar derivation is kernel-checked. The actual family potential,
   extractor, NV faithfulness and inner assumption remain premises, not proved
   by that scalar theorem. Advice and preprocessing must be included in the
   inner game; a fixed accepting false pair can otherwise be hard-coded.
3. **Simulation cost.** The written G-P1-C argument gives a quadratic lower
   bound for a universal online fixed-interface circuit simulator, with
   arbitrary private quantum encodings. At 2^64 calls and 336-bit outputs,
   exact simulation needs more than 2^128 gates in the stated model. Lean
   checks the cone count and arithmetic, not the full quantum information
   argument. Independent review remains necessary. QRAM, uncharged feedback
   and adversary-specific reductions are outside this statement.

A generic collision or grinding work factor is not, by itself, a proof of an
accepted false statement for this concrete system. The earlier claim that a
quadratic simulator upper bound proves `S_(d-1)` false is withdrawn.

## 6. Claim and artifact boundaries

| Object | Current claim |
|---|---|
| Single/family outer layer | Correct conditional operator bound; actual protocol instantiation still open. |
| Recursive semantics | Separate conditional research theorem requiring a coherent model/game, faithfulness and resource accounting. |
| G2 artifact | FINAL is measured at 293,077 bytes; reproduction evidence lives in `results/pq-stream-commit/g2-gate`. No total security number is established by that measurement. |
| Deployed D3 admission path | R5 keeps it capped, without composition; the recursive A-IC assumption is not load-bearing for that path. |

The final/inner domain separation is already present in the pinned G2 code;
there is no outstanding H-1 architecture change to approve.

## 7. Scope decision (2026-10-21)

The user authorized the narrowly scoped G-P1 investigation, without changing the
construction. Its model-specific negative result is documented; it is not
promoted to a theorem excluding every possible simulation or reduction.
A-IC(τ) remains a proposed research endpoint requiring a coherent formulation,
not a proven consequence of the time bound or Theorem O. The actual family-QROM
and NV proof obligations must remain visible in the paper.

Keep U-7, SHA-384 throughout. No lattice or algebraic-hash wrapper is funded;
relaxing U-7 would require a separate user decision. R5's deployment decision
also remains unchanged.

## Files

* `LEMMA.md`: corrected Theorem O and peeling accounting; G-P1 cost model,
  written lower bound and its precise limits.
* `../../qrom/Qrom/Peeling.lean` and `QueryCost.lean`: scalar regression,
  finite cone counting and exact numerical consequences only.
