# Prior-art check of the candidate novel findings (NF-1 … NF-10)

Lane `lane/novelty-prior-art`, 2026-10-18.

**Register checked.** `docs/research/NOVEL-FINDINGS.md` @ `lane/research-catalog` 58d9f096b.

**Method.**
* Each entry's evidence was read with `git show` at the commit the register cites.
* Literature sources:
  * ePrint and arXiv full texts, read for the cited sections. PDFs and text are in the session
    scratchpad.
  * Public code, cloned at the commits named below.
* The NF-1 code survey that names specific systems is in **RESTRICTED-NF1.md**.

**Verdict scale.** `known` / `incremental` / `searched-new`. "Searched-new" means the search
found nothing closer than the works cited. It is not a proof of novelty.

| id | verdict | worth | venue type |
|---|---|---|---|
| NF-1 | searched-new (as a QROM proof-gap observation); **no attack**; claim as registered is overstated | remark → short note together with NF-2 | ePrint note / workshop (e.g. ZKProof, FSE/ToSC short), or a section of the NF-3/NF-4 paper |
| NF-2 | incremental (mechanism = CMS19 App. B; classical case = Chiesa–Orrù 2025/536) | remark | same note as NF-1 |
| NF-3 | searched-new (attack: expected instance of CY21b's robustness requirement; Thm R + Thm 4: first IOP/QROM version) | **paper** (after independent review of Thm 4 / Thm R) | TCC / Crypto / Eurocrypt, or CiC |
| NF-4 | incremental (QROM analogue of CGSY24 Thm 5.1) | short note, or a section of the NF-3 paper | TCC / CiC |
| NF-5 | known (folklore; BCG24, CGSY24 §1.1.2) | remark | inside NF-4 |
| NF-6 | incremental (WHIR reference already has 3-smooth NTT + exact index sampler) | remark / lemma | systems paper appendix; upstream to WHIR |
| NF-7 | searched-new as an engineering data point (2.6× fewer cells than the only open SHA-512 AIR); the techniques are partly known | short note / systems-paper section | ePrint engineering note; ZK workshop |
| NF-8 | searched-new as a *data point* (no published proven-128-bit-QROM recursive size); modelled, not measured | short paper once measured | CiC / systems venue (USENIX Sec, CCS) |
| NF-9 | known to specialists | remark | — |
| NF-10 | known / incremental (LXYYZ 2026/2133 Tables 3–4) | remark | inside NF-8 |

---

## 1. NF-1: grinding credit when the PoW bits are not bound to the query block

### 1.1 Claim, as verified
Evidence read:
* `lane/pq-final-soundness` @ ae0ae8a7b: `final-soundness/PROOF.md` §5 Lemma 5.1, §6.4 and
  §6.5, and `GAPS.md` G-2;
* the fix in 46b7e62e2.

The transcript squeezes in two different ways (the "chained" and "single-output" patterns used
throughout this note):
* **Chained (the old code):** s′ = H(7, σ‖w). The verifier requires the leading z bits of s′ to
  be zero. The query indices come from later calls H(5, s′), H(5, H(5, s′)), ….
* **Single-output (T\*-2):** B_j = H(7, σ‖w‖j). The PoW is on the first z bits of B₁, and the
  indices come from the rest of B₁ and from B₂, B₃, ….

The project's Theorem 6.4 is a compressed-oracle "first flip" argument, the CMS19 §8.5 style.
It charges each oracle query the round-by-round error of the move that the query completes. It
gives:

| pattern | per-round error the proof can charge | resulting bound |
|---|---|---|
| single-output | 2⁻ᶻ·(1−δ)ᵗ (Lemma 5.1) | ≈ 2⁻¹³⁵ |
| chained | (1−δ)ᵗ; the PoW flip and the index flip happen at different oracle points and do not multiply | ≈ 2⁻¹⁰⁵ |

The chained row follows because the PoW is a separate verifier move with no prover message in
between. The rbr error of two consecutive verifier moves is the max of the two errors, not their
product (cf. CMS19 App. B).

**Correction to the register.** The registered claim says the z bits "give no provable
reduction … in the QROM". That is **overstated**. Correct statement: *the standard
rbr-to-QROM compilation (CMS19 Thm 8.6, CDHZ Thm 6.9/11.3, the project's Thm 6.4) does not
give the grinding credit for the chained pattern.* The credit is not shown to be false, and
§1.3 argues it is in fact true for every fixed prefix. The fix, T\*, is still the right
engineering choice. It costs 0 bytes and restores a proof under existing theorems.

### 1.2 Closest prior art

**ethSTARK documentation v1.2, ePrint 2021/582**
* §3.11.3 implements the chained pattern: a nonce hashed with the chain state, before the query
  randomness is generated.
* §6.3 Thm 6 analyses a "grinded IOP" in the single-output form: the verifier sends σ‖r, and
  state′ = 1 ⇔ state = 1 ∧ r = 0ᶻ.
* Thm 8 / Cor 3 lift this to T·maxᵢ εᵢ2^{−zᵢ} + 3(T²+1)/2^κ, **classical ROM only**.
* The gap between implementation and theorem is present but not remarked on. Closing it
  classically is routine (§1.3).

**Herold–Khovratovich–Kudinov–Tessaro–Wagner, "Aborting Random Oracles", ePrint 2026/016**
* §2.3 and §8 contain the only formal grinding analysis we found.
* Lemma 14: Adv ≤ Σ qᵢ(1−θᵢ)εᵢ.
* Cor 3: Hᵢ : {0,1}* → Cᵢ × {0,1}^{τᵢ} with f(α, 0^τ) = α. This is exactly the single-output,
  disjoint-bits pattern, classical, and it describes this as "grinding as implemented in
  practice".
* The quantum case is only sketched, for indifferentiability (App. A, Remarks 8 and 10). §2,
  "The Quantum Setting", says a direct quantum analogue is **an open problem**.
* The chained pattern is not considered.

**CMS19 (ePrint 2019/834) §8.6 and App. B (Hulett): the mechanism**
* QROM proofs need each round's message fixed in chain order.
* Thm B.3: strong rbr ≤ (k+1)^{1/(k+1)}·ε^{1/(k+1)}.
* Prop. B.4: that loss is tight *for the IOP property*.
* NF-1's lost credit is a 2-call instance of the same "two verifier moves, no product"
  phenomenon.
* CMS19 has no PoW.

**DFMS22, "Online-extractability in the QROM" (Eurocrypt'22, ePrint 2021/280)**
* Prop. 3.5 gives Pr[(x, RO(x)) ∈ R] ≤ 152(q+1)²Γ_R/2ⁿ. This yields the single-output credit
  directly.
* Thm 4.3 builds the extractable RO-simulator with commutator 8√(2Γ/2ⁿ). That is the tool for
  closing the chained gap (§1.3).

**Other works checked**
* BGKTTZ23, "Fiat–Shamir security of FRI and related SNARKs" (ePrint 2023/1071):
  * no grinding model (related work and the Plonky2 appendix only);
  * BCS used as a black box (Thm 3.15);
  * the quantum claims are inherited from CMS19.
  So it does **not** cover the chained pattern, even classically.
* Chiesa–Orrù, "A Fiat–Shamir transformation from duplex sponges" (ePrint 2025/536, TCC'25):
  * classical ideal permutation;
  * grinding appears only as a spongefish feature;
  * QROM open (§1.3).
* WHIR §6 and STIR §6 set PoW bits at the parameter level only.
* Bünz–Chen–Guan, "It takes two: proofs of work for Fiat–Shamir" (ePrint 2026/2326), abstract
  only:
  * relativized ROM;
  * grinding vs XFS PoW notions;
  * no QROM and no binding to the indices.
* GitHub: Plonky3 #200 records the chained design, discussing efficiency only. Nothing in the
  trackers of WHIR, spongefish, OpenVM or Stwo discusses binding or quantum grinding.

### 1.3 Attack or proof gap? (task item b)

**Classical ROM: no gap.**
* Exclude the event that some s′ equals an earlier query input. Its probability is ≤ T²/2ⁿ.
* Then each s′ that passes the PoW is fresh, and H(5, s′) is uniform and independent of it.
* The expected number of passing s′ is ≤ T·2⁻ᶻ. So Pr ≤ T·2⁻ᶻ·ε + O(T²/2ⁿ), the same as the
  single-output pattern.
* A toy lazy-sampling simulation agrees: chained 202.6 vs one-call 194.4, against an expected
  195.3 per 2·10⁵ trials at z = 6, ε = 2⁻⁴ (`scratchpad/exp/chain_vs_onecall.py`).

**QROM, fixed transcript prefix: no attack; sketch of a matching bound.**
* Fix σ and let the witness space W satisfy |W| ≤ 2^{n−z}. Real systems use 32–64-bit nonces
  and n ≥ 256.
* Given a random F = (a, b) : W → {0,1}ⁿ × C, simulate both oracles:
  * **g:** g(w) := a_z(w) ‖ π(w), with π a random injection W → {0,1}^{n−z};
  * **h:** h(ℓ‖u) := b(π⁻¹(u)) if ℓ = a_z(π⁻¹(u)), else r(ℓ‖u), with r an independent random
    function.
* (g, h) is distributed as two independent random oracles, up to the injection-vs-function
  distance O(t³/2^{n−z}).
* Each simulated query costs O(1) queries to F.
* A chained-pattern win becomes a search for x with lead_z(a(x)) = 0 ∧ Good(b(x)), a predicate
  of density 2⁻ᶻ·ε. By DFMS22 Prop. 3.5, Pr ≤ 152(t+1)²·2⁻ᶻ·ε.
* So for one prefix, the chained pattern is as strong as the single-output one. The natural
  attack strategies do no better than Grover on the joint predicate, at Θ(√(2ᶻ/ε)). Those
  strategies are: Grover-searching PoW-valid s′ first, claw-finding between g-outputs and good
  h-points, and querying h before g.

**QROM, with state restoration over many prefixes: open, but only as a proof.**
* The embedding cannot cover a 384-bit σ.
* Composing the per-prefix statement with the compressed-oracle potential of Thm 6.4 is not
  done by any published theorem.
* A naive sequential-capacity bound (CFHL21-style) gives O(t⁴·2⁻ᶻ·ε). That is a proof
  artifact, as the fixed-prefix reduction shows.
* A plausible closure:
  * simulate h on g-images with DFMS22's extractable simulator: h(y) := b(E(y)), using Thm 4.3
    (2.c, 4.a, 4.b);
  * this should give √Pr_chained ≤ √Pr_single + O(t²·2^{−n/2}).
* At n = 384 and t = 2⁶⁴ that additive term is ≈ c²·2⁻¹²⁸: just adequate. At n = 256 it is
  vacuous, which is one more reason to prefer T\* over arguing the old pattern. This is a
  sketch, not a theorem.

**Conclusion for (b).** A proof gap, not an attack. We believe the chained pattern is secure in
the QROM with essentially the same bound. The missing piece is a composition lemma.

### 1.4 Deployed systems (task item c)
* **Possible impact on 4 systems, as a proof gap only; no attack. See RESTRICTED-NF1.md.**
* Several other systems already use a covered pattern: a separate PoW hash plus reseed, which is
  equivalent to one long-output call.
* No affected system was found to claim proven QROM security that includes grinding credit.
  Most use permutation duplex sponges, for which no QROM Fiat–Shamir theorem exists anyway.
* **Disclosure assessment:** no coordinated disclosure is needed for security. The user decides
  on courtesy notices before publication. The register's `check` flag can move to
  `none-needed (proof gap; user to decide on courtesy notice)`.

### 1.5 Worth
* **Remark to short note.** The observation is new as written, but small.
* Publishable value comes if it is bundled with:
  * the fixed-prefix reduction;
  * a proved composition lemma: "chained ≈ single-output in the QROM";
  * the NF-2 counterpart.
* Best as a section of the NF-3/NF-4 paper, or as a short ePrint note on "binding PoW to
  challenges in QROM Fiat–Shamir".

---

## 2. NF-2: multi-call challenge squeezing

### 2.1 Claim, as verified
* Evidence: GAPS.md G-1 and PROOF.md §6.4–6.5. A query move needs 4–7 sequential blocks
  σ_{j+1} = H(5, σ_j), and an Ext12 sample needs 2 blocks about 54% of the time.
* The published QROM BCS theorems model one challenge as one oracle output:
  * CMS19 §8.2: one λ-bit output;
  * CDHZ 2025/2166 Def. 6.1: a long-output rndᵢ, i.e. counter mode;
  * HHMRS 2026/146 Thm 19: one block.
* So a chain is not covered. A worst-case-over-database transition gives ≈ ε^{1/k}.
* Counter mode, B_j = H(κ‖j), is covered: Lemma 6.3, at a cost of t → 2t. This adds 0 bytes,
  not literally "no cost".
* As with NF-1, ε^{1/k} is a loss of the *technique*. No attack is claimed or known.

### 2.2 Closest prior art
* **CMS19 App. B, Thm B.3 / Prop. B.4.** The same ε^{1/(k+1)} loss for "messages not fixed in
  chain order". Tight as an IOP property.
* **Chiesa–Orrù 2025/536.** Multi-block squeezing handled **classically** (§2.4 overview, Thm 1
  in §6: ε^sr + 25t²/|Σ|^c). §1.3 lists the QROM as open.
* **Fractal (2019/1076).**
  * §10.5 chains long inputs only.
  * §12.2.1 admits the implementation squeezes across several permutation calls ("omits some
    details"). This is an acknowledged but unaddressed instance.
* **Huang–Hülsing–Maram–Ritsch–Saha, "Feistel tools" (2026/146).**
  * App. G.1 Thm 19 covers duplex FS in the quantum random-permutation model, for 3-round
    protocols with one-block outputs.
  * §5 calls the general case open.

### 2.3 Verdict
* **Incremental.** The mechanism and the classical solution are known. The explicit QROM
  observation is not written down anywhere we found.
* The same extractable-simulator argument as §1.3, applied to each link of the chain, very
  likely closes it with additive O(k·t²·2^{−n/2}) terms.
* **Worth:** a remark, in the same note as NF-1.

---

## 3. NF-3: sub-collision-resistant Merkle digests in WHIR

### 3.1 Claim, as verified
Evidence: `lane/pq-weak-binding` @ 70bbb8c2e, `weak-binding/ANALYSIS.md`, `HROB.md` §0–§4 and
`REVIEW-1.md`. Three parts:
* **(i) Prop. 2.1, the attack.** WHIR Construction 5.1 and its implementations recompute the
  query answers y_{i,j} from the openings but sample γ_i before absorbing them.
  * With n-bit digests, an adversary fixes one equivocated leaf *after* seeing γ_i, so that the
    combined claim becomes honest.
  * The search is a Grover second preimage on one leaf, with success Θ(min(1, t²/2ⁿ)).
  * So n ≥ 256 is forced for that transcript order.
* **(ii) WHIR-Y.** Absorbing the y's before γ costs 0 proof bytes and about 90 extra verifier
  compressions.
* **(iii) Thm R + Thm 4.** For WHIR-Y, Thm R proves block-robust rbr soundness. Thm 4, a QROM
  BCS theorem tolerating K narrow collisions, then gives 26 B digests at c = 11 (net 39.4 KB).
  * Both theorems are unreviewed. Thm 4 has had one adversarial review (REVIEW-1).
  * [H-outer] is still open.

The registered claim is accurate.

### 3.2 Closest prior art
* **CY21b, "Subquadratic SNARGs in the ROM" (ePrint 2021/281, CRYPTO'21).**
  * Game 5.2 and Def. 5.3, "permuted robust soundness": the prover changes ≤ d blocks after
    seeing the randomness. This is the same quantifier as ε_rob.
  * Also relevant: Lemma 2.6 (collision score), Def. 6.5 / Lemma 6.6 (caps reduced to
    robustness).
  * PCPs and Micali only, classical only. §1 says "we leave it for future work to adapt [CMS19]
    to our construction".
* **CY21a (2021/188).** Classical collision and inversion budgets.
* **CMS19 Thm 8.6; CDHZ Thm 8.3.** Zero tolerance for collisions. CDHZ notes the t³/2^σ term is
  tight.
* **Hamoudi–Magniez (TQC'21) Prop. 4.3.** The closest database-level collision counting lemma.
* **Implementations.** The WHIR reference (worldfnd/whir @afec1fa,
  `src/protocols/whir/verifier.rs`) samples γ via `geometric_challenge` after reading the
  openings as unhashed hints. So the reference code has the same order as OpenVM v2. This is
  harmless at ≥ 32 B digests.
* **Checked, not relevant:**
  * Weak Fiat–Shamir (Dao–Miller–Wright–Grubbs, S&P'23): about statements left out of the hash;
  * Chiesa–Dall'Agnol–Guan–Spooner(–Yogev) 2023/1737 and 2024/1434: standard-model Kilian with
    binding commitments;
  * Chiesa–Hu 2026/2099: QMA;
  * SoK 2026/1367: survey.

### 3.3 Verdict
* **Searched-new.**
  * The attack is a natural, expected instance of CY21b's robustness requirement. It is new as
    a concrete statement about WHIR/STIR-style batching.
  * Thm R + Thm 4 would be the first multi-round IOP version of CY21b and the first QROM
    version. That fills a gap CY21b names explicitly.
* **Worth: paper,** conditional on an independent review, or formalisation, of Thm 4, Lemmas
  1–2 and Thm R, and on closing [H-outer].
* The attack plus the fix alone are worth a short note and a hardening suggestion upstream. It
  is not exploitable at today's ≥ 32 B digests, so no disclosure is needed.
* **Venue:** TCC / Crypto / Eurocrypt, or CiC.

---

## 4. NF-4: QROM straight-line knowledge soundness for families of recursive layers

### 4.1 Claim, as verified
* Evidence: PROOF.md Thm 6.4 (the "more strongly" clause), §7.3–7.4 Thm 7.4.
* One measured compressed-oracle database contains, except with probability
  ≤ (t′G + √(ℓ_V/2³³⁶))², **no** accepting transcript with failed extraction. This holds for
  every vk v and statement x at once.
* Hence recursion of any depth d costs no extra error. **This is conditional on A-IC**, the
  assumption that the in-circuit SHA-384 behaves as the RO.
* Accurate as registered, but the register should state the A-IC dependence.

### 4.2 Closest prior art
* **Chiesa–Guan–Samocha–Yogev, TCC'24 (ePrint 2023/1646).**
  * Thm 1 / Thm 5.1, proof idea in §2.1: one run, locate the bad vertex. The PCD knowledge
    error equals the single-argument error, with no factor of depth or graph size.
  * §2.3 / Thm 6.5: the "weak relativized SNARK" idealisation, which is the classical analogue
    of A-IC. §1.1.2 says it is a conjecture.
  * Classical only.
* **CDHZ 2025/2166.**
  * Thm 11.3: QROM straight-line extraction for one BCS step.
  * Thm 10.6: sequential composition roughly doubles the error per step. NF-4 avoids that
    growth.
* **CCGOS23 (2023/587) Thm 9.4.** Classical AROM unbounded-depth PCD; quantum left open.
* **Fractal (2019/1076).** Thm 10.1 is single-step QROM; Thm 11.5 covers constant-depth
  recursion only, with nested extractors.

### 4.3 Verdict
* **Incremental:** the QROM analogue of CGSY24 Thm 5.1, built on the CMS19 §8.5.2 / CDHZ
  extractor.
* New parts: the QROM setting, vk-indexed IOP families, truncated 42 B digests, and the
  "whole database" form.
* **Worth:** short note, or a section of the NF-3 paper. Cite CGSY24 for the classical result
  and for the A-IC-style idealisation.

---

## 5. NF-5: query-bounded security of hash-only recursion is impossible

### 5.1 Claim, as verified
* Evidence: `lane/pq-aic-research` @ 0079ed29a, `aic-research/LEMMA.md` (Thm O; Lemma E.3
  step 3 is only sketched).
* In any model that bounds only oracle queries, an unbounded-time prover hard-codes a false base
  proof that is valid under the concrete in-circuit hash, and then wraps it honestly.

### 5.2 Prior art
* **BCG24 (Barbara–Chiesa–Guan, TCC'25, ePrint 2024/728).** Thms 4.1/5.1/6.1 rule out
  relativized succinct arguments in the ROM.
* **CGSY24 §1.1.2.** Hash-based PCD in the ROM needs relativization, which they present as a
  conjecture.
* **Fractal §11 / CCGOS23.** Recursion needs heuristic instantiation.
* **The generic fact.** A fixed-verifier succinct argument cannot be sound against unbounded
  provers (Goldreich–Håstad; Goldreich–Vadhan–Wigderson; cited from memory).

### 5.3 Verdict
* **Known (folklore).** The explicit "lucky move" bound (Lemma E.2) and the three-way framing in
  Cor. O.2 are clean presentation, not new results.
* **Worth:** a remark inside NF-4.

---

## 6. NF-6: WHIR over ×15 cosets on BabyBear

### 6.1 Claim, as verified
* Evidence: `lane/pq-x15-domains` @ 2cf46f1a4, `x15-domains/SOUNDNESS.md`.
  * l.24–35: the four uses of smoothness (P1–P4).
  * l.49: BCGM Thm 9.2 holds for any evaluation set D.
  * l.69 and l.76: the exact sampler, which rejects at p−1 and then reduces mod 15·2ʲ.
  * l.114 and l.127: m = 3, because m = 8 misses 2⁻²⁶⁸ at Ext12.
* Accurate as registered.

### 6.2 Prior art
* **Papers.** BBHR18 (Remarks 1.4, 3.1), STIR §2 / Constr. 5.1 and WHIR (def. at l.876,
  Constr. 5.1) all define "smooth" as a power of two. None writes WHIR Thm 5.2 for c·2ᴷ.
* **Proximity gaps.** BCGM 2025/2051 Def. 3.8 / Thm 9.2 and BCHKS 2025/2055 hold for any D, so
  the domain-free part is direct.
* **WHIR reference implementation (WizardOfMenlo/whir).**
  * 1d392aa (2026-03-24), "Support non-power-of-two in NTT": `PRIMES = [2, 3]` at
    `src/algebra/ntt/cooley_tukey.rs:27`.
  * 2556d4e (2026-06-16): an exact rejection-sampled `IndexDomain` for non-power-of-two n
    (`src/protocols/challenge_indices.rs:38-80`).
  * The planner emits sizes like 12288 = 4096·3.
  * So mixed-radix (3-smooth) WHIR with an exact sampler already exists in code, though not
    ×5 / ×15 and not with a written proof.
* **Plonky3.** `sample_uniform_bits` with `ErrorOnRejection` is the same "reject the proof"
  idea, for power-of-two ranges.
* **Alternatives.** ECFFT II (2022/1542) and Circle STARKs (2024/278). ReedWeave (2026/2147,
  abstract only) relaxes smoothness by a factor m.

### 6.3 Verdict
* **Incremental.** What looks unpublished:
  * the written c·2ᴷ lemma;
  * the specific BabyBear ×15 choice, which gives +3.9 bits of domain for low-rate proof size;
  * the observation that the BCGM n²ρ^{−3/2} term forces m = 3.
* **Worth:** a remark or appendix lemma. Consider sending the lemma upstream to WHIR.

---

## 7. NF-7: SHA-512 compression AIR on a 31-bit field

### 7.1 Claim, as verified
Evidence: `lane/pq-sha384-air2` @ 971c41b5b,
`research/near-compression/results/pq384-sha-air2/README.md` (the register's path omits the
`research/near-compression/` prefix).

**Correction to the register.** The register says "171 + 13 columns". In fact
7,353 = 171 × 43 is the **main columns only**. The 13-column control/K table is a fixed 64 rows
(832 cells) per proof, not per compression. The cell figure is correct; the description is not.

Other figures, as measured:
* degree 21;
* 14 interactions per row;
* 144 next-row columns;
* 5,921/5,921 mutations detected;
* SHA-only prove time about 10× the bit-decomposed v1 on CPU.

### 7.2 Prior art: committed main cells per compression, counted from code

| system @ commit | hash | cols × rows | cells | cells/(round·bit) | degree |
|---|---|---|---:|---:|---:|
| **NF-7 v2.1 k=3** (BabyBear) | SHA-512 | 171 × 43 | **7,353** | **1.44** | 21 |
| NF-7 k=2 | SHA-512 | 231 × 43 | 9,933 | 1.94 | 9 |
| NF-7 v1 (bits) | SHA-512 | 442 × 44 | 19,448 | 3.80 | 4 |
| OpenVM sha2-air `Sha512Config` @e74f9b1ee (BabyBear) | SHA-512 | 903 × 21 | 18,963 | 3.70 | 3 |
| OpenVM sha2-air `Sha256Config` | SHA-256 | 456 × 17 | 7,752 | 3.79 | 3 |
| Plonky3 `p3-sha256-air` @576717ee9 | SHA-256 | 7,728 × 1 | 7,728 | 3.77 | 3 |
| Zisk `sha256f.pil` @1e22630bb (Goldilocks) | SHA-256 | 102 × 72 | 7,344 | 3.59 | — |
| SP1 ShaCompress + ShaExtend @02fa30185 | SHA-256 | 206×80 + 128×48 | 22,624 (incl. memory plumbing) | 11.0 | 3 |

Normalisation: cells / (rounds × word bits), i.e. /5,120 for SHA-512 and /2,048 for SHA-256.

**Sources**
* OpenVM: `crates/circuits/sha2-air/src/config.rs:7-11, 99, 143`; `columns.rs:33-149`.
* Plonky3: `sha256-air/src/columns.rs:92-212`.
* Zisk: `precompiles/sha256f/pil/sha256f.pil:36-40, 81-83`.
* SP1: `syscall/precompiles/sha256/compress/columns.rs:22-114`.
* There is no SHA-512 AIR in SP1, Zisk, stwo-cairo or Plonky3 at those commits.
* A web search (extended) found no published SHA-512 AIR cell counts on 31-bit or 64-bit fields.

**Techniques**
* Sparse, spread or digit word representations are well established:
  * halo2 table16 "spread" lookups;
  * PSE zkEVM Keccak sparse base-13 / base-9;
  * Cairo's diluted pool.
* All of those normalise digits with lookup tables. We found no AIR that evaluates
  XOR3/Ch/Maj as a polynomial of centred base-8 digits, with polynomial carry and range checks
  and no lookups, trading degree (21) for cells.
* Expression-valued bus messages (e.g. OpenVM `sha2-air/src/air.rs:364`) and zero-valid
  padding (`is_real` gating in SP1) are standard.

### 7.3 Verdict
* **Searched-new as an engineering data point.**
  * It uses 2.6× fewer committed cells than the only open SHA-512 AIR (OpenVM).
  * It uses 2.5× fewer per round-bit than every bit-decomposed SHA-256 AIR, which sit at about
    3.6–3.8. Degree-3 bit AIRs are near their floor of 3 cells per round-bit.
* The digit-polynomial evaluation is the one apparently new technique. The trade-off is degree
  21 and slower proving.
* **Worth:** a short engineering note, or a section of a systems paper. It needs a fair
  end-to-end comparison: prover time, and interaction columns under the same backend.

---

## 8. NF-8: narrow verifier circuit; ≈ 299 KB PQ final layer

### 8.1 Claim, as verified
Evidence: `results/pq-recursion-nv/README.md` @ 46b7e62e2 (l.163, l.217, l.225-231, l.280-281)
and the log `docs/logs/pq-final-layer-model-2026-10-17.md` @ lane/pq-native-hermetic.

What the evidence supports:
* a 69-column NvAir, against 3,481–3,923 columns in the OpenVM recursion port;
* 258 opened columns in total;
* a measured T = 20 chain at 171,797 B;
* **modelled** final layers of 308,547 B (power-of-two heights) and 298,881 B (padding-free).

Conditions the register omits:
* **The size is modelled, not measured.** The register says so; keep that.
* It is conditional on T\* and on A-IC for the recursive step. The register should state both.

### 8.2 Prior art (sizes and security models)
* **WHIR §6.3.4.** WHIR-JB is 299 KiB, by coincidence, but at 128-bit **classical** rbr with a
  256-bit hash. It is not recursive, and in that version it assumed a conjecture that BCGM later
  proved.
* **leanMultisig / leanVM (README @55f8b03).** 2→1 recursion at 200.5 KiB, stated as
  "128-bit ROM (64-bit QROM)".
* **soundcalc (ethereum/soundcalc @2af5e7d).** ZisK final 269/313 KiB and zkDTVM 200 KiB at
  128-bit JBR rbr with 248–256-bit hashes. OpenVM2 is 270 KiB at 100-bit. soundcalc does not
  compute the QROM correspondence.
* **RISC Zero succinct receipt.** About 200 kB at about 96–99 bits under a conjecture.
* **Fractal §13.1.** 80–160 kB in the ROM. Its QROM result is asymptotic only.
* **CDHZ 2025/2166.** A qualitative QROM theorem with no sizes.
* No published concrete size exists for a recursive hash-based proof with **proven 2⁻¹²⁸
  against 2⁶⁴ quantum queries**. That target roughly doubles the per-round bits (≈ 268) and
  needs 42–48 B digests.

### 8.3 Verdict
* **Searched-new as a data point.**
* The narrow role-multiplexed verifier AIR is good engineering, not a new idea: Fractal §12.2
  builds generic verifier circuits, and zkVMs use specialised recursion AIRs.
* The measured size laws are useful but project-specific.
* **Worth:** a short systems or parameter paper, *after* a measured final layer at real settings
  and with A-IC and T\* stated plainly. Venue: CiC, or a systems venue.

---

## 9. NF-9: lattice SNARK QROM obstruction

### 9.1 Claim, as verified
* Evidence: `lane/pq-lattice-qrom` @ eea80395b, `docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`.
* Ajtai commitments compress, so the witness is not determined by the oracle database. A
  CMS19-style database extractor therefore cannot give rbr knowledge for Ajtai-committed
  folding.
* Closing the gap needs a quantum forking or tree-rewinding lemma.

### 9.2 Prior art
* **Symphony (Chen, 2025/1905).**
  * §1 and fn. 2: rewinding-based lattice folding is secure only to constant depth.
  * App. B / Thm 5.1: a straight-line-extractable outer commitment is added for exactly this
    reason.
  * Classical.
* **DFMS22.** Online extraction works only for values committed through the RO.
* **Quantum rewinding results:**
  * LMS22 (2022/889);
  * CMSZ21/22;
  * CMNW 2024/281 §2.4, and App. B.6, which uses DFM20;
  * Chiesa–Dall'Agnol–Di–Guan–Spooner 2025/947.
* **Akita (2026/1983).** Classical. It says a QROM Fiat–Shamir theorem for its extraction tree
  is future work.

### 9.3 Verdict
* **Known to specialists.** Ajtai commitments are collapsing but not extractable, so extraction
  needs rewinding.
* The precise statement of the missing quantum lemma is a useful framing of an open problem.
* **Worth:** a remark.

---

## 10. NF-10: capacity regime vs Johnson regime cost at low rate

### 10.1 Claim, as verified
* The evidence is log l.254-284, which is **iteration 7, not 6** as the register says. Iteration
  6's "b−0.5" rows were withdrawn.
* LXYYZ (ePrint 2026/2133) Thm 1.1/4.14 needs m ≥ 4R(2−R)/ε² + 4(1−R)/ε.
* At ρ = 2⁻⁵ the bytes per security bit compare with Johnson-regime WHIR (m = 8 leaves) as
  follows:

| m used | bytes per security bit vs Johnson |
|---|---|
| proven m | 3.1–29.8× |
| conjectured m = 1/ε | 1.14–2.2× |

### 10.2 Prior art
* **LXYYZ 2026/2133 itself.**
  * l.204-212: m = O(1/ε²) is "the main bottleneck" for proof size.
  * Tables 3 vs 4: proven-capacity FRS IOPPs are larger than Johnson-regime FRI at λ = 100, e.g.
    818 vs 426 at R = 1/16. Their claimed gain is a smaller field, not smaller proofs.
  * **Counter-evidence for the conjectured half:** Table 5 uses a conjectured m = 4 at
    ε ≈ 0.11–0.14, i.e. m·ε ≈ 0.5. It *beats* FRI at low rate: 340 vs 426 at R = 1/16.
* **Goyal–Guruswami 2025/2054.** m > 4/ε².
* **Crites–Stewart 2025/2046 and Diamond–Gruen 2025/2010.** The up-to-capacity conjectures are
  false.
* **Folklore.** Johnson gives about b/2 bits per query and capacity about b.

### 10.3 Verdict
* **Known / incremental.**
* The proven-m half is already visible in LXYYZ.
* The conjectured-m half should be restated: "worse for m ≳ 1/ε, possibly better for
  m ≈ 0.5/ε (LXYYZ Table 5)".
* **Worth:** a remark inside NF-8.

---

## Recommended register updates (for the catalogue lane to apply)

| id | novelty | other changes |
|---|---|---|
| NF-1 | `searched-new` | Reword the claim to "the standard QROM compilation does not give the credit". Add closest prior art: ethSTARK 2021/582 §3.11.3 vs §6.3 Thm 6/8; HKKTW 2026/016 Cor 3 and §2 "Quantum Setting"; CMS19 App. B; DFMS22 Prop. 3.5 / Thm 4.3. Disclosure: `none-needed`, pending the user's decision on a courtesy notice; "no attack; possible impact on 4 systems as a proof gap; see restricted note". |
| NF-2 | `incremental` | Prior art: CMS19 App. B Thm B.3; Chiesa–Orrù 2025/536 (classical; QROM open, §1.3); Fractal §12.2.1; HHMRS 2026/146 Thm 19. Disclosure: `none-needed`. |
| NF-3 | `searched-new` | Prior art: CY21b Game 5.2 / Def. 5.3 / §1; CMS19 Thm 8.6; CDHZ Thm 8.3; Hamoudi–Magniez Prop. 4.3. Note that the WHIR reference has the same γ order. Next: independent review of Thm 4 and Thm R. |
| NF-4 | `incremental` | Prior art: CGSY24 (2023/1646) Thm 5.1, §2.3; CDHZ Thm 10.6 / 11.3; CCGOS23 Thm 9.4. State the A-IC dependence. |
| NF-5 | `known (folklore)` | Prior art: BCG24 Thms 4.1/5.1/6.1; CGSY24 §1.1.2. |
| NF-6 | `incremental` | Prior art: WHIR repo commits 1d392aa and 2556d4e (3-smooth NTT, exact non-power-of-two index sampler); BCGM Def. 3.8. |
| NF-7 | `searched-new` (engineering) | Fix the description: 7,353 = 171 × 43 main cells; the 13-column table is a fixed 64 rows. Fix the evidence path prefix. Comparator: OpenVM sha2-air SHA-512 at 18,963 cells. |
| NF-8 | `searched-new` (data point) | Add "conditional on T\* and A-IC". Comparators: WHIR §6.3.4, leanMultisig, soundcalc. |
| NF-9 | `known` | Prior art: Symphony 2025/1905; LMS22; CMNW 2024/281; Akita 2026/1983. |
| NF-10 | `known/incremental` | Evidence is iteration 7. Prior art: LXYYZ 2026/2133 Tables 3–5. Soften the conjectured-m claim. |
