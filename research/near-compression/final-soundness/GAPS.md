# Gaps, ratings and code-vs-proof mismatches

> **2026-10-21 correction (supersedes earlier ratings).** S-19 is OPEN: the
> previous family proof's `wide-bad` predicate classified legitimate chain
> edges as bad. S-20 is conditional on repairing and instantiating S-19 and a
> coherent recursive hash model. S-28 is OPEN at the actual list-decoding
> radii: `Udr/McaToGap.lean` does not supply that transfer. The Mathlib QROM
> capstone now correctly composes operators, amplitudes and probabilities, but
> has explicit protocol-specific premises; it is not closed except two citations.
> See `docs/research/pq-proven-soundness-paper-draft.md` Appendix C.


Companion to `PROOF.md` (lane `lane/pq-final-soundness`, 2026-10-18).

Ratings:
* **proven**: a published, refereed theorem applies as used.
* **proven-with-new-lemma-here**: the proof is written in PROOF.md, but it is new and has not
  been reviewed.
* **relies-on-unreviewed**: it rests on a preprint, a project note, or code and tests without
  a written proof.
* **open**: not proven, or contradicted by the code as written.

## A. Proof steps

| # | step | where | rating | notes |
|---|---|---|---|---|
| S-1 | Oracle split by framing, truncation (narrow 336 b / wide 384 b) | Lemma 1.1 | proven-with-new-lemma-here (elementary) | Node prefix under the 42-B lever is `NPQ5‖0x2a‖C‖ND`, not `NPQ4NODE` (SHA:35-37); still disjoint from the framed `n…` prefix. |
| S-2 | rbr-KS definition, list-form ⇒ rbr-KS, union over list | Def 2.1, Lemmas 2.3–2.4 | proven-with-new-lemma-here | Lemma 2.4 = HROB Lemma 4.7 at m = 0. |
| S-3 | Gruen rounds, derived claims, masked/zero claims, WHIR-Y absorption | Lemma 2.5 | proven-with-new-lemma-here | Gruen's own soundness remark is informal (ePrint 2024/108 App. A.3). |
| S-4 | LogUp α, β | Lemma 3.1 | proven-with-new-lemma-here (standard) | Proves balance **mod p** only; intended semantics pushed to NV-faithful (F4). |
| S-5 | Fractional GKR | Lemma 3.2 | proven-with-new-lemma-here (standard) | |
| S-6 | Zerocheck point = GKR point (implicit claims) | Lemma 3.3 | proven-with-new-lemma-here | Needed because ξ reuses GKR randomness. |
| S-7 | λ sampled before the per-AIR claims | Lemma 3.4 | proven-with-new-lemma-here | **Sound as is**, because λ only enters claim-independent terms and the claims are fixed before μ. |
| S-8 | Univariate-skip zerocheck | Lemma 3.5 | proven-with-new-lemma-here (standard) | d = 21. |
| S-9 | Program binding as part of the relation | Lemma 3.6 | proven-with-new-lemma-here | Without it a valid trace with a different program could pair with false program openings. NV must arithmetise V′ (F2). |
| S-10 | Stacking + tight heights kernel identities (multilinear form) | Lemma 3.7 (a), (b) | proven-with-new-lemma-here | |
| S-10′ | The same identities in the code's univariate-skip encoding (`chunk_factors`, rotation correction δ_i) | Lemma 3.7 remark | **relies-on-unreviewed** (code + 24 tamper tests) | If (b) were mis-encoded, transition constraints across chunk boundaries could go unchecked. Needs a line-by-line derivation or a Lean/symbolic check (G-6). |
| S-11 | Next-row mask | Lemma 3.8 | proven-with-new-lemma-here | Requires the mask ⊇ the DAG's offset-1 reads (keygen computes it). |
| S-12 | WHIR Thm 5.2 rbr (Johnson regime, list form) | Lemmas 4.3–4.7 | proven (WHIR, Eurocrypt 2025 / ePrint 2024/1586) | **Tartu corrections located and checked (lane/pq-mca-upgrade, MCA-UPGRADE.md §1.6):** Puškin, MSc thesis, Univ. of Tartu, Feb 2026 (hdl 10062/119861; full text via the DSpace bitstream). Its corrected Thm 5.3 (pp. 70–71) has the same ε^fold, ε^out, ε^shift, ε^fin as ACFY Thm 5.2; no term is larger. New explicit hypotheses: char F ≠ 2, list-decodability of every C^(i,s), s = 0..k_i, and the MCA radius B⋆(C^(i,s),2) ≥ ρ (printed as ≥ δ_i, a typo per its proof); all hold here. Its Thm 5.7 (smaller combination error, no ℓ factor) is **not** adopted. |
| S-13 | WHIR on 15·2^K domains | Lemma 4.1 | relies-on-unreviewed (x15 SOUNDNESS.md, re-checked here) | One definitional edit of WHIR's hypothesis. |
| S-14 | MCA in the Johnson regime, explicit constant | Lemmas 4.2–4.3 | proven (BCGM, CCC 2026; Def 9.1 / Thm 9.2 of the ePrint full version) | **Re-pinned:** the local copy is ePrint 2025/2051 v5 (19 May 2026, last of 5 revisions); Def 9.1 / Thm 9.2 / Lemma 9.3 are unchanged from the Feb 2026 version (word diff: typos only). The CCC 2026 paper (LIPIcs.CCC.2026.24) states it only as "Theorem 5 (informal)" and defers to the ePrint, so cite ePrint v5 Def 9.1 / Thm 9.2. Proposed replacement (MCA-UPGRADE.md): DKT26 Thm 5.12 + Cor 7.7 (S-26). |
| S-15 | Grinding inside one call | Lemma 5.1 | proven-with-new-lemma-here | **Holds only under T\*-2** (G-2). |
| S-16 | One-layer rbr-KS error ε_rbr = 2⁻²⁶⁸·⁰¹ (U-13; was 2⁻²⁶⁸·⁵⁵ under BCGM m = 3) | Thm 5.2, bound.py | **conditional on S-28 and exact transcript model** | Historical calculation. Worst move: WHIR query, round 1, final layer (236.01 + 32). Worst non-query: OOD r1, 2⁻²⁷¹·⁹. |
| S-17 | Counter mode ≡ one long-output call (t → 2t) | Lemma 6.3 | proven-with-new-lemma-here (elementary) | Needs T\*. |
| S-18 | Multiproof ⇒ per-leaf paths | Lemma 6.2 | proven-with-new-lemma-here | |
| S-19 | Family QROM instantiation | PROOF §6.4 | **open** | Repaired conditional operator theorem; concrete potential/transition/extraction proof and constants remain. |
| S-20 | Recursive composition | PROOF §7.4 | **conditional** | Needs completed S-19, NV faithfulness and a precisely modelled recursive hash bridge. |
| S-21 | NV circuit arithmetises V′_{i−1} faithfully | Lemma 7.1 (F1–F6) | **relies-on-unreviewed** (circuit lane, in progress) | Exact required form stated. |
| S-22 | Layer-0 AIRs encode chunk validation | Lemma 7.2 | **relies-on-unreviewed** | Out of scope here. |
| S-23 | Recursive in-circuit hashing (A-IC) | Assumption 7.3 | **model/assumption obligation** | Query-only obstruction is conditional; a runtime cap alone does not identify concrete SHA with an independent RO. |
| S-24 | Base-layer parameters (W, degree, interactions, commitments) | bound.py | **open** (not pinned) | A stress shape (W = 601, 2 commitments) passes at 2⁻²⁶⁸·⁵⁵. Re-run with the real app vk. |
| S-25 | Efficient extraction | §7.3 | proven (GS list decoding) / not needed | The theorem only uses existential extraction. |
| S-26 | **U-13 (adopted 2026-10-18), O-1:** line MCA at the Johnson radius √ρ(1+1/128) (backend ListDecoding m = 64): DKT26 Thm 5.12 with the Lean constant `johnsonE0`; list = pairwise term of (67) only; interleaving/fold transfer Cor 7.7/7.8 | Lemmas 4.2–4.4 | **proven (Lean)**: github.com/quangvdao/ArkLib @ a5aa2677 (`johnson_lineMCA_probability`, `closePolynomialSet_finite_and_ncard_le_johnsonPairwise`, `fullSetLevelWitness_interleaved_of_exactAgreement`, `tensorFoldBad_card_le`); Thm 5.12 → Cor 7.7/7.8 glue proven in lane/pq-dkt-verify `lean/DKTGlue.lean`; axioms propext/Classical.choice/Quot.sound only (DKT-VERIFY.md). Paper unrefereed. | O-1's μ-batching uses three first-order curve certificates (S-27), so O-1 as configured is not purely Johnson-regime. Base layer uses O-1. |
| S-27 | **U-13, O-2:** first-order (beyond-Johnson) list + line/curve MCA at a_i < √ρ_i: DKT26 Prop 5.10 + Lemma 5.6 (factorwise squarefree transfer), Lemma 5.11, Cor 7.3/7.5/7.7; 36 certificates (calc/dkt_certs.json; max B∂ = 52) | Lemmas 4.2–4.5 | **proven (Lean)**: `CurveCertificate.exists_exceptional_exact_powerAgreement_squarefree_sharp_optimized`, `finiteSquarefreeListBound_of_profile`; all 36 instances re-checked by the Lean kernel (lane/pq-dkt-verify `lean/DKTCerts.lean`, equal to the JSON rationals). Paper unrefereed. | Final [38, 35, 29, 24], inner [45, 41, 31, 24]; lists ≤ 2⁴³·⁴; per-round agreement table must be bound into the vk; regenerate for the final pinned shape. |
| S-28 | DKT-to-WHIR list-regime transfer | DKTGlue / paper §6.1 | **open** | RS-level Johnson/interleaving results exist; gated Udr utility requires unique decoding and does not close the actual WHIR transfer. |

## B. Code-vs-proof mismatches (tree U = stark-backend-unified, SHA = native_sha384_levers_config.rs)

| # | severity | what | where | consequence | fix |
|---|---|---|---|---|---|
| **G-1** | **proof gap (open)** | Challenges are squeezed through a sequential chain σ_{j+1} = H(5, σ_j); the challenge words are the chain states themselves. Query moves need 4–7 blocks; an Ext12 sample needs 2 blocks about 54 % of the time. | SHA:160-171 (in-circuit twin likewise) | No QROM theorem (CMS19, CDHZ, Thm 6.4) covers multi-call challenges. The worst-case-over-database transition loses ≈ ε^{1/k}. Not an attack: nested amplitude amplification suggests only a poly(k) loss, but that is unproven. The U-10 basis ("Grover-tight") silently assumed one call ([H-M] in the weak-binding notes). | **T\*-1**: B_j = H(5, κ‖le32(j)) from the post-absorb key κ; next state = last block consumed. 0 proof bytes, 0 extra compressions (input +4 B). Native verifier, prover and NV circuit must change together. |
| **G-2** | **proof gap (open); breaks the grinding credit** | PoW bits are the leading bits of the absorb output s′ = H(7, σ‖w); query indices come from later calls H(5, s′), … | SHA:142-186; U whir.rs:175-196 | Lemma 5.1 fails. The provable per-round error is the ungrinded 2⁻²³⁶·⁵⁵, which gives 2⁻¹⁰⁵ total: **fails U-6**. | **T\*-2**: B_j = H(7, σ‖w‖le32(j)); PoW on the first z bits of B₁; indices from the remaining words. Honest grind cost unchanged (1 compression per attempt). |
| G-3 | info | WHIR-Y present only in the unified tree | U whir.rs:315-320; absent from the levers-only and x15-only patches | None if production uses U. At 42 B, WHIR-Y is not needed for soundness (PROOF §4, Lemma 4.6 remark); it is needed for any digest < 256 b. | Pin U as the production tree. |
| G-4 | info | Node hashes carry no position or tree tag | SHA:91-99 | None at 42 B (K = 0 tolerates no collision anyway; |Chg| ≤ 3t′ accounted). Required only for weak-binding < 41 B digests. | — |
| G-5 | ok | λ sampled before the per-AIR claims | batch_constraints.rs:311 vs 315-320 | Sound (Lemma 3.4). | — |
| G-6 | relies-on-unreviewed | tight-heights kernel in the univariate-skip encoding | stacked_pcs.rs:90-103, stacked_reduction.rs:220-236 | See S-10′. | Write the derivation or check it symbolically. |
| G-7 | ok | ×15 sampler: native re-samples on p − 1, circuit rejects | U traits.rs:62-71; NV verifier.rs:244-249 | Both exact (Lemma 4.1). | — |
| G-8 | ok | Merkle multiproof | whir.rs:470-515 | Sound (Lemma 6.2); duplicate leaves must agree (checked). | — |
| G-9 | low | For a trace with common_main = 0, both `tight_height = None` and `Some(h)` pass, and the absorbed word count differs: the preamble encoding is non-injective. | proof_shape.rs:561-569; proof.rs:559-561; mod.rs:149-152 | Semantically irrelevant (no columns to chunk), so no state-function ambiguity. Malleability only. | Reject `Some` when common_main = 0. |
| G-10 | low | The verifier trusts the vk pre-hash (does not recompute it from the vk); `c` (odd factor) is `serde(skip)` and not in the pre-hash. | mod.rs:129; config.rs:203 | The verifier uses its own params, so it is sound. For recursion the pre-hash and all params must be constants of the parent program, and of the native V_d (NV-faithful F2). | Bind `c` in the pre-hash. |
| G-11 | low | PoW witness neither absorbed nor checked when bits = 0 | traits.rs:83-85; SHA:173, 182 | Proof malleability only (e.g. logup pow_bits = 0). | Require a zero witness. |
| G-12 | info | The soundness calculator ignores digest truncation, multi-target Merkle terms and WHIR-Y; its comment "Merkle proofs are observed before γ" is wrong. Its γ batch counts q + 1 in the final round (conservative). | calculator.rs:356-545, 482 | The calculator is not a proof. Use `calc/bound.py`. | Fix the comment; add the hash terms. |
| G-13 | info | Only the first WHIR round's fold is configurable (k₁); there is no per-round vector | config.rs:472-478 | Matches the analysed protocol. | — |

## C. What would close the contract

1. Validate the implemented T* transcript against the exact long-output model,
   including framing, PoW/index separation, caps, fanout and simulation cost.
   G-1/G-2 describe the historical source snapshot, not the later G2 run.
2. Complete the concrete family-QROM potential, transition counts and extraction
   proof (S-19); instantiate the repaired conditional operator theorem.
3. Complete the actual DKT-to-WHIR list-regime transfer (S-28). The RS-level
   ArkLib results are useful inputs; `McaToGap.lean` is a unique-decoding utility,
   not this transfer. Regenerate certificates for the pinned shape.
4. Prove NV-faithfulness (S-21), including the univariate-skip/stacking kernel
   (S-10′), and supply the base-relation theorem (S-22).
5. Specify and justify the recursive hash bridge (S-23), including its reduction
   loss and runtime. Adoption of A-IC(τ) does not prove its validity.
6. Pin the actual VK, parameters, sources and measured artifact; recompute every
   bound and reproduce the size measurement. For a universal size claim, prove
   capacity and serialized-size bounds over the entire permitted family.

The paper's Appendix C gives the target security game and completion evidence.
