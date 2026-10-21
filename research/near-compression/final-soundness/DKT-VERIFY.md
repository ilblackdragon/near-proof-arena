# DKT26 verification for O-1 and O-2

Lane `lane/pq-dkt-verify` (from `lane/pq-mca-upgrade` @ 6841b5f56), 2026-10-18.

This document checks the DKT26 inputs that MCA-UPGRADE.md proposes for the PQ final-layer
soundness proof. The paper is Dao, Kominers and Thaler, ePrint 2026/2056. Its Lean development is
ArkLib at the paper's pin. Five questions are answered:

* Does the pinned ArkLib build?
* Which axioms do the cited theorems use?
* Do the Lean statements match the paper and the way MCA-UPGRADE.md uses them?
* Do the constants that bound_mca.py plugs in survive an independent re-derivation?
* Do the 36 integer certificates pass a check that is not the authors' Python?

Companion files:
* `lean/DKTAxioms.lean`, with its output `lean/DKTAxioms.out`: the axiom audit.
* `lean/DKTGlue.lean`, with its output `lean/DKTGlue.out`: Thm 5.12 composed with Cor 7.7 and
  Cor 7.8 in Lean.
* `lean/DKTCerts.lean`: all 36 certificates checked by the Lean kernel, with semantic theorems.
  * `lean/DKTCertsEval.lean` and `lean/DKTCertsEval.out` produce it: support counts and thresholds
    found by `#eval!`. The kernel re-derives all of them.
  * `calc/dkt_lean_certs.py` generates these files from `dkt_certs.json`.
* `calc/dkt_verify.py`, with its output `calc/dkt_verify.out`: an independent, exact-integer
  re-derivation of the O-1 Thm 5.12 numbers and of the O-2 query schedule. It does not import
  bound.py or bound_mca.py.

## 0. Verdicts

| item | verdict |
|---|---|
| **O-1**: DKT26 Thm 5.12 (Johnson line MCA), list (67), Cor 7.7 (interleaving), Cor 7.8 (folds); backend m = 3 → 64 | **Proven (Lean, no sorry), and the constants match. OK to cite as [P].** Every cited theorem uses only `propext`, `Classical.choice` and `Quot.sound`. The Lean error constant `johnsonE0` is exactly the constant bound_mca.py uses. Every number in the O-1 schedule re-derives exactly (§4). Caveat: O-1 as configured batches μ with three first-order curve certificates, which belong to the O-2 machinery. They pass the same Lean check (§5). |
| **O-2**: first-order beyond-Johnson certificates (36 codes) | **Proven (Lean, no sorry), and the constants match. OK to cite as [P].** All 36 certificates were re-checked by the Lean kernel with ArkLib's own decidable checker. For each one, the exceptional-set and list-size theorems were derived over every field of characteristic p. The Lean-evaluated bounds equal the JSON rationals exactly: 36/36 for E and for lists (§5). The citations need correcting: the certificates instantiate the factorwise-squarefree transfer (Lemma 5.6), not Thm 5.8 / Lemma 5.9 (§3.5). |
| **O-2 as implemented** (lane/pq-recursion-sha384 vk-bound `AgreementTable::canonical`, six real shapes; §8) | **All 129 certificates present and Lean-kernel checked** (93 round/fold sub-codes s ≤ k_i + 36 round-0 batching curves) in `calc/dkt_certs_o2.json`. The backend's integer rule is kept unchanged. The full bound passes for both finals, inner NV and the b = 2 chain. Base app stress needs round 0 at J64 (+2 queries, budget not certificate). The final's 301,157 B is backed. |

No gap was found in either item. The remaining caveats are in §6:
* the paper is still a preprint;
* the step from the RS-level MCA statements to WHIR is paper-level (Pus26 Thm 5.3), as before;
* no independent kernel replayed the proofs.

## 1. What was built

* **Source.** The pin `a5aa267` is **not** in `github.com/Verified-zkEVM/ArkLib`, so a fetch of
  upstream fails. It is the authors' fork, `github.com/quangvdao/ArkLib`, at commit
  `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, "Tighten Taylor bounds and strengthen capacity
  characteristic guarantees". The authors' README (rs-beyond-johnson @ 60b7257) names exactly this
  URL and commit as the paper's mathematical-source pin. MCA-UPGRADE.md / PROOF.md should cite the
  fork URL.
* **Location and toolchain.** The clone is in `/data/illia/nearproof-deps/arklib-dkt/ArkLib`,
  with a clean tree at the pin. The toolchain is `leanprover/lean4:v4.33.1`. Mathlib came from
  `lake exe cache get`: 8,690 files, none compiled locally.
* **Build.** `lake build` ran on `ReedSolomon.PaperGuide` (which imports every headline module),
  `FirstOrder.Squarefree.Sharp`, `CurveCertificate`, `HiddenDerivative.Parameters.Johnson.FiniteBounds`
  and `ProximityGenerator.BinaryTensorFoldAgreement`. Result: 4,128 jobs, **build completed
  successfully**. The cap was 24 GB, and MemAvailable never fell below 47 GB.
* **`sorry` in the build cone.** Five declarations in the dependency cone use `sorry`:
  * `Data/Fin/Basic.lean:327`
  * `Data/MvPolynomial/Interpolation.lean:250`
  * `ProximityGenerator/MCAGenerator.lean:265`
  * `ProximityGenerator/TensorGenerator.lean:278`
  * `ProximityGenerator/PolynomialGenerator.lean:287`

  **None of them is reachable from any theorem below.** `#print axioms` is transitive, and no cited
  theorem lists `sorryAx`.
* **Other escape hatches.** The ArkLib sources were searched for `skipKernelTC`, `native_decide`,
  `implemented_by`, `@[extern]` and `addDeclWithoutChecking`. None occurs; the only `unsafe` hits
  are aesop rule-priority annotations. The VCVio and CompPoly dependencies contain no
  `skipKernelTC`.
* **Untrusted code.** Nothing from the authors' repositories was run except the Lean build.

## 2. Axiom audit (`lean/DKTAxioms.out`, `lean/DKTGlue.out`, `lean/DKTCerts.lean`)

The check file is a classic (non-`module`) file, so that proof bodies are loaded and
`#print axioms` sees the full cone.

| paper result | Lean declaration (ArkLib @ a5aa267) | axioms | proof |
|---|---|---|---|
| Thm 5.12 (MCA set, any A ≥ an) | `ReedSolomon.exists_exceptional_johnson_lineMCA_allChar` | propext, Classical.choice, Quot.sound | full |
| Thm 5.12 (A = ⌈an⌉) | `ReedSolomon.exists_exceptional_johnson_lineMCA_at_ceil` | same | full |
| Thm 5.12, probability form | `ReedSolomon.johnson_lineMCA_probability` | same | full |
| Thm 5.12, weighted certificate form | `ReedSolomon.exists_exceptional_weightedJohnsonMCA_fullAgreement`, `weightedJohnson_mcaError_le` | same | full |
| (67), pairwise term | `ReedSolomon.closePolynomialSet_finite_and_ncard_le_johnsonPairwise` | same | full |
| Lemma 7.6 / Cor 7.7 (interleaving) | `ReedSolomon.uniformExactInterleavedPowerAgreement_of_scalar_arbitrary` | same | full |
| Cor 7.7 (lines, a fold level) | `ReedSolomon.fullSetLevelWitness_interleaved_of_exactAgreement` | same | full |
| Cor 7.8 (folds) | `TensorMCA.tensorFoldBad_card_le`, `TensorMCA.hasFullTensorDecomposition_of_not_mem_bad`, `ReedSolomon.interleavedRS_tensorFoldBad_card_le_heightThree` | same | full |
| Thm 5.8 / Table row (first order, asymptotic form) | `ReedSolomon.FirstOrder.firstOrderBranch_finiteLength_{finiteSlack_bounds, rate_bounds, mcaError_le}` | same | full |
| Lemma 5.6 / Cor 7.3 (squarefree curve MCA, raw) | `ReedSolomon.FirstOrder.Squarefree.exists_exceptional_retainedSquarefreeCurveMCA_sharp{,_at,_optimized}` | same | full |
| Prop 5.10 (certificate ⇒ interpolant) | `ReedSolomon.CurveProfile.LineProfile.CurveVerification.exists_certificate` | same | full |
| Prop 5.10 + Lemma 5.6, profile form | `ReedSolomon.CurveCertificate.exists_exceptional_exact_powerAgreement{,_squarefree_sharp,_squarefree_sharp_optimized,_squarefree_sharp_le,_best,_best_optimized}` | same | full |
| Lemma 5.11 (lists) | `ReedSolomon.CurveCertificate.finiteSquarefreeListBound_of_profile`, `finiteListBound_of_profile` | same | full |
| ours: Thm 5.12 → Cor 7.7 → Cor 7.8 | `DKTVerify.johnson_lineExact`, `johnson_levelWitness`, `johnson_tensorFold`, `o1_line_mcaError` (`lean/DKTGlue.lean`) | same | full |
| ours: the 36 certificates | `DKTCerts.mca0 … mca35`, `DKTCerts.list*` (`lean/DKTCerts.lean`) | same | full (kernel `decide`) |

No `sorryAx`, no custom axiom, and no `Lean.ofReduceBool` (that is, no `native_decide`) appears
anywhere. Every entry is a complete proof, not a bare statement.

## 3. Statement match against the paper and against MCA-UPGRADE.md's use

### 3.1 Thm 5.12 (O-1 line MCA)

| aspect | paper (p. 53, eqs. (65)–(68)) | Lean | MCA-UPGRADE.md / bound_mca.py | match |
|---|---|---|---|---|
| field | any field | `[Field F]`, any; `[Fintype F]` only for the probability form | q = p¹² | yes |
| evaluation set | any n distinct points | `domain : Fin n ↪ F`, arbitrary | ×15 cosets and their 2^s images | yes |
| characteristic | none | none | none | yes |
| range | 1 ≤ D ≤ n − 2, η₀ > 0, a = √ρ₋ + η₀ ≤ 1 | `1 ≤ D`, `D ≤ n - 2`, `0 < eta`, `johnsonAgreement ≤ 1`, `a·n ≤ A ≤ n` | D = k − 1 ≥ 63, A² > nD, A ≤ n (all asserted in dkt_verify.py) | yes |
| m, t, B_jet, B_Z | (65), (66) | `johnsonM`, `johnsonT`, `johnsonMu`, `johnsonH`: same formulas | same formulas | yes |
| error count | (68): B_cf = E_ord^(1)(D,A,n;B_jet,B_Z), the **Ψ_D form** (38) | `johnsonE0` = (2μ−1)h + θ(h + μ + **4Dμh**) + (n−D−1)μ | `max(e1, e2)`, where e2 = `johnsonE0` | see note |
| conclusion | full agreement-set MCA (exact witnesses) | `HasExactCorrelatedPair` ⇒ `IsMCA` (WHIR Def 4.9 / BCGM Def 3.14 form) | same | yes |
| probability | B_cf/|F| | `mcaError (AffineLineGenerator F) (code domain (D+1)) (1−a) ≤ min 1 (johnsonE0/|F|)` | E/|F| | yes |

**Note (constant).** The paper's (68) counts with Ψ_D(B) = 1 + (2D−1)(2B−1) + 2(B−2D−1)₊, and
the Lean theorem proves the bound with 1 + 4DB instead. Ψ_D(B) ≤ 1 + 4DB holds for all D, B ≥ 1:
* for B ≤ 2D + 1, Ψ = 4DB − 2D − 2B + 2;
* otherwise Ψ = 4DB − 6D.

So **Lean proves a slightly weaker constant than the paper prints**: `johnsonE0` ≥ B_cf.
bound_mca.py takes `max(e1, e2)`, which therefore always equals `johnsonE0`. **The constant used is
exactly the one Lean proves.** `DKTVerify.o1_line_mcaError` restates the Lean theorem with
η := A/n − √(D/n). It then needs only the integer hypotheses 1 ≤ D ≤ n−2, nD < A², A ≤ n, and
reaches radius 1 − A/n and error `johnsonE0 n D A η / |F|`: exactly bound_mca's reading. The
closed form 8nt³/(3ρ₋) of (68) is not used; dkt_verify.py nonetheless asserts E < 8nt³/(3ρ₋) for
every code.

### 3.2 List bound (67)

* The paper gives |L| ≤ min(B_jet, ⌊n(A−D)/(A²−nD)⌋).
* **Lean proves only the pairwise term**: `closePolynomialSet_finite_and_ncard_le_johnsonPairwise`,
  with hypotheses D + 1 ≤ A and nD < A². The docstring says the B_jet component is not supplied.
* At our parameters, **the pairwise term is the smaller one for every one of the 48 O-1 codes (three shapes)**
  (`calc/dkt_verify.out`: for example, final r0 has pairwise 3,917 against B_jet 3,996). So the
  lists bound_mca.py uses (2^11.94 … 2^15.43) are exactly the Lean-proved ones.
* Interleaved lists: ArkLib's `lambda_interleaved_rs_le_of_ratFunc_polynomial_agreement_bound`
  (Lemma 7.4 via F(Z)) together with the field-independent scalar bound gives the width-free
  transfer.

### 3.3 Cor 7.7 (interleaving)

* **Paper.** Assume a scalar full agreement-set curve MCA with count E_ℓ at A ≥ k. Then the same
  count holds at every width, with error E_ℓ/q. The proof is Lemma 7.6, which avoids at most q
  proper subspaces of F_q^s; their union has at most q^s − q + 1 < q^s elements. I re-checked
  this; it is sound.
* **Lean.** `uniformExactInterleavedPowerAgreement_of_scalar_arbitrary` covers any field, any
  `width > 0` and `k ≤ agreement`, and gives the same natural-number count. For lines at one fold
  level, `fullSetLevelWitness_interleaved_of_exactAgreement` takes a `LineExactAgreementBound` and
  returns the same count for every width and every family of parents.
* **Match.** Hypotheses and count match the paper. MCA-UPGRADE.md uses one scalar count per fold
  sub-round, with no width factor. That is what the Lean statement gives.
* **Glue.** ArkLib does not state Thm 5.12 *composed* with these transfers. `lean/DKTGlue.lean`
  proves the composition with count ⌊johnsonE0⌋₊:
  * `johnson_lineExact` gives Thm 5.12 in `LineExactAgreementBound` form;
  * `johnson_levelWitness` adds Cor 7.7;
  * `johnson_tensorFold` adds Cor 7.8: at most h·⌊johnsonE0⌋₊·|F|^(h−1) bad tuples, and the full
    tensor decomposition outside them.

  These hold for any finite field, any domain and any width, with no `sorry`.
* **Fold parametrisation.** Lean's fold is (1−r)u₀ + r·u₁, while WHIR folds as f_e + r·f_o. The
  bijective substitution u₀ = f_e, u₁ = f_e + f_o maps one to the other and preserves common
  agreement sets.

### 3.4 Cor 7.8 (multilinear folds)

* **Paper.** h levels sharing a challenge per level cost h·E/q. The proof is a union bound over
  levels with conditional uniformity, re-checked and sound.
* **Lean.** `tensorFoldBad_card_le` proves `card ≤ h·E·|F|^(h−1)` for one `ModuleCode` at every
  level.
* **Use.** WHIR's codes shrink from level to level, so bound_mca.py does not use Cor 7.8 for the
  fold. It charges every sub-round separately: Cor 7.7 for the code C^(i,s), with
  max_{s'} E(C^(i,s')) over s' = 0..k_i, which is conservative. Cor 7.8 is cited only for the
  unused "tensor" batching option. No mismatch.

### 3.5 First order (O-2) and the μ-batching curve

**What the certificates actually instantiate.** `dkt_certs.json` records
`transfer = sharp-squarefree-free-tail-taylor-tight-v3-*`. That is:
* the factorwise-squarefree transfer of **Lemma 5.6 / (55)**;
* with the ordinary threshold L₀ minimised independently;
* with the tight Taylor exponent τ = 2D − 3.

It is not the successive-stage objective (59) of Lemma 5.9. The matching Lean theorem is
`CurveCertificate.exists_exceptional_exact_powerAgreement_squarefree_sharp_optimized`:
* its hypotheses are `CurveVerification` (the Prop 5.10 row test, (63));
* the split L satisfies k ≤ L ≤ A ≤ n;
* 2 ≤ k < n, ℓ ≥ 1, 1 ≤ B∂ ≤ B_jet;
* the characteristic is 0 or exceeds max(k−1, B∂).

Lists come from `finiteSquarefreeListBound_of_profile`, which is Lemma 5.11's first branch.

**Mismatches in MCA-UPGRADE.md** (citation only; the numbers are unaffected):
1. §1.1 and §4 edit 4 cite Thm 5.8 / Lemma 5.9 / (59) and `firstOrderBranch_finiteLength_*`. The
   Branchwise theorems are the asymptotic-form bounds (7C³n/s², 140C⁶n²/s⁴); they are not what
   the 36 numbers instantiate. PROOF.md should cite instead:
   * DKT26 Prop 5.10 + Lemma 5.6 (+ Lemma 5.11, Cor 7.3, Cor 7.5, Cor 7.7);
   * the Lean `CurveCertificate.exists_exceptional_exact_powerAgreement_squarefree_sharp_optimized`
     and `finiteSquarefreeListBound_of_profile`;
   * this lane's `lean/DKTCerts.lean`.
2. `exists_exceptional_retainedSquarefreeCurveMCA_sharp_at` (cited in §4 edit 4) takes the
   interpolant `Q` and `Q_z(P) = 0` as *hypotheses*. The profile wrapper above discharges them
   from the certificate. Cite the wrapper.
3. "B∂ ≤ 192" (§1.1 and edit 3) versus "B∂ ≤ 52": the actual maximum over the 36 certificates is
   **B∂ = 52**. Both values satisfy p = 2³⁰·⁹ > max(k−1, B∂), so this is cosmetic.

**Characteristic and field.**
* The squarefree route needs p > max(k−1, B∂). The largest such value here is 2²¹ − 1, and the
  BabyBear Ext12 field has characteristic p = 2,013,265,921, so the guard holds.
* The hybrid route (`exists_exceptional_exact_powerAgreement`) would need p > max(k−1, B_jet).
  It is not used, and it would also hold.
* The field size enters only as E/|F|.

**Evaluation set and width.**
* All statements take an arbitrary `Fin n ↪ F`.
* Interleaving goes through `uniformExactInterleavedPowerAgreement_of_scalar_arbitrary`, whose
  hypothesis is exactly the conclusion of `DKTCerts.mca_i`.

**O-1 batching.** bound_mca.py's O-1 configuration with `batching = first-curve` (worst
non-query move 2⁻²⁸⁹·⁷) uses three first-order curve certificates at the *Johnson* agreement:
* ℓ = 140 at (2,013,265,920, 2¹⁹, 32,742,759);
* ℓ = 140 at (503,316,480, 2¹⁹, 16,371,380);
* ℓ = 600 at (2,013,265,920, 2²¹, 65,485,518).

So O-1 is not purely Johnson-regime. All three are among the 36 that pass §5.

## 4. Independent re-derivation of the O-1 constants (`calc/dkt_verify.py`)

**Method.** The script was written from the paper's (65)–(68) and the Lean `johnsonE0` definition.
Every ceiling is decided in exact integer or rational arithmetic, for example
m = smallest c with (D/n)(1+2c)² ≤ 4c²(A/n)², and B_jet = smallest c with c²D/n ≥ t², minus 1.
Agreements are A = ⌈(1 + 1/128)√(kn)⌉ (backend `ListDecoding { m: 64 }`) and A_s = ⌈A·n_s/n⌉.
Parameters: q = p¹² = 2³⁷⁰·⁸⁸, p = 15·2²⁷ + 1, and bound.py's shapes with n = 15·2^(log_h+b) in
every round.

**O-1 per-round results.** "max_s E/q" is over C^(i,s), s = 0..k_i; "list" is the pairwise term,
max over s. The bound_mca.out column shows the printed bits/query, q and fold MCA.

| layer | round | n | k | A | bits/query | q | m_DKT | max_s E/q | list | bound_mca.out |
|---|---|---|---|---|---|---|---|---|---|---|
| final | r0 | 2,013,265,920 | 2¹⁹ | 32,742,759 | 5.9422 | 40 | 64 | 2⁻³⁰⁹·⁶¹ | 2¹¹·⁹⁴ | 5.942 / 40 / −309.61 |
| final | r1 | ″ | 2¹⁸ | 23,152,627 | 6.4422 | 37 | 64 | 2⁻³⁰⁸·⁶² | 2¹²·⁴⁴ | 6.442 / 37 / −308.62 |
| final | r2 | ″ | 2¹⁵ | 8,185,690 | 7.9422 | 30 | 64 | 2⁻³⁰⁵·⁶³ | 2¹³·⁹⁵ | 7.942 / 30 / −305.63 |
| final | r3 | ″ | 2¹² | 2,894,079 | 9.4422 | 25 | 64 | 2⁻³⁰²·⁶³ | 2¹⁵·⁴³ | 9.442 / 25 / −302.63 |
| inner | r0 | 503,316,480 | 2¹⁹ | 16,371,380 | 4.9422 | 48 | 64 | 2⁻³¹³·⁵⁹ | 2¹⁰·⁹¹ | 4.942 / 48 / −313.59 |
| inner | r1 | ″ | 2¹⁸ | 11,576,314 | 5.4422 | 44 | 64 | 2⁻³¹²·⁶⁰ | 2¹¹·⁴³ | 5.442 / 44 / −312.60 |
| inner | r2 | ″ | 2¹⁴ | 2,894,079 | 7.4422 | 32 | 64 | 2⁻³⁰⁸·⁶² | 2¹³·⁴⁵ | 7.442 / 32 / −308.62 |
| inner | r3 | ″ | 2¹⁰ | 723,520 | 9.4422 | 25 | 61 | 2⁻³⁰⁴·⁸³ | 2¹⁵·³⁷ | 9.442 / 25 / −304.83 |

* Base stress also matches: 48/44/32/25, with worst fold 2⁻³⁰²·⁶³.
* **All values agree with bound_mca.out to every printed digit**, including the m_DKT column and
  the query sums 132 and 149.
* The query move leaves only 0.06 bits of slack in final r3 (25 × 9.4422 = 236.06). Integer
  rounding of A changes log₂(A/n) by less than 10⁻⁶ per query, so q is unaffected.
* MCA-UPGRADE.md's claims E/q = 2⁻³⁰²…2⁻³¹⁴ at m_DKT ≤ 64 and "(68) holds" are confirmed: the
  closed-form inequality is asserted for all 48 codes.

**O-2 schedule.** Agreements are A = ⌈r·√((k−1)n)⌉ at the plan ratios. Every needed sub-code
C^(i,s) has a certificate (none missing).

| layer | round | A | a/√ρ₋ | bits/query | q | max_s E/q (certified) | list |
|---|---|---|---|---|---|---|---|
| final | r0 | 27,128,239 | 0.835 | 6.2136 | 38 | 2⁻²⁸⁹·¹⁸ | 2⁴⁰·⁰⁴ |
| final | r1 | 18,792,001 | 0.818 | 6.7433 | 35 | 2⁻²⁸⁸·⁹⁹ | 2⁴⁰·⁹⁹ |
| final | r2 | 7,139,336 | 0.879 | 8.1395 | 29 | 2⁻²⁹²·⁵⁸ | 2³⁸·⁵⁵ |
| final | r3 | 2,205,154 | 0.768 | 9.8344 | 24 | 2⁻²⁸⁰·⁷⁴ | 2⁴³·³⁷ |
| inner | r0 | 13,271,719 | 0.817 | 5.2450 | 45 | 2⁻²⁹⁰·¹⁵ | 2³⁹·⁵⁶ |
| inner | r1 | 9,292,622 | 0.809 | 5.7592 | 41 | 2⁻²⁹⁰·⁶⁷ | 2³⁹·⁸² |
| inner | r2 | 2,570,043 | 0.895 | 7.6135 | 31 | 2⁻²⁹⁶·⁸¹ | 2³⁵·⁹⁴ |
| inner | r3 | 551,087 | 0.768 | 9.8350 | 24 | 2⁻²⁸⁷·¹⁷ | 2⁴¹·³⁷ |

* μ-batching curves: final 2⁻²⁸²·⁰⁵ and inner 2⁻²⁸³·⁰² (ℓ = 140).
* This matches MCA-UPGRADE.md: 38/35/29/24 and 45/41/31/24; bits/query 6.214 / 6.743 / 8.140 /
  9.834 and 5.245 / 5.759 / 7.614 / 9.835; worst E/q 2⁻²⁸⁰·⁷; lists ≤ 2⁴³·⁴; final A values.

## 5. O-2: the 36 certificates, re-checked in the Lean kernel (`lean/DKTCerts.lean`)

**Method.** ArkLib ships a decidable checker for finite first-order profiles. The ZisK, ProveKit
and LambdaVM examples use it. It is **not** the authors' Python. For each certificate
(n, k, A, ℓ, m, B∂, B_jet, B_Z) in `dkt_certs.json`:

1. **Support and surplus.** `verified_i : prof_i.CurveVerification`. This is the Prop 5.10 surplus
   (row test (63)) at the batching degree ℓ. The support dimension, local rank and height slots
   are recomputed from the support definitions.
   * The four large double sums are rewritten to a structural sum (`sumTo`, equivalence proved)
     and evaluated by `decide +kernel`.
   * The plain `Finset.range` form exhausted 24 GB of kernel memory at B_jet = 12,431.
2. **Exceptional count.** `envelope_i`: the Lemma 5.6 count at the ordinary threshold L₀ and the
   regular threshold L is at most ⌈E_json⌉, decided by the kernel.
   * L₀ and L were found by a convex search in `#eval!` (`DKTCertsEval.lean`). Only the kernel's
     `decide` is trusted.
   * In every case L₀ = k.
   * `opt_le_envAt` bounds the optimised envelope by the count at any admissible (L₀, L).
3. **Exceptional set.** `mca_i`. For every field F with `ringChar F = 15·2²⁷+1`, every domain
   `Fin n ↪ F` and every received curve of degree ℓ, there is an exceptional set of size at most
   ⌈E_json⌉. Outside it, every close candidate has exact power agreement on its full agreement
   set.
4. **List size** (the 31 line certificates; the five ℓ = 140/600 rows reuse line codes). `listq_i` and `list_i`: every finite family of close
   polynomials has at most list_json members.

**Results.**

| check | result |
|---|---|
| `CurveVerification` (Prop 5.10 surplus) | 36 / 36 pass |
| Lean Lemma 5.6 count vs JSON E | **exactly equal** (rational equality) for 36 / 36 |
| Lean Lemma 5.11 list vs JSON list | **exactly equal** for all 36 (the Lean `list_i` theorems are stated for the 31 ℓ = 1 rows) |
| `mca_i`, `list_i` axioms | propext, Classical.choice, Quot.sound |
| worst E/q | 2⁻²⁸⁰·⁷⁴, at (1,006,632,960, 2,048, 1,102,577) |
| worst list | 2⁴³·³⁷, at (2,013,265,920, 4,096, 2,205,154) |
| kernel run | `lake env lean lean/DKTCerts.lean`: exit 0, wall 30 min, peak 19.6 GB (cap 24 GB) |

So the authors' Python engine and ArkLib's Lean definitions agree bit for bit on all 36. The Lean
kernel independently confirms each certificate and turns it into a semantic MCA or list theorem.
The resulting values are the ones bound_mca.py reads.

## 6. Caveats that remain

* **Peer review.** DKT26 is still an unrefereed preprint four weeks old, with AI-assisted proofs.
  With the Lean check, correctness of the *statements used* rests on:
  * the Lean 4.33.1 kernel;
  * Mathlib (cache at manifest rev 0df444a);
  * ArkLib's VCVio and CompPoly dependencies;
  * the faithfulness of a few ArkLib core definitions: `IsMCA`/`mcaError`, `code`,
    `polynomialAgreementSet`, `HasExactPowerAgreement`. These were read and match WHIR Def 4.9.

  It no longer rests on the paper's proofs. Whether PROOF.md's [P] tag also requires refereeing is
  the policy question MCA-UPGRADE.md §5 already raised. This verification removes the technical
  part of that question.
* **WHIR binding is still paper-level.** The step from RS-level MCA and list statements to the
  WHIR round-by-round errors is Pus26 Thm 5.3 / ACFY. That step is unchanged by this lane and is
  not formalised.
* **No independent kernel replay.** The proofs were not replayed with an independent checker such
  as lean4checker or nanoda. The local lean4checker targets v4.29. The trust is that of Lean's own
  kernel at elaboration time.
* **Pinned shapes only.** `dkt_certs.json` covers bound.py's plan shapes. `dkt_certs_o2.json`
  (§8) covers the six real shapes of the recursion lane's O-2 table. If a shape changes, add it to
  `O2_SHAPES` in `dkt_certs.py`, rerun `--table`, then `calc/dkt_lean_certs.py eval|proof` with
  `DKT_JSON` and the Lean check.

## 7. Reproduce

```
# ArkLib at the paper pin (fork), Mathlib from cache
git clone https://github.com/Verified-zkEVM/ArkLib && cd ArkLib
git fetch https://github.com/quangvdao/ArkLib a5aa2677fee4e3a79d6bb05136631cce4a08587d
git checkout a5aa2677fee4e3a79d6bb05136631cce4a08587d && lake exe cache get
M=ArkLib.Data.CodingTheory.ReedSolomon
HEAVY_MEM=24G heavy lake build $M.PaperGuide $M.MutualCorrelatedAgreement.FirstOrder.Squarefree.Sharp \
  $M.MutualCorrelatedAgreement.CurveCertificate $M.HiddenDerivative.Parameters.Johnson.FiniteBounds \
  ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldAgreement
L=<worktree>/research/near-compression/final-soundness/lean
lake env lean $L/DKTAxioms.lean        # axioms (seconds)
lake env lean $L/DKTGlue.lean          # O-1 composition (seconds)
lake env lean $L/DKTCerts.lean         # 36 certificates (kernel; ~30 min, peak ~20 GB)
cd <worktree>/research/near-compression/final-soundness
python3 -I calc/dkt_verify.py           # O-1 / O-2 re-derivation
python3 -I calc/dkt_lean_certs.py eval > lean/DKTCertsEval.lean   # regenerate (after a shape change)
python3 -I calc/dkt_lean_certs.py proof lean/DKTCertsEval.out > lean/DKTCerts.lean
```

## 8. O-2 certificates for the implemented agreement table (`calc/dkt_certs_o2.json`)

**What this section adds.** lane/pq-recursion-sha384 @ cf2262a24 implements O-2 as a canonical
per-round agreement table that is bound into the vk (`AgreementTable::canonical`). Its check
`dkt_cert_check.py` found no real shape covered by `dkt_certs.json`, for three reasons:
* the grid's A was off by one at some sizes;
* fold sub-codes s = 3, 4 were missing;
* the domains 15·2²⁵ (inner NV) and 15·2²²/15·2²³ (b = 2 chain) had no certificates.

This section certifies exactly the integers that the backend binds, for every real shape.
**The NV lane consumes `research/near-compression/final-soundness/calc/dkt_certs_o2.json`**
(top-level keys `"n,k,A,ell"`; metadata in `_meta`, the per-shape table in `_shapes`, and
`_no_certificate`, which is empty).

### 8.1 The agreed integer rule

The rule is the backend's, unchanged (`stark-backend-unified.patch`, `AgreementTable::canonical`,
margin_milli = 50, m = 64):

    ratio = min(a1(ρ)/√ρ + margin_milli/1000, 1 + 1/(2m)),   ρ = k/n
    A     = ceil(ratio · √((k−1)/n) · n)                      (IEEE f64)
    fold sub-code s = 0..k_i:  (n >> s, k >> s, ceil(A / 2^s))  (exact integers)

`dkt_certs.o2_agree` reproduces it operation for operation. Python floats are IEEE f64; `sqrt`, `+`,
`*` and `/` are correctly rounded; `dkt_a1` uses the same bisection.

**It is sound for certification; no change is needed.**
* A certificate speaks about an integer A. The f64 arithmetic only selects which integer, and it
  is deterministic.
* Over all 28 rounds of the six shapes, the real-valued product `ratio·√((k−1)/n)·n` is at least
  0.013 from an integer. The f64 error is about 10⁻⁸, so f64, 80-digit Decimal and
  `bound_mca.agreement('F', ..)` give the same A. `o2_table_bound.py` asserts this.
* Rounding up only raises the agreement, which makes certification easier.
* The cap 1 + 1/(2m) = 1.0078 is never active here: the largest ratio is 0.877, at ρ = 2⁻⁵·⁹.
* Each fold sub-code keeps ρ and has agreement fraction ceil(A/2^s)/(n/2^s) ≥ A/n.

One remark outside the certificates: the query count `ceil(target / −log2(A/n))` uses libm
`log2`, which is not guaranteed correctly rounded. Platforms could disagree only when the quotient
is within about 1 ulp of an integer. That affects the canonical-table check's portability, not
soundness.

**Why the old grid was off by one.** The `--grid` mode built the s = 0 key as
`dceil(Decimal(A)/n · n)`. Finite-precision division rounds A/n up in its last digit, so the
product lands just above A and the ceiling gives A + 1. This happens for k = 2¹⁹, 2²⁰ and 2²¹ at
both 28 and 80 digits. `bound_mca.py` was never affected (it uses `Fraction`). The `--grid` line now
uses the exact `ceil(A/2^s)`. The stored `_grid` in `dkt_certs.json` is superseded and must not be
consumed for O-2.

### 8.2 Certified table per shape

Produced by `dkt_certs.py --table 1`. Every code was found by the same search as §5: smallest m
with E/|F| ≤ 2⁻²⁷⁵ and list ≤ 2⁴⁴, Taylor model tight-2D-minus-3-v3, squarefree transfer.
Searches took 0–3 s per code, and no code failed. q is `ceil(236/−log2(A/n))`. The "codes"
column counts the distinct (n, k, A) line codes over all rounds and sub-codes s = 0..k_i.

| shape (n) | round: A_i (k_i, q_i) | codes | worst E/\|F\| | worst list |
|---|---|---|---|---|
| final b7 h20 k4 lf7 (15·2²⁷) | 0: 37,140,791 (1, 41) · 1: 26,000,207 (4, 38) · 2: 6,325,509 (4, 29) · 3: 1,559,051 (4, 23) | 17 | 2⁻²⁸¹·¹⁹ | 2⁴³·¹⁴ |
| final bound.py b8 h19 k3 lf9 (15·2²⁷) | 0: 26,000,207 (1, 38) · 1: 18,228,420 (3, 35) · 2: 6,325,509 (3, 29) · 3: 2,210,990 (3, 25) | 14 | 2⁻²⁸³·⁶⁴ | 2⁴³·¹⁴ |
| inner NV b6 h19 k4 lf6 (15·2²⁵) | 0: 13,286,583 (1, 46) · 1: 9,285,185 (4, 41) · 2: 2,248,088 (4, 31) · 3: 552,545 (4, 25) | 17 | 2⁻²⁸⁷·⁴⁶ | 2⁴¹·¹⁴ |
| base stress b6 h21 k4 lf8 (15·2²⁷) | 0: 53,146,367 (1, 46) · 1: 37,140,791 (4, 41) · 2: 8,992,555 (4, 31) · 3: 2,210,990 (4, 25) | 17 | 2⁻²⁸³·⁴⁶ | 2⁴³·¹⁴ |
| chain inner b2 h20 k4 lf3 (15·2²²) | 0: 7,124,062 (1, 76) · 1: 4,930,246 (4, 65) · 2: 1,160,633 (4, 41) · 3: 280,951 (4, 31) · 4: 68,832 (4, 24) | 22 | 2⁻²⁹¹·⁴⁰ | 2³⁸·¹¹ |
| chain final b2 h21 k3 lf8 (15·2²³) | 0: 14,248,127 (1, 76) · 1: 9,860,497 (3, 65) · 2: 3,321,637 (3, 46) · 3: 1,139,244 (3, 35) · 4: 395,254 (3, 29) | 18 | 2⁻²⁸⁹·⁴⁰ | 2³⁸·⁶¹ |

Together that is 93 distinct line certificates (ℓ = 1). `calc/dkt_cert_check.py` is the recursion
lane's checker, copied with `_grid` made optional. Run on `dkt_certs_o2.json`
(`calc/dkt_cert_check_o2.out`), it reports **every round of every shape OK, 0 missing**. The
largest B∂ is 48 and the largest k − 1 is 2²¹ − 1, so the characteristic guard p > max(k−1, B∂)
holds everywhere.

### 8.3 μ-batching curve certificates (round 0)

bound_mca.py's 'first-curve' batching needs a powers-curve certificate of degree ℓ = W − 1 on the
round-0 code. `dkt_cert_check.py` does not test this; the table mode adds it.
* For every shape there are certificates at ℓ = 52, 140 and 600 (W = 53 for the b7 h20 final,
  141 for bound.py's NV shapes, 601 for the base). They exist both at the O-2 A₀ (18 certificates)
  and at the Johnson agreement of ListDecoding(64), A_J = ceil((1 + 1/128)·√(k/n)·n), for a round 0
  that falls back to O-1 (18 certificates, 3 of them reused from §5).
* Worst E/|F| at the O-2 A₀: 2⁻²⁷⁶·⁸¹, at ℓ = 600 on (15·2²⁷, 2¹⁹). At the W of the b7 h20
  final (ℓ = 52) it is 2⁻²⁸⁰·⁷⁶.
* **A degree-ℓ certificate covers any W ≤ ℓ + 1.** Pad the W words with zero words. The batched
  word is unchanged. In the exact power agreement that `mca_i` concludes, the polynomial attached
  to a zero word agrees with 0 on at least A > k points, so it is 0. Restricting to the first W
  words therefore gives the W-word statement. If the NV lane's W differs, use the next ℓ above
  W − 1.

All entries: 93 + 18 + 18 = **129** in `dkt_certs_o2.json` for the six shapes; 173 with the penultimate candidates of §8.7.

### 8.4 Full bound with these certificates, and the one fallback

`calc/o2_table_bound.py` (output `calc/o2_table_bound.out`) runs `bound_mca.layer` with the
canonical A for every round, batching 'first-curve', reading only `dkt_certs_o2.json`. It checks
three plans:
* **O-2**: every round first order, which is what the backend binds today;
* **r0=J64**: round 0 at the Johnson radius of m = 64, the other rounds first order;
* **all J64**: O-1 alone.

| shape | O-2: q (sum), worst non-query | verdict |
|---|---|---|
| final b7 h20 (W 53) | [41, 38, 29, 23] (131), 2⁻²⁷¹·⁶⁶ | **pass** |
| final bound.py b8 h19 | [38, 35, 29, 25] (127), 2⁻²⁷¹·⁶⁶ | **pass** |
| inner NV b6 h19 | [46, 41, 31, 25] (143), 2⁻²⁷⁴·²⁵ | **pass** |
| base stress b6 h21 (2 commits) | [46, 41, 31, 25] (143), **2⁻²³¹·⁷⁷** (logup α,β, L3.1) | **fail**: round 0 → J64 |
| chain inner b2 h20 | [76, 65, 41, 31, 24] (237), 2⁻²⁸¹·⁶¹ | pass |
| chain final b2 h21 | [76, 65, 46, 35, 29] (251), 2⁻²⁷⁸·⁶¹ | pass |

**The base fallback is a budget problem, not a missing certificate.** All 17 base certificates
exist.
* The pre-WHIR moves (L3.1–L3.7) are charged the round-0 list size to the power of the number of
  commitments.
* Under O-2, the round-0 first-order list is 2⁴¹·⁵⁶. With commits = 2 and logup over 2²⁶
  interactions, the logup α,β move reaches 2⁻²³¹·⁷⁷, against the budget of 2⁻²⁷⁰.
* With round 0 at J64 (list 2¹⁰·⁹¹), the layer passes at 2⁻²⁷¹·²⁷.
* Cost: round-0 queries go from 46 to 48 (+2). Rounds 1–3 stay O-2.
* For comparison, O-1 alone is [48, 44, 32, 25].

The single-commit shapes do not have this problem. For the finals the logup move is below the OOD
move.

**Consequences for the NV lane.**
* **The final proof is fully covered.** The b7 h20 final's table (A, q = [41, 38, 29, 23]) is
  certified and its bound passes, so the 301,157 B O-2 number is backed. The same holds for the
  inner NV layer and the bound.py final.
* **The base app layer (stress) needs the round-0 fallback.** The vk-bound table then needs a
  per-round regime, for example `regime: F | J(m)` per `AgreementRound` with round 0 = J(64)
  when the layer has more than one commitment. The alternative is to accept the J64 query
  count for round 0 only.
  * This changes the backend rule (the NV lane's decision), so this lane did not do it.
  * Byte impact: +2 round-0 queries in the base proof only. It does not enter the final proof's
    bytes. It only slightly enlarges the layer-1 verifier circuit's base-proof part.

### 8.5 Independent checks

| check | result |
|---|---|
| `dkt_cert_check.py dkt_certs_o2.json` | 0 missing, 0 recorded as not certifiable (`calc/dkt_cert_check_o2.out`) |
| `dkt_certs.py <engine> --check dkt_certs_o2.json`: authors' engine re-evaluation from the stored (m, B∂, B_jet), plus E/\|F\| ≤ 2⁻²⁷⁵, list ≤ 2⁴⁴, char guard | 129 / 129 ok (`calc/dkt_certs_o2_check.out`) |
| Lean `#eval!` of ArkLib's checker (`lean/DKTCertsO2Eval.lean/.out`) | `CurveVerification` true 129 / 129; Lean E and list **exactly equal** to the JSON rationals, 129 / 129 |
| Lean kernel proofs `lean/DKTCertsO2_{0..5}.lean` (§5 method, 6 interleaved slices) | **129 / 129 pass**: exit 0 on all six slices, no errors; 222 theorems (129 `mca_i`, 93 `list_i`), each depending only on propext, Classical.choice, Quot.sound (`lean/DKTCertsO2_{0..5}.out`); wall 12–32 min per slice (138 min total), peak 19.2 GB (cap 24 GB) |

### 8.6 Reproduce

```
cd <worktree>/research/near-compression/final-soundness/calc
JOBS=12 nice -n 10 python3 -I dkt_certs.py <rs-beyond-johnson@60b7257> --table 1   # ~1 min
python3 -I dkt_cert_check.py dkt_certs_o2.json
python3 -I dkt_certs.py <rs-beyond-johnson> --check dkt_certs_o2.json
python3 -I o2_table_bound.py
DKT_JSON=calc/dkt_certs_o2.json python3 -I calc/dkt_lean_certs.py eval > lean/DKTCertsO2Eval.lean   # from ..
DKT_JSON=calc/dkt_certs_o2.json DKT_CHUNK=i/6 python3 -I calc/dkt_lean_certs.py proof lean/DKTCertsO2Eval.out > lean/DKTCertsO2_i.lean
(in ArkLib) HEAVY_MEM=24G heavy lake env lean <worktree>/.../lean/DKTCertsO2_i.lean
```

### 8.7 Penultimate candidates (lane/pq-recursion-sha384 @ 3c4324e8c, `size_cut3.py`)

The recursion lane's best penultimate is (b 8, n_stack 18, k1 2, k 4, lf 6), so log_h = 20. It was
counted on Johnson because it was not in this file. It was certified on request, with the same rule
and process.

**Domain problem.** That shape's initial WHIR domain is 15·2²⁸. BabyBear has p − 1 = 15·2²⁷
(2-adicity 27), so no multiplicative subgroup of that order exists, and with an odd factor of 1
the domain 2²⁸ does not exist either. `ext.py` enforces `maxdom = 27` for the final-layer search,
but `size_cut3.py`'s penultimate loop (b up to 8, n_stack up to 18) does not. This is a
domain/spec question for the NV lane, so this lane did not choose a replacement. It also certified
the two realizable neighbours with log_h + b = 27.

| shape (n) | round: A_i (k_i, q_i) | codes | worst E/\|F\| | worst list | status |
|---|---|---|---|---|---|
| b8 h20 k1 2 lf6 (15·2²⁸, **not a BabyBear domain**) | 0: 52,000,438 (2, 38) · 1: 25,592,250 (4, 33) · 2: 6,273,989 (4, 26) · 3: 1,552,217 (4, 21) | 18 | 2⁻²⁸⁰·⁸⁸ | 2⁴³·⁸⁹ | 17 / 18; round 3, s = 0 has no certificate |
| b8 h19 k1 2 lf9 (15·2²⁷) | 0: 26,000,207 (2, 38) · 1: 12,796,101 (4, 33) · 2: 3,136,899 (4, 26) | 13 | 2⁻²⁸³·²¹ | 2⁴²·⁸⁹ | all certified |
| b7 h20 k1 2 lf6 (15·2²⁷) | 0: 37,140,791 (2, 41) · 1: 18,228,420 (4, 35) · 2: 4,453,003 (4, 27) · 3: 1,099,669 (4, 22) | 18 | 2⁻²⁸²·⁴² | 2⁴³·³⁷ | all certified |

Each shape also has round-0 curve certificates at ℓ = 52, 140 and 600, at A₀ and at A_J. That
makes 44 new entries, and **173** in total.

**The uncertifiable code** is (4,026,531,840, 1,024, 1,552,217), round 3 at s = 0 of the
infeasible shape.
* The list bound is the obstacle: the best is 2⁴⁴·⁵⁸ at m = 24 against the cap of 2⁴⁴, while E has
  margin (2⁻²⁸²·⁸⁶).
* On a 0.2 % grid, the smallest certifiable A is 1,561,531 (+0.6 %), and q stays 21.
* A certificate at a larger A does not cover the vk-bound A, so it is not stored. The round falls
  back to J64 (q 22, +1). `_no_certificate` records this.

**Bound** (`o2_table_bound.py`, NV inner parameters, W = 141, 1 commitment):

| shape | plan | q (sum) | worst non-query |
|---|---|---|---|
| b8 h20 | O-2 with r3 = J64 | [38, 33, 26, 22] (119) vs all-J64 [40, 34, 27, 22] (123) | 2⁻²⁷⁰·¹¹ (pass, thin) |
| b8 h19 | O-2 | [38, 33, 26] (97) vs [40, 34, 27] (101) | 2⁻²⁷⁰·²⁷ (pass, thin) |
| b7 h20 | O-2 | [41, 35, 27, 22] (125) vs [44, 37, 28, 23] (132) | 2⁻²⁷²·¹¹ (pass) |

**Bytes** (recursion lane model at 3c4324e8c: `size_cut3.py` run unmodified in a scratch copy, last
row "+ v4 child DAG", final b7 h20 O-2 throughout):

| penultimate | final |
|---|---|
| b8 h20 on Johnson (current figure; infeasible domain) | 287,037 B |
| b8 h20 certified (model counts round 3 at O-2 q 21; the J64 fallback adds 1 query there) | 286,285 B (−752) |
| realizable only (log_h + b ≤ 27), nothing new certified: best b8 ns17 k1 1, on Johnson | 287,413 B |
| realizable only, with b8 h19 / b7 h20 certified: best b7 ns18 k1 2, q [41, 35, 27, 22] | **287,037 B** |

So under the domain constraint, the certified, realizable penultimate gives the same 287,037 B as
the current (infeasible, Johnson) figure. The −752 B is available only if a 15·2²⁸ domain were
realizable, which it is not over BabyBear.

**Lean.** The 44 new entries (keys in `lean/DKTCertsO2_6.keys`):
* **`#eval!`**: `CurveVerification` is true for 44 / 44, and E and list are exactly equal to the
  JSON.
* **Kernel, 35 / 44 pass.** These are the 35 entries with B_jet ≤ 8,845
  (`lean/DKTCertsO2_small.keys`), checked in `lean/DKTCertsO2_6.lean` and `lean/DKTCertsO2_7.lean`.
  Both exit 0 with no errors, and 64 theorems depend only on the standard axioms. Wall times were
  11 and 17 min, peak 12.1 GB.
* **Kernel blocked for 9 / 44** (`lean/DKTCertsO2_big.keys`): the round-3 codes
  (k = 2¹⁰ → 2⁶, all sub-codes) of the two h20 k1 2 shapes.
  * Their supports are inherently large. A minimum-B_jet re-search, now stored, still needs
    B_jet 22,444–39,411; the earlier picks went up to 41,382.
  * A single certificate at B_jet 38,199 was OOM-killed at the 24 GB cgroup cap after 7 min. The
    first 22-certificate slice also hit the cap.
  * These 9 are checked by the authors' engine (`--check`) and by ArkLib's checker under `#eval!`
    (exact), but **not by kernel proof**. A kernel check would need a larger memory cap
    (probably 32–48 GB). That is the user's decision, so it was not attempted.

**Kernel-backed coverage.**
* b8 h19 is kernel-backed in full.
* For b7 h20, rounds 0–2 are kernel-backed. Round 3 is engine and `#eval!` only. With round 3 on
  J64 (q 22 → 23, no certificate needed), b7 h20 is fully kernel-backed. That costs about 0 B in
  the model: 1 query is about 330 NvAir rows, against the 6.4k-row margin under 2¹⁸.
* For the infeasible b8 h20, round 3 is J64 anyway.

All 173 entries pass the engine re-evaluation, and 164 have kernel proofs.

## Measured G2 FINAL scalar-fold transfer (2026-10-21)

`lean/DKTG2FoldCerts.lean` selects the 13 child-code certificates needed by the
recorded FINAL rounds (1, 4, 4, 4 binary folds). The generator
`calc/g2_fold_certificates.py` reads the measured round records through
`calc/audit_g2.py`, checks the pinned certificate inputs, and copies the existing
kernel proof bodies. It does not promote `#eval!` output into a theorem.

All 13 selected MCA theorems were checked by Lean 4.33.1 against ArkLib commit
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. `DKTWhirFold.lean` proves:

* the backend operation `u + (gamma-x)*(u-v)/(2*x)` equals ArkLib's binary fold;
* primitive even-order cosets give square-paired domains;
* the coset-major layout with an odd cyclic factor gives such a domain when the
  declared generator orders and coprimality conditions hold.

`DKTG2FoldTransfer.lean` composes each certificate with ArkLib's
`exists_parentPolynomial_of_exactAgreement`. It recovers the parent polynomial
and agreement threshold in the list regime, without unique decoding. Its exact
rational arithmetic proves that the sum of the 13 rounded exceptional-count
bounds, divided by `2013265921^12`, is less than `2^-283` (approximately 283.23
bits). All 30 audited declarations across these three files use only
`propext`, `Classical.choice`, and `Quot.sound`.

Recheck with:

```sh
research/near-compression/final-soundness/lean/check_g2_folds.sh \
  /data/illia/nearproof-deps/arklib-dkt/ArkLib \
  /data/illia/nearproof-deps/pq-security-lean
```

**Boundary:** this is a scalar-fold result for FINAL, conditional on the supplied
field/domain data. It is not full WHIR soundness. Still required are the actual
Rust domain/index/field correspondence; the history-dependent received-word
invariant and challenge law; initial multi-column batching; list-size products;
sumcheck, OOD, shift and final-query terms; and all parent/base family members.
`Qrom.Adaptive` supplies a classical adaptive counting lemma, but its premises
have not been instantiated for WHIR or replaced by a QROM reduction. The
`2^-283` figure must not be substituted for the total proximity or security error.
