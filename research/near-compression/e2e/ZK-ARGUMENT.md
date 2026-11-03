# Zero-knowledge argument for the chunk proof: construction, simulator, hiding error, cost

Status (2026-11-03, lane E2E-D, milestone D-2): **the masked protocol is built and measured; the
simulator and the hiding error are written below; `zero_knowledge_established=false`.** Two
lemmas of the composition (Lemma D and Lemma E, §6.2) are argued but not proved with a
strong bound. Both are about base-field cells absorbing extension-field functionals. Lemma E
comes from the PCS layer built on 2026-11-02: the per-column opened rows and the stacked
openings. Everything the 2026-11-02 version left open at the PIOP level is now built and
simulated: GKR, batch zerocheck, stacking sumcheck and column openings. Earlier versions of
this file are in git history; its §3 (PCS layer) is kept with one change (three more mask
columns, §3.1).

Mode: `WhirLevers::zk = 5` on the FINAL layer (`NEARPROOF_ZK_FINAL=5`). This is the PCS layer
of `zk = 2` with slice-splitting packing, plus the PIOP masks of §4. `zk = 4` is the same
without the splitting packing. The base layer stays `zk = 1`, and the inner NV levels stay
`zk = 0`. Patches: `native/recursion/patches/{zk-pcs,zk-piop}.patch`
(`make_zk_piop_patch.sh`). The shared definitions are in `stark-backend/src/zk.rs`.

## 1. What must be hidden, level by level

Only the packet is published: `claim.bin` (the statement), the hint (derived outputs, checked
against the claim), the base point `u`, and the FINAL proof. The setup is trusted and public.

| level | published? | must hide | why |
|---|---|---|---|
| base | only `u` (and `y = T_pub(u)`, which the verifier computes) | `u` must be simulatable | `u` is the RO output of the base transcript. Without randomness in the base commitment, `u` is a deterministic function of the witness, so anyone could test a guessed witness. |
| L1 … L_n | no | nothing | each is only the witness of the next level; the FINAL proof's ZK covers it |
| FINAL | yes | everything except its public values (level, statement digest), the shape, and the pinned program | its trace is the NV verifier run on L_n, so leaking the trace leaks L_n and hence the chain |

ZK at an inner level would not work. A ZK simulator programs the random oracle, but the next
level recomputes that oracle (SHA-384) inside its circuit. FINAL is the one proof whose
transcript is evaluated only natively, under its own transcript domain
(`ShaTranscript::new_layer(true)`). Programming the oracle at FINAL's points is therefore
consistent with every in-circuit evaluation. The recursion circuit is unchanged.

Public columns. The NvAir program columns `P0..P3` hold the pinned program, and V_d checks
their openings against it (`vd::check_final_program_at`). Their content is public, so their
plain openings are sent unmasked (`StarkVerifyingParams::zk_public_cols`, set for `zk >= 4`
keys from `PartitionedBaseAir::zk_public_columns`). A first full-ZK FINAL run that masked them
was rejected by V_d ("final program openings differ from the pinned program"). The shape
(trace heights) is fixed by the converged program and is part of the per-shape setup.

## 2. Leakage inventory of the FINAL proof and what hides each field (`zk = 5`)

| field | content | hidden by |
|---|---|---|
| `common_main_commit` | Merkle root of the stacked codeword | random reserved rows and mask columns in every leaf (§3) |
| `whir_proof.*` | functions of the batched polynomial `g` and of the opened rows | `g` is a one-time pad (§3.2); the opened rows are hidden by reserved rows and mask columns (§3.3, Lemma E) |
| `stacking_proof.stacking_openings` | stacked columns at `u` | reserved rows; mask columns' outer cells (Lemma E) |
| `stacking_proof` rounds | stacking sumcheck | committed-column Libra mask `M_1, M_2` (§4.3, Lemma D) |
| `stacking_proof.zk = [G_1, G_2]` | mask sums | uniform (Lemma D) |
| `batch_constraint_proof` uni-skip and rounds | batch zerocheck + LogUp | Libra mask `h_0, h_i` (§4.2, Lemma A) |
| `batch_constraint_proof.column_openings` | trace columns at `r` | last-variable column masks `A` (§4.2, Lemma C); public program columns unmasked |
| per-AIR LogUp terms | — | not sent: every AIR's numerator term has batching coefficient 1, its denominator term `μ` (§4.2) |
| `gkr_proof` root | `p_1(b), q_1(b)` (half sums), `q_0` (product of all denominators) | replaced by a masked root sumcheck; `q_0` not sent (§4.1) |
| `gkr_proof` layer claims and rounds | level MLEs at random points, layer sumchecks | level masks `α_k` (Lemma B); Libra masks `h_k` (Lemma A) |
| `logup_pow_witness`, PoW witnesses | grinding results | functions of the (simulated) transcript |
| `trace_vdata`, public values | shape, level, statement digest | public |
| packet `u` | base stacking point | base `zk = 1` (§3.4) |

## 3. PCS layer (built 2026-11-02; three more mask columns for `zk >= 4`)

### 3.1 Construction

* `zk = 1` (base): the common-main stacked layout keeps the last `R = 256` rows of every stacked
  column free. Packing is first-fit decreasing of the power-of-two slices into `2^h - R` rows.
  The prover fills the free rows with fresh uniform field elements, by rejection sampling of
  `/dev/urandom`. No trace slice lies there, so no PIOP claim weighs them.
* `zk = 2`: as `zk = 1`, plus `M = 12` appended stacked columns of uniform elements.
* `zk = 3`: as `zk = 2`, with slice splitting: a slice that fits no open column is halved.
  **Fixed 2026-11-03.** The halves used to be pushed to the front of the queue. A later
  full-size slice could then land at a fill pointer aligned only to the half size. That
  misaligned slice broke the stacking reduction's index arithmetic, which assumes every slice
  is aligned to its size, and the FINAL proof failed with `FinalSumMismatch`. The halves are now
  re-queued behind every remaining larger slice, so placements happen in non-increasing size
  order and alignment holds by construction (now a release `assert`). A toy with tight heights
  plus splitting reproduced the failure and now passes (`zk-selftest`, §8.1).
* `zk = 4, 5` (full ZK): `M = 15` mask columns. The last three (`M_s`, `M_1`, `M_2`,
  `zk::mask_columns`) carry the PIOP masks of §4. The other 12 are *pure*: no message other
  than WHIR refers to them. They keep the one-time-pad argument of §3.2 exactly as it was.
* Both sides compute the layout from the vk (`StackedLayout::new_tight_zk`). The lever is in the
  vk (serialized only when non-zero, so every existing key's pre-hash is unchanged) and in the
  proof's lever header, bits 1–3 of the `keep_domain` byte.

### 3.2 WHIR is hidden: `g` is a one-time pad

WHIR batches the stacked columns as `g = Σ_j μ^j c_j`, with `μ ∈ EF` sampled after the root.
The 12 pure columns `P_0..P_11` contribute `Σ_b μ^{j_0+b} P_b`. This is uniform in `EF^{2^h}`
whenever `1, μ, …, μ^11` are linearly independent over `F`, which fails with probability at
most `p^6/p^12 = 2^-185` (`μ` must avoid every proper subfield of `F_{p^12}`). So `g` is uniform
conditioned on every other column, except for the linear functionals of `g` that the rest of
the view fixes: the claimed `g(u)` and `g` at the opened positions. Every WHIR message after
batching is a deterministic function of `g` and the verifier's challenges: round polynomials,
fold oracles and their roots, OOD answers, opened fold values, the final polynomial, and PoW
witnesses. The simulator samples `g'` uniformly subject to those constraints and runs the
honest WHIR prover. This is the "batch with a random codeword" ZK of linear-code PCSs (Ligero,
Ames–Hazay–Ishai–Venkitasubramaniam CCS'17 §5; Aurora, EUROCRYPT'19; Plonky3 `HidingFriPcs`).
Unlike HVZK-WHIR (eprint 2026/391) it needs no mask oracles and no extra queries.

### 3.3 Opened initial rows, stacked openings and the root

Each query reveals every stacked column's codeword symbols at its coset, two points with
`k_first = 1`. The stacking reduction also reveals each column's evaluation `q_k(u)`.

* Trace columns: the `R = 256` reserved cells are, after the triangular eval→coefficient
  transform, the coefficients of the top block. The 92 opened symbols are Vandermonde rows on
  those coefficients at distinct base-field points, which have rank 92 deterministically. The
  12 F-components of `q_k(u)` restricted to the block span `EF` except with probability at most
  `2^-154` (Lemma S, §6.2). Joint independence of the two is Lemma E.
* `M_s`, `M_1`, `M_2`: the same functionals are absorbed by their cells outside the PIOP-mask
  region, which number `2^21 - 16·N_coef`.
* Pure pad columns: uniform outright.

Every Merkle leaf carries `15 · 31 = 465` bits of fresh entropy, from the mask columns' symbols.
That makes unopened leaves and the root hiding in the ROM without a separate salt.

### 3.4 Base point `u`

With `zk = 1` the base root is a RO hash of leaves that carry fresh randomness. So `u`,
squeezed after the root, is uniform and independent of the witness except with probability
`q · 2^{-336}`. The simulator samples `u` uniformly and computes `y = T_pub(u)` and the
statement digest itself.

## 4. PIOP masking (built: `zk-piop.patch`, `WhirLevers::zk >= 4`)

Every mask is an extension-field coefficient. Each one is stored in `D = 12` base cells of the
mask column `M_s`, at stacked rows `16k .. 16k + 11` for coefficient `k` (`zk::MaskCoefs`), and
is uniform because `zk_fill` fills `M_s` uniformly. The masks are fixed by the commitment,
i.e. before every challenge. Each masked sumcheck ends in a **sparse claim**
`Σ_i w_i · coef[c_i] = V`. The verifier derives the value `V` from the sumcheck's final check;
`V` is never sent. The stacking reduction proves all sparse claims together with the
column-opening claims. Coefficient allocation is deterministic from the shape, and the prover
and verifier compute it identically (`GkrZkLayout`, `BatchZkLayout`). FINAL uses 1,217 GKR
coefficients plus about 500 batch coefficients, which is about 21 K cells of `M_s`'s 2 M.

### 4.1 Masked GKR (`verify_gkr_zk`, `fast::gkr::fractional_sumcheck_fast_zk`)

LogUp GKR over `K = l_skip + n_logup` levels (`K = 27` for FINAL). Level `k` has `2^k` nodes,
with `p_k(b, y)` and `q_k(b, y)` where `b` is the newest coordinate. The layer relation is
`p_k = p_{k+1}(0,·)q_{k+1}(1,·) + p_{k+1}(1,·)q_{k+1}(0,·)` and `q_k = q_{k+1}(0,·)q_{k+1}(1,·)`.

* **Level masks** (off the cube, last coordinate): for `k ≥ 2`,
  `p̃_k(b, y) = p_k(b, y) + y_last(1 − y_last)·α^p_k(b)`, and likewise `q̃_k`. Here
  `α_k = (α^p(0), α^q(0), α^p(1), α^q(1))` are uniform coefficients. On the cube nothing
  changes, so every layer relation still holds. The claims the prover sends for level `k`, at
  `(b, ρ_{k-1})`, are masked by `Z_k α_k(b)` with `Z_k = ρ_last(1 − ρ_last) ≠ 0`. Level 1 is
  masked by `b(1 − b)·α_1`.
* **Root**, replacing the upstream `p_1(0..1), q_1(0..1), q_0` messages that leaked half sums
  and the product of all denominators: a one-variable sumcheck for
  `Σ_b p̃_1(b)·q̃_1(1 − b) = 0`, with Libra mask `g_R` (degree 4; the prover sends `G_R`, then
  `s_R(1..4)`). It ends in `P = p̃_1(β)` and `Q = q̃_1(1 − β)` at a fresh `β`. The upstream
  check `q_0 ≠ 0` is dropped. Some leaf denominator is zero, as a polynomial in the LogUp `α`,
  with probability at most `2^27/|EF| = 2^-343`, because the trace is committed before `α`.
  With all denominators non-zero, `p_0 = 0` ⟺ `Σ p/q = 0`.
* **Layer 1** (one variable `y`): the summand is
  `eq(β, y)[φ_p + M_1] + λ eq(1 − β, y) φ_q + ρ h_1(y)`, with claim `P + λQ + ρH_1`. `h_1` has
  degree 5, and the round has degree 5 (the prover sends `s(1..5)`).
* **Layer `k ≥ 2`**: the upstream Gruen sumcheck of `eq(ξ, y)[φ_λ + M_k + ρ h_k(y)]`, with claim
  `C_k + ρH_k`. `M_k = Z_k(α^p_k(μ) + λα^q_k(μ))` makes the identity hold for the masked
  claims. The Libra mask is `h_k = Σ_i h_{k,i}(y_i)`, with degree 2 per variable and 4 for the
  last one. All rounds except the last are unchanged in the prover: the mask of level `k+1`
  vanishes while `y_last` is Boolean. The last round has a quartic reduced polynomial (the
  prover sends `s(1..4)`) and is evaluated from the two remaining table entries.
* Each sumcheck's final check defines `V = s(r)/eq − φ(claims)`, the sparse claim
  `V = M + ρ h(r)`. The GKR output `p̃(ξ), q̃(ξ)` carries the input-level mask `M_K`, which the
  batch sumcheck absorbs.

Proof format (`GkrProof::zk`): `[G_R, s_R(1..4)]`, `[H_1, s(3..5)]`, and per layer `k ≥ 2`
`[H_k, s_last(3), s_last(4)]`. `claims_per_layer[0] = (P, Q)`, and no claim is derived. Cost
about 4 EF per layer.

### 4.2 Masked batch sumcheck (`verify_zerocheck_and_logup_zk`, `finish_zerocheck_and_logup_zk`)

* **No per-AIR LogUp terms.** Every AIR's numerator term is batched with coefficient 1 and its
  denominator term with `μ`; the zerocheck of AIR `t` uses `μ^{2+t}` and the mask `μ^{2+T}`.
  The claim is `p̃(ξ) + μ(q̃(ξ) − α) + μ^{2+T} G_b`. This is sound because the GKR needs only
  the sums.
* **Libra mask** `g(X, y) = h_0(X)·eq(ξ_y, y) + eq_D(ξ_0, X)·eq(ξ_y, y)·Σ_i h_i(y_i)` (`G_b`
  is sent before `μ`), plus the GKR input mask `eq_D·eq_y·M_K`. `h_0` has the full uni-skip
  degree 30, and every round keeps its `eq1(ξ_i, X)` factor, so Gruen still applies.
* **Column masks:** every column of AIR `t` is masked in the AIR's *last* multilinear variable:
  `f̂ = f + y_{n_t}(1 − y_{n_t})·A`, with one coefficient `A` per opening (plain and rotated).
  The uni-skip round and every round before `n_t` are unchanged. In round `n_t` the AIR's
  contribution has degree `2d`, and the prover evaluates it from its two-row tables. The other
  AIRs' degree-`d` part is extended by interpolation (`LogupZerocheckRowMajor::
  zk_masked_last_round`). That round sends `d` more evaluations (`BatchConstraintProof::zk`).
  Opening `t̂ = t + Z_t A` with `Z_t = r_{n_t}(1 − r_{n_t})`. Masking the uni-skip variable
  instead (`Z_D(X) = X^4 − 1`) would need extension-field masks inside the base-field round-0
  evaluator.
* Sparse claim `V_b` = the mask's value at the final point; each opening's mask enters the
  stacking claim of its column.

### 4.3 Masked stacking reduction (`verify_stacked_reduction_with`, `prove_stacked_opening_reduction_zk`)

* Before the batching `λ`: two points `τ_1, τ_2` are sampled, and the prover sends
  `G_j = M̂_j(τ_j)`, the prismatic evaluations of the mask columns `M_1, M_2`.
* The claims are the column openings, now with their mask terms, then the sparse claims, then
  `G_1, G_2`, all batched by powers of `λ`. The summand gains
  `E·M_s + λ_1 eq_prism(τ_1,·) M_1 + λ_2 eq_prism(τ_2,·) M_2`, where `E` collects the batched
  sparse weights on the coefficient cells.
* Per round, `M_j` contributes the fresh direction `eq1(τ_{j,i}, X)(X − τ_{j,i})`. Two distinct
  `τ`s span the round-polynomial space allowed by the sum check.
* The final check gains the `M_s` coefficient `Σ_k w_k Σ_b β_b δ_{16k+b}(u)`
  (`zk::ms_coefficient`, one eq table over the coefficient index) and
  `λ_j eq_prism(τ_j, u)` on `M_j`. No new opening is sent.

### 4.4 Soundness of the masked protocol

No new commitment is added. Every mask is committed before every challenge, and every new
check is a polynomial identity of bounded degree. Per-round degrees: GKR up to 5 (masked last
rounds, layer 1), batch up to `2d + 1 = 19`, root 4. The new batching coefficients are `ρ_*`
(Libra, degree 1), `μ^{2+T}` (degree `T + 2`), and the stacking `λ` powers over `K + 3` more
claims. `SoundnessCalculator` charges these under `zk >= 4`. The bits the patched calculator
reports for the FINAL setup are listed in §7. The minimum is unchanged: the WHIR query term,
268.2 bits at the pinned target.

## 5. Proof sizes (measured, §7)

| | non-ZK (10-31) | PCS-ZK (`zk = 2`, 11-03) | full ZK (`zk = 5`) |
|---|---:|---:|---:|
| FINAL packet, chunk 1 | 306,839 | 325,613 | **319,695** |
| FINAL packet, chunk 2 | 307,314 | 324,534 | **320,464** |
| FINAL packet, chunk 3 | 307,427 | 326,243 | **319,779** |
| stacked columns | 53 | 95 | 68 (53 + 15 mask, split packing) |
| FINAL GKR / relations / stacking B (chunk 1) | 37,592 / 24,772 / 6,736 (`zk = 2`) | same | 42,828 / 24,436 / 5,440 |

## 6. Simulator and hiding error

### 6.1 Simulator `S` (FINAL proof plus packet `u`), random-oracle model with programming

`S` receives the statement (public values, shape, vk, pinned program) and outputs a packet. It
samples every challenge itself and programs `H` at the corresponding transcript prefix, and
aborts if `H` was already queried there.

1. `u`: uniform (§3.4). `y = T_pub(u)` and the digest are computed. Root: a uniform 42-byte
   string.
2. GKR: `G_R` uniform; `s_R(1..4)` uniform (`s_R(0)` follows from the sum check); `P`, `Q`
   uniform; for every layer, `H_k` uniform, every sent round evaluation uniform, and the next
   level's four claims uniform.
3. Batch: `G_b` uniform; the uni-skip coefficients uniform subject to `Σ_D s_0 = claim`; every
   round evaluation uniform (the Gruen-derived one computed); the masked openings `t̂` uniform;
   the public program openings computed from the pinned program at `r`.
4. Stacking: `G_1, G_2` uniform; `s_0` uniform subject to its sum check; round evaluations
   uniform; every stacked opening `q_k(u)` uniform except `q_{M_1}(u)`, which is solved from the
   final check (coefficient `λ_1 eq_prism(τ_1, u) ≠ 0`).
5. WHIR: sample `g'` uniform with `g'(u) = Σ_j μ^j q_j(u)` and run the honest WHIR prover on it.
   For each query position, sample every column's symbols uniformly subject to
   `Σ_j μ^j sym_j = g'(α)`, program the Merkle path of that row to the root, and compute PoW
   witnesses.
6. All sparse-claim values `V` are whatever the final checks give. They are never sent.

### 6.2 Why the real view has the same distribution (per component, conditional on challenges)

* **Lemma A (Libra masked sumcheck, with the eq factor).** Let `F` be any summand of individual
  degree `≤ d_i`. Let the mask be `eq(ξ, y)·Σ_i h_i(y_i)`, with `h_i` uniform of degree `d_i`
  over `EF`, `ρ ≠ 0`, and every `eq1(ξ_i, x) ≠ 0` at the evaluation points. Then `H` and the
  round messages are uniform over the transcripts consistent with the verifier's sum checks,
  independently of `F`.
  *Proof.* Given the earlier messages, the non-constant coefficients of `h_i` enter only round
  `i`, as `ρ·A_i·eq1(ξ_i, X)·(h_i(X) − h_i(0))` with `A_i = Π_{j<i} eq1(ξ_j, r_j) ≠ 0`. That is
  a bijection onto the `d_i`-dimensional space of reduced round polynomials with a fixed sum.
  The constants of all the `h_i` together, plus `H`, account for the one remaining degree of
  freedom. This is CFS17 / Libra Thm 3; the eq factor is public. Exact (statistical distance 0)
  outside the events `ρ = 0` or `eq1 = 0`, each of probability `≤ 2/|EF|`.
  This covers GKR layers (`k ≥ 2`, layer 1 with two kernels, the root with no kernel), the batch
  sumcheck (`h_0` free in `X`; tail rounds keep the `eq1` factor), and the claimed sums `H`,
  `G`. The sumcheck's final value is not constrained by `F(r)`: it fixes `V`.
* **Lemma B (level masks).** The level-`k` claims are `p_k(b, ρ) + Z_k α^p_k(b)` and similar,
  with `α_k` uniform over `EF^4` and `Z_k ≠ 0`. `α_k` appears elsewhere only in `M_k`, inside
  the sparse claim `V_k`, whose value the transcript determines. So the claims are uniform.
  The root's `P`, `Q` work the same way with `β(1 − β) ≠ 0`.
* **Lemma C (column masks).** `t̂ = t + Z_t A` with `A` uniform over `EF` and `Z_t ≠ 0`. `A`
  appears elsewhere only in sparse weights. Exact.
* **Lemma S (span of an evaluation functional).** For `u` uniform, the `F`-span of the stacking
  weights of a block of `4·2·2` rows, `{1, u_0, u_0², u_0³} ⊗ {1, u_1} ⊗ {1, u_2}`, is all of
  `EF` except with probability `≤ 2·2^-155 + 2^-279`.
  *Proof.* `V_0 = span{1, u_0, u_0², u_0³}` has dimension 4 unless `u_0 ∈ F_{p^2} ∪ F_{p^3}`.
  `V_1 = V_0 + u_1 V_0` has dimension 8 unless `u_1 ∈ {v'/v : v, v' ∈ V_0}`, a set of at most
  `p^7` elements. `V_1 + u_2 V_1 = EF` unless `u_2 ∈ ∪_{a ∈ V_1^⊥ \ 0} a^{-1} V_1^⊥`, also at
  most `p^7` elements. So a single `EF`-valued evaluation functional of base-field cells is
  uniform over `EF`.
* **Lemma D (stacking Libra mask with base-field columns) — argued, not proved with a strong
  bound.** Per round, `M_j`'s fresh contribution is `σ_{j,i}·eq1(τ_{j,i}, X)(X − τ_{j,i})`,
  where `σ_{j,i}` is the slope of `M̂_j(u_{<i}, X, τ_{j,>i})`. As a functional of `M̂_j` it is
  linearly independent of every earlier one, all of which evaluate coordinate `i` at
  `τ_{j,i}`: take `M̂ = (x_i − τ_{j,i})·K` for any `K`. The two directions span the allowed
  space unless `τ_{1,i}` and `τ_{2,i}` coincide or are paired (`≤ 2/|EF|` per round). The open
  step: the `σ`s are `EF`-valued functionals of **base-field** cells. Lemma S gives each one
  uniform over `EF`. The *joint* `F`-rank of all of them, together with `q_{M_j}(u)`, `G_j` and
  the 92 opened symbols, is a generic-position statement for which only weak (base-field
  Schwartz–Zippel, about `2^-24`) bounds are proved.
  Fix: make the mask one `EF`-valued column `M̂ = Σ_b β_b P_b` built from 12 base columns. The
  independence is then over `EF`, and Schwartz–Zippel gives `deg/|EF|`. This costs columns, or
  couples with the WHIR pad.
* **Lemma E (per-column absorption) — open, inherited from §3.3.** For a trace column, the 92
  opened symbols alone are uniform, because a Vandermonde matrix on distinct points has full
  rank; `q_k(u)` alone is uniform by Lemma S. Jointly they are uniform iff
  `W_u ∩ span{v(α_i)} = 0`, where `W_u` is the 12-dimensional space of `F`-components of
  `q_k(u)`'s weights. `W_u` is fixed before the query points are sampled. A union bound over
  vectors of `W_u` of "exponential rank" `m` gives `≤ Σ_m N_m (92/|Dom|)^m`. This is
  `≤ 2^-118` for the terms with `m ≥ 20`. The terms `m < 20` need `W_u` to contain no short
  exponential sum, which is plausible but not proved.
  The clean fix is a protocol change: **batch WHIR with the stacking reduction's final
  coefficients plus a `μ`-power pad, and send no individual stacked opening.** Only symbols
  would then be revealed per column, and their absorption is exact. It also saves the 68
  stacked openings, about 3.3 KB. Not built: it changes WHIR's batching soundness term.

### 6.3 Concrete hiding error

| term | bound | status |
|---|---|---|
| RO programming (transcript prefix with the 336-bit root, `≤ 2^10` programmed points, `q = 2^64` queries) | `≤ 2^-262` | proven |
| Merkle leaf / root hiding (465 fresh bits per leaf) | `≤ q·2^-465` | proven |
| `μ`-basis of the WHIR pad | `≤ 2^-185` | proven |
| Libra / level / column / root masks (Lemmas A–C): `ρ = 0`, `eq1 = 0`, `Z = 0`, `β(1 − β) = 0`, `A_final = 0` | `≤ 2^10/|EF| ≈ 2^-360` | proven |
| Lemma S per functional | `≤ 2^-154` | proven |
| Lemma D (joint rank of the stacking mask functionals) | — | argued, open |
| Lemma E (joint rank of opened symbols and stacked openings per column) | `≤ 2^-118` + the short-exponential-sum term | open |

**ε_ZK ≤ 2^-185 + ε_D + ε_E**, statistical, in the ROM. `ε_D` and `ε_E` are the two open lemmas.
Until they are proved, or removed by the redesigns named above, the masked protocol is
"zero-knowledge under Lemmas D and E", and `zero_knowledge_established` stays `false`.

## 7. Measured (2026-11-03)

Three chunks, FINAL re-proved with `zk = 5` from each L4 checkpoint: packets 319,695 /
320,464 / 319,779 B. Fresh-process verify takes 40–50 ms on one core, at host load 13–19. The
FINAL check is 24–26 ms of that. 21/21 negatives pass per chunk, and the minimum is 268.2 bits
per round. See README §0 and `results/zk/zk5/`.

## 8. Tests

### 8.1 `zk-selftest` (toy AIRs, FINAL configuration: SHA-384, Ext12, FINAL levers)

Fibonacci (rotation, constraints) plus a LogUp sender/receiver pair with mixed heights. With
`log_send/send_live`, a zero tail makes tight chunks. The test proves and verifies, checks a
codec round trip, and tampers with every zk field, every GKR claim and round, batch rounds,
openings, stacking rounds and openings. Every tampered proof must be rejected. Results:
`results/zk/zk-selftest.txt`.

### 8.2 Hiding tests on FINAL proofs

* `zk-diff` of two full-ZK FINAL proofs of the same L4 (same witness, fresh randomness): every
  field except the shape, the public values and the public program openings must differ.
* **Witness-guessing distinguisher** (`NEARPROOF_ZK_GUESS`). For a FINAL proof and a candidate
  witness (the FINAL trace generated from an L4 checkpoint), it recomputes every column opening
  the proof reveals, i.e. the candidate trace's prismatic MLE and rotation at the `r` the
  verifier derives, and counts equalities.
* **Two-witness test.** The same distinguisher with the right and the wrong witness: the
  proof's own chunk versus another chunk's L4. Without PIOP masking the right witness matches
  every opening and the wrong one matches none, so the proof identifies its witness. With
  masking neither matches.

## 9. Obligations before `zero_knowledge_established = true`

1. Prove Lemma D and Lemma E, or remove them: an `EF`-valued stacking mask column, and WHIR
   batching with the stacking coefficients so that no individual stacked opening is sent
   (about −3.3 KB).
2. An independent review of the simulator (§6) and of the masked verifier code
   (`zk-piop.patch`).
3. No machine-checked ZK statement exists for any layer. Lemmas A–C and S are finite linear
   algebra and the cheapest to formalise first.
