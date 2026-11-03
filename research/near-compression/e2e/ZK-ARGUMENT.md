# Zero-knowledge argument for the chunk proof: status, construction, simulation, cost

Status (2026-11-03, lane E2E-D): **not zero-knowledge yet; `zero_knowledge_established=false`.**
The PCS layer of the FINAL proof and the published base point `u` are now hidden (§3, built and
measured: `NEARPROOF_ZK=1`). The PIOP layer of the FINAL proof (GKR, batch zerocheck, stacking
sumcheck, column openings) still leaks; its construction is specified in §4 with its size cost
estimated, not built. The 2026-10-31 version of this file (leakage inventory, HVZK-WHIR sweep) is in
git history; its §4 measurements stay valid and are reused in §6.

## 1. What must be hidden, level by level

Only the packet is published: `claim.bin` (statement), the hint (derived outputs, checked against
the claim), the base point `u`, and the FINAL proof. The setup is trusted and public.

| level | published? | must hide | why |
|---|---|---|---|
| base | only `u` (and `y = T_pub(u)`, computed by the verifier) | `u` must be simulatable | `u` is the RO output of the base transcript; without randomness in the base commitment it is a deterministic function of the witness (lets anyone test a guessed witness) |
| L1 … L_n | no | nothing | each is only the witness of the next level. The FINAL proof is ZK for *any* witness, so whatever the inner proofs contain is covered by the FINAL simulator |
| FINAL | yes | everything except its public values (level, statement digest) | its trace is the NV verifier run on L_n; leaking it leaks L_n, hence the chain |

Why ZK at an inner level would not do: a ZK simulator for an inner proof programs the random
oracle, but the next level recomputes that oracle (SHA-384) *inside its circuit*, which a
programmed oracle cannot satisfy. FINAL is the one proof whose transcript and Merkle hashes are
only ever evaluated natively (by the verifier), and it uses its own transcript domain
(`ShaTranscript::new_layer(true)`), so programming the oracle at FINAL's points is consistent with
every in-circuit SHA-384 evaluation of the inner levels. This is why ZK in the FINAL prover and
native verifier, plus the base randomisation for `u`, is enough; the recursion circuit is unchanged.

Shape: the FINAL trace heights (`tight_height` per AIR) are fixed by the converged program and the
child shape (`zk-diff` across chunks and across replays, §5); they are part of the per-shape setup.

## 2. Leakage inventory of the FINAL proof (after this change)

| field | content | hidden now? | by |
|---|---|---|---|
| `common_main_commit` | Merkle root of the stacked trace codeword | **yes** | random reserved rows + mask columns in every leaf (Z1, §3) |
| `whir_proof.*` (sumcheck rounds, fold commits, OOD values, opened codewords, final poly, PoW) | functions of the batched polynomial `g` and of the opened initial rows | **yes** | `g` is a one-time pad (§3.2); opened rows by reserved-row randomness (§3.3) |
| `stacking_proof.stacking_openings` | stacked columns at `u_F` | **yes** (given §4) | reserved rows |
| `stacking_proof` round messages | stacking sumcheck | no | §4 Z3 |
| `batch_constraint_proof.*` | uni-skip + zerocheck rounds, per-AIR logup terms, **column openings at r** | no | §4 Z2, Z3 |
| `gkr_proof.*` | layer claims and round messages | no | §4 Z3-GKR |
| `trace_vdata`, public values | shape, level, digest | public | – |
| packet `u` | base stacking point | **yes** | base `zk = 1` (Z6) |

## 3. Built: PCS-level hiding (`WhirLevers::zk`, `patches/zk-pcs.patch`)

### 3.1 Construction

* `zk = 1` (base): the common-main stacked layout keeps the last `R = 256` rows of every stacked
  column free (first-fit-decreasing packing of the power-of-two slices into `2^h − R` rows) and
  the prover fills them with fresh uniform field elements (rejection sampling of `/dev/urandom`).
  No trace slice lies there, so no PIOP claim (zerocheck, stacking weights) gives them weight:
  soundness is unchanged (they are simply unconstrained committed cells).
* `zk = 2` (FINAL): as `zk = 1`, plus `M = 12` appended stacked columns of uniform elements.
* Both sides compute the layout from the vk (`StackedLayout::new_tight_zk`, called by the prover
  and by `verify_proof_shape`); the lever is in the vk (`params.whir.levers.zk`, serialized only
  when non-zero, so every existing key's pre-hash is unchanged) and in the proof's lever header
  (bits 1–2 of the keep_domain byte; upstream bytes unchanged at `zk = 0`). Cached commitments
  (the base TAPE) are never randomised: the verifier evaluates the public TAPE at `u`.

### 3.2 Why WHIR is hidden: `g` is a one-time pad

WHIR batches the stacked columns of the FINAL commitment as `g = Σ_j μ^j c_j` (μ ∈ EF from the
transcript, after the root). With `M = 12` uniform base-field columns `h_0..h_11` among them,
`Σ_i μ^{w+i} h_i` is uniform in `EF^{2^h}` whenever `1, μ, …, μ^11` are linearly independent over
`F` (μ outside every proper subfield of `F_{p^12}`: failure ≤ p^6/p^12 = 2^-185). So `g` is
uniform conditioned on everything else, except for the linear functionals of `g` the view fixes
(the claimed `g(u)` from the stacking openings, and `g` on the opened positions). Every WHIR
message after batching — round polynomials, fold oracles and their roots, OOD answers, opened fold
values, final polynomial, PoW witnesses — is a deterministic function of `g` and the verifier's
challenges. Simulator: sample `g'` uniform subject to those linear constraints (linear algebra on
≈ 100 constraints) and run the honest WHIR prover on `g'`. This is the classical "batch with a
random codeword" ZK of linear-code PCSs (Ligero, Ames–Hazay–Ishai–Venkitasubramaniam CCS'17 §5;
Aurora, Ben-Sasson et al. EUROCRYPT'19, ZK low-degree test via a random masking polynomial;
Plonky3's `HidingFriPcs`). Unlike HVZK-WHIR (eprint 2026/391) it needs no mask oracles and no
extra queries: its cost is `M` columns in the initial opened rows.

### 3.3 Why the opened initial rows and the root are hidden

Each query reveals, for every stacked column, the codeword symbols at its coset (`2^{k_first} = 2`
points), and the PIOP reveals one opening per column at `u_F`: 46·2 + 1 = 93 linear functionals
per column. The `R = 256` reserved cells occupy the top block of the column's hypercube (high
bits all 1); under the eval→coefficient transform they map bijectively onto the coefficients of
that block, whose contribution to a codeword symbol at `α` is `α^{2^h−R} · Σ_{s<R} c_s α^s`
(Vandermonde rows for distinct `α`) and to the opening at `u_F` a multilinear evaluation. For
distinct query points these 93 functionals restricted to the 256 random coordinates are linearly
independent except with probability ≤ 93·256/|EF| (generic position of `u_F`), so the revealed
values of every column are uniform and independent of the trace. The `M` mask columns are uniform
outright. Every Merkle leaf (a codeword row) therefore carries ≥ 12·31 = 372 bits of fresh entropy
(the mask columns' symbols), which makes unopened leaves and the root hiding in the ROM without a
separate salt: the mask columns double as leaf salts (Z1 at zero extra bytes).

### 3.4 Base point `u` (Z6)

With `zk = 1` the base root is a RO hash of leaves carrying fresh randomness, so `u` (squeezed
after the root) is uniform and independent of the witness except with probability
`q · 2^{-min(336, 31·R·w)}` (q oracle queries; `w` = base stacked width). The simulator samples `u`
uniformly and computes `y = T_pub(u)` and the statement digest itself.

### 3.5 Error terms (statistical, ROM)

`ε_PCS ≤ 2^-185 (μ basis) + 93·256/2^370 (rank) + q·2^-336 (root/leaf hiding)`; `ε_u ≤ q·2^-336`.
With q = 2^64: ≤ 2^-185 overall. Soundness: unchanged — no new challenge, no new round, no new
claim; the reserved and mask cells are unconstrained committed data, which WHIR already batches.
The per-component bits from `soundness` on the ZK setups are in §6.

## 4. Specified, not built: PIOP-level hiding of the FINAL proof

| # | leak | construction | reference | size cost (estimate) |
|---|---|---|---|---|
| Z2 | column openings at `r` (and rotations) | mask each FINAL trace column off the domain: `f̂_j = f_j + Z_D(X)(a_j + b_j X)` in the univariate-skip variable (`Z_D = X^4 − 1` vanishes on the skip subgroup, so every hypercube value and every constraint is unchanged); two coefficients per column hide the opening and the rotated opening. The coefficients live in reserved rows; the stacking reduction gives those cells the weight `Z_D(r_0)·(1, r_0)` times the column's batching coefficient, so `f_j(r)` itself is never sent | low-degree masking, Chiesa–Forbes–Spooner 2017; Libra (Xie et al., CRYPTO'19) §4 | uni-skip round degree 27 → 45 at constraint degree 9: ≈ +1 KB |
| Z3 | sumcheck round messages (batch zerocheck, stacking) | Libra masked sumcheck: `g = Σ_i g_i(X_i)` of the round degree, coefficients in reserved rows, prover sends `G = Σ_H g`, verifier ρ, sumcheck on `F + ρ g`; `g(r)` is a linear functional of reserved cells, opened through the stacking reduction | CFS17 Thm; Libra Thm 3 | +1 EF per sumcheck |
| Z3-GKR | GKR layer claims `p, q` at `ξ_i` and layer round messages | Libra's zero-knowledge GKR: mask each layer's `p_i, q_i` with `Z(x_1)·R_i` (small random `R_i`), masked layer sumchecks; the extra cross terms raise the degree of the rounds in the masked variables only | Libra §4.2 (multiplication-gate layers; the fractional layer relation is the same bilinear form) | ≈ 22 layers × (1 mask sum + ≈ 3 extra coefficients) ≈ 4–8 KB |
| – | per-AIR logup input terms | covered by Z2 (they are functions of the masked openings) | – | 0 |

Total (A) ≈ 6–12 KB (estimate). Each adds a prover step in the FINAL layer only and changes the
FINAL verifier's checks; none touches the NV circuit (it never verifies FINAL). Soundness: the
masked rounds' degree increase costs ≤ 2 bits per affected sumcheck (all ≥ 350 bits today); must be
recomputed in `SoundnessCalculator`.

## 5. Hiding sanity test (`nearproof-chunk-e2e zk-diff A B`)

Field-level test, necessary not sufficient: two FINAL proofs of the same statement from the same
witness (same `L_n` checkpoint, fresh prover randomness) are compared leaf by leaf; a field equal in
both is a deterministic function of (witness, statement). Results: §6 and `results/zk-diff-*.txt`.

## 6. Measured (2026-11-03)

* **Three chunks end to end with `NEARPROOF_ZK=1`** (base `zk = 1`, FINAL `zk = 2`): packets
  325,613 / 324,534 / 326,243 B vs 306,839 / 307,314 / 307,427 B non-ZK (+17.2 to +18.8 KB);
  23/23 negatives each; fresh-process verify 129–283 ms on one core under host load 20–22, of
  which the FINAL protocol check is 20–48 ms (README §0).
* **Where the bytes go** (FINAL, chunk 1): stacked width 53 → 95 columns = 12 mask columns + 30
  columns of packing loss (first-fit with `R` reserved rows cannot place two `2^20` slices in one
  `2^21` column). Each column costs 4 B × 92 opened rows + one 48 B stacked opening:
  mask columns ≈ 5.0 KB, packing loss ≈ 12.5 KB, plus Merkle-digest variation. GKR, relations
  and the WHIR fold rounds are byte-identical in size to the non-ZK proof.
* **Packing lever (`zk = 3`, halve a slice when no column fits it)**: built, but the FINAL proof
  fails the prover's own stacking-reduction final-sum check (re-sorting the placed slices by size
  did not help); suspected: a code path that assumes at most the binary-decomposition chunks of a
  tight column. Would bring the PCS-ZK overhead to ≈ +5 KB (≈ 312 KB packets).
* **Versus HVZK-WHIR** (10-31 sweep, 128-bit Johnson, rate 1/64): +222 to +312 KB for the PCS alone.
  Random-codeword batching costs 12–17× less here because it adds no oracle and no query.
* **Per-round bits**: unchanged by the lever, min 268.2 (FINAL WHIR query); at a 274-bit FINAL
  target the packet is 329,505 B (+3.9 KB, queries [47, 43, 31, 25]).
* **Hiding checks**: `results/zk/zk-diff-replay-same-witness.txt` (two FINAL proofs, same L4):
  root, all WHIR fields and stacked openings fresh; trace heights identical (no data-dependent
  shape within a witness); PIOP fields change only through their challenges and stay
  witness-determined (§4 open). `results/zk/zk-diff-base-same-witness.txt`: two `zk = 1` base
  proofs of one witness have different roots, hence different `u`.
* **Full-ZK projection**: 325 KB measured + 6–12 KB PIOP masking (estimate) ≈ 331–338 KB, or
  ≈ 318–325 KB once the packing lever works: within the ~400 KB budget at 268 bits, and at 274 bits.

## 7. Obligations to set `zero_knowledge_established = true`

1. Z2, Z3, Z3-GKR (§4) in the FINAL prover and native verifier.
2. The simulator of §3.2–3.4 composed with the PIOP simulators of §4 into one simulator for the
   FINAL proof plus `u`, with the concrete error bound at the FINAL parameters (§3.5 gives the PCS
   and `u` terms).
3. Soundness re-derived for the masked PIOP (§4 last paragraph).
4. `zk-diff` on two FINAL proofs from the same witness reports no deterministic field other than the
   public values and the shape; plus a simulated transcript that the verifier accepts under a
   programmed oracle (shape test).
5. No machine-checked ZK statement exists for any layer (the zk-formal pattern models the relation,
   not the proof system); the finite linear-algebra lemmas of §3.2–3.3 are the cheapest to
   formalise first.
