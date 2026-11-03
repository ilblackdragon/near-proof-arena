# The e2e verifier patch: review and soundness argument (2026-11-03)

Patch: `research/near-compression/native/recursion/patches/e2e-verify.patch` (moved there from
`e2e/patches/` on 2026-11-03), applied by `native/recursion/setup_e2e_verify_deps.sh` on top of
the cpu-fast stack. `native/pq-chunk-e2e/setup.sh` and `e2e/scripts/setup_e2e.sh` both go through
that script, so the driver builds from a clean checkout (before, `pq-chunk-e2e/setup.sh` stopped at
the cpu-fast tree and the driver, which calls `take_last_stacking_point`, did not compile).
Regenerate with `native/recursion/make_e2e_verify_patch.sh` (`E2E_REFRESH=1`).

It changes two things. Each is reviewed below; the review found one hardening item, fixed in the
moved patch (§2.3).

## 1. TAPE binding by random evaluation (`NEARPROOF_TAPE_EVAL=1`, packet/setup version 2)

### 1.1 What changed

Before: the statement digest exposed by every NV level was
`d = node(G1(pvs), R_T)`, with `R_T` the Merkle root of the base proof's cached TAPE commitment,
and the verifier recomputed `R_T` from the public TAPE (a rate-1/1920 codeword of 126 M points,
8–15 s on one core).

After: L1's in-circuit verifier of the base proof (`nv/verifier.rs`, the `deferred_statement`
branch) exposes `d = node(G1(pvs), H_tape(u, y))`, where

* `u = (u_0, u_1, …, u_{n_stack})` is the base proof's stacking point `u_prism`, squeezed from the
  base transcript in the stacked reduction;
* `y` is the vector of stacked openings, at `u`, of the TAPE commitment's stacked columns,
  read from `stack_open` — the same values the WHIR check that follows in the same circuit
  verifies against `R_T` (the root is located among the WHIR roots by cell address);
* `H_tape` is SHA-384 (tag `TAG_STATEMENT`) over `["TAPE" marker, |u|, |y|, coeffs(u), coeffs(y)]`.

The packet (`NPQCH02`) carries `u`; the verifier computes `y_pub = T_pub(u)` from the public TAPE
(`stacked_openings_at`, ≈ 43 k non-zero cells, 2^16 eq weights) and requires the final proof's
digest to equal `node(G1(pvs_pub), H_tape(u, y_pub))`. The setup's `version` (pinned by the
operator's hash) selects the format; a packet cannot choose it.

### 1.2 Claim

Let `T*` be the TAPE the base proof's own soundness is relative to (the polynomial its zerocheck
and stacking openings of the cached columns refer to). If the verifier accepts, then
`T* = T_pub`, except with probability at most

    ε_tape ≤ Q · L · D / |EF|      (classical, Q random-oracle queries)

with `D = (2^l_skip − 1) + n_stack = 3 + 18 = 21` (the stacked polynomial as a function of
`u_prism` has degree ≤ 3 in `u_0` — univariate skip over a 4-element subgroup — and is
multilinear in `u_1..u_18`), `|EF| = p^12 ≈ 2^370.9` (BabyBear, degree-12 extension), and
`L` the list size of the base commitment's proximity regime. Numbers:

| | per attempt | Q = 2^64 classical | Q = 2^64 quantum (O(Q²ε), CMS19) |
|---|---:|---:|---:|
| unique-decoding view, L = 1 | 2^-366.5 | **2^-302.5** (the "2^-303" quoted on 2026-10-31) | 2^-238.5 |
| Johnson list decoding of the base (ρ = 2^-7, m = 64 ⇒ L ≤ m/ρ = 2^13) | 2^-353.5 | 2^-289.5 | 2^-225.5 |

The second row is the bound to quote: the base runs WHIR in the list-decoding regime, so the
root fixes a word with up to `L` nearby codewords rather than one polynomial. Either way the term is
far below the 268-bit per-round target of every other component, so it does not move the
128-bit PQ claim.

### 1.3 Argument

1. *Fixing.* `R_T` is observed in the base preamble (cached commitments, before any challenge).
   In the ROM, Merkle binding (U-10, `t^3/2^336`) fixes the committed word `w_T`, hence the list
   `List(w_T) = {P_1..P_L}` of codewords within the proximity radius, before `u` is sampled. The
   prover may vary `R_T` (and anything else) between attempts; each attempt is a fresh RO query
   for the transcript prefix, which is what `Q` counts.
2. *WHIR.* The L1 circuit verifies the base WHIR proof on the batched claim that includes `y`
   at `u_cube = (u_0, u_0^2, …, u_0^{2^{l_skip−1}}, u_1, …)`. WHIR's soundness (269.6 RBR bits for
   the base, `results/soundness-*.txt`) gives: on acceptance some `P_i ∈ List(w_T)` has
   `P_i(u) = y`, and that `P_i` is the polynomial the base proof's PIOP openings refer to (the
   zerocheck and stacked reduction land on the same `u` and the same `y`), i.e. `T* = P_i`.
   In-circuit SHA-384 is the A-IC assumption (U-11/U-12), as for every other in-circuit check.
3. *Evaluation.* The verifier accepts only if `H_tape(u, y) = H_tape(u, y_pub)`, i.e. (barring a
   SHA-384 collision, already in the hash budget) `y = T_pub(u)`. So `P_i(u) = T_pub(u)` for the
   `u` the RO produced after `List(w_T)` was fixed. For each `P_i ≠ T_pub` the difference is a
   non-zero polynomial of total degree ≤ `D` in `u`, and `u` is uniform in `EF^{n_stack+1}`, so
   Schwartz–Zippel gives `Pr[P_i(u) = T_pub(u)] ≤ D/|EF|`; a union bound over `L` list elements and
   `Q` attempts gives §1.2.
4. *Format separation.* v1 and v2 digests are `node(G1, R)` and `node(G1, H_tape)`; `R` is a Merkle
   root (Merkle tag) and `H_tape` a statement hash under a different tag with a leading marker
   cell, so equal digests across formats imply a SHA-384 collision. The format is pinned by the
   setup's version.
5. *What the root no longer does.* `R_T` leaves the statement, but it still enters the base
   transcript, which determines `u`; that is where its binding now acts (step 1).

### 1.4 Review notes

* `u` is the full `u_prism` (length `n_stack + 1`; the packet decoder checks the length against
  the setup's `base_params.n_stack`), not `u_cube`; `stacked_openings_at` evaluates the
  prismalinear form at the same `u`, matching the prover's stacked openings (`chain` asserts
  `TAPE_EVAL_OK` against the base proof's own openings on every run).
* The openings are taken from the flat `stack_open` list by the root's commit index and the
  per-commit widths, the same slicing WHIR uses; a cached root that is not among the WHIR roots
  panics at program generation (no proof is produced), it cannot be skipped.
* Zero-knowledge: `u` is a deterministic function of the base transcript, so it fingerprints the
  base witness unless the base commitment is randomised; see `ZK-ARGUMENT.md` Z6.

## 2. Program check at the reused batch point

### 2.1 What changed

`vd::verify_final_claim` used to replay the final proof's transcript and re-run
`verify_zerocheck_and_logup` to recover the batch point `r`, then check the pinned program's MLE
against the NvAir's program-column openings at `r`. Now `stark_backend::verifier::verify` records
`r` in a thread-local (`LAST_ZEROCHECK_POINT`) right after deriving it, and `verify_final_claim`
(i) clears the slot, (ii) runs `engine.verify` on the proof, (iii) takes the slot, and (iv) passes
it to `check_final_program_at`. The program MLE is also evaluated over the program's `2^m`
prefix with the high hypercube variables factored out as `∏_{i>m}(1 − r_i)`.

### 2.2 Equivalence

* `r` is set on the success path of the same `verify` call on the same proof (cleared before the
  call; any failure returns early), so it is exactly the point the replay derived: both run the
  same transcript operations on the same proof bytes under the same vk.
* The fast path picks the openings the replay picks: the NvAir is AIR 0; its position `ti` among
  the present traces is computed with the verifier's ordering (descending log height, then AIR
  index).
* Prefix evaluation: the eq table is built with each new variable as the highest bit, as in the
  original, so for `x < 2^m` the bits above `m` are zero and `eq(r_{1..n}, x) =
  eq(r_{1..m}, x) · ∏_{i=m+1..n}(1 − r_i)`; points `x ≥ ⌈len/2^l_skip⌉` carry no words. The per-row
  weights `lv[i]·τ^j` are only regrouped. `m ≤ n` is enforced, and the length check
  `len ≤ 2^{l_skip+n}` runs before the evaluation.

### 2.3 Hardening (applied in the moved patch)

The replay path rejected proofs with an absent AIR and the fast path did not. With the final vk
all NV AIRs are required, so `engine.verify` already rejects such a proof (proof shape), but the
two paths are now identical by construction: the fast path also requires every AIR present and
rejects a recorded point shorter than `1 + n`.

## 3. The delivered-packet (v1) path

Kept working, not removed: a setup with `version = 1` and an `NPQCH01` packet verify through the
root-recomputing path (`expected_claim`, the same binary: 8.8–9.6 s single core, 2.4 s at 16
threads on `opt-baseline-8`). It is **deprecated for new setups**: it is two orders of magnitude
over the 200 ms target, and its root recomputation is the step the v2 statement removes. New
chains are produced with `NEARPROOF_TAPE_EVAL=1` (the driver's default).
