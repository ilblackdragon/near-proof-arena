# R2 (native accumulation): the ROM theorem and its proof plan

Status: research note, 2026-10-06, lane `lane/v3-d3`. Input to checkpoint 2 (the R1/R2/R5 decision memo) of
`docs/requirements/RECURSION_REQUIREMENTS.md`. Read-only with respect to `zk-formal/`, `formal-core/` and
`docs/zk-formal/`. Citations are `file:line` in this worktree. Unless a path says otherwise, Lean paths are
relative to `zk-formal/ZkFormal/`.

## 0. Summary

* **The admission theorem does not change.** R2 inhabits the existing random-oracle branch of `CryptoSound`
  (`formal-core/ArenaCore/Admission.lean:112-118`). The deployed verifier runs every accumulation step natively.
  All of its hashing is a protocol oracle call, and no hash function is arithmetised.
* **The scheme.** We fix the simplest sound candidate in the unique-decoding regime, "UDR-Arc" (§1.2). Each
  step does three things:
  * It takes a multilinear line-batch of the previous accumulator's degree-corrected quotient and the
    segment's DEEP columns.
  * The prover commits the new accumulator word.
  * A 24-chunk group of spot-check positions is sampled. These positions become **evaluation claims** on the
    new accumulator. They are not compared against it.

  The decider is one degree-correction batch followed by the existing FRI. **There is no OOD sample in the
  accumulator**, because unique decoding makes it unnecessary. There are also no curves, no list decoding, and no
  correlated agreement beyond the line gap that is already proved.
* **Claims are essential.** A design without claims (check `a_i(x) = h_i(x)` directly) is not sound at any
  useful parameter, because the radius degrades by the spot-check slack at every step (§2.6).
* **New algebra.** Soundness needs four small deterministic lemmas, which make up the PoC (§3):
  * quotient-with-fill;
  * degree correction by shifts;
  * spot-check doom;
  * spot-check escape.

  All other IOP math is already proved in L3: `strong_line_rs`, `batch_chain`, `fri_query_bound` and `rsGap`.
* **No union bound over S.** The L2 potential argument charges each oracle query at most the maximum
  per-query error, so the bound does **not** grow with S. S enters only through the honest query counts. The
  query-phase term is ≤ 2^-131.1 for every accumulation domain `n ≥ 2^16` and `S ≤ 4096` (§1.5).
* **Two L2 changes are missing.**
  * **Intermediate query groups (Q1).** The BCS layer must support query chunks whose positions fix later
    rounds.
  * **Challenge-weighted `badPot` (Q4).** Today every oracle query pays `B/2^256`. At S = 1000 the honest
    prover's roughly 2^40 Merkle queries push the commit-phase term to 2^-126, so it must be charged only to
    challenge queries (about 2^-142 after the change).

  Everything else in L2 is reused unchanged: `romSound_of_potential`, `bad_query_bound`, `query_phase_bound`,
  `collision_bound`, `invPot`, MMCS binding and multiproofs.
* **Size estimate.** About **11–19k new LOC** on top of R1's multi-segment front end, which R2 needs as well
  (§2.7).
* **Cost caveat for the decision memo (§5).** With a native verifier, R2's proof is analytically **at least
  R1's**:
  * every segment is still opened at about 216 positions;
  * R2 adds accumulator openings plus one Merkle path per tree per step;
  * the global bus challenges force the same commit-all-then-challenge prover schedule as R1.

  This is an analytical expectation, not a measurement.

---

## 1. The theorem

### 1.1 Notation and parameters

* `F = Fp` (BabyBear) and `K = Fp8` (`Algebra/Fp8.lean:103`). `Kall = Fp8.all`.
* Decoder fibres: `Dm = 2·3^8` (`hdec_deployed`, `Bcs/TransFinal.lean:60`).
* Every segment is proved over one LDE domain `L = {xs 0, …, xs (n−1)}` with `n = 2^logN`, `16 ≤ logN ≤ 26`,
  rate 1/16 and degree bound `D = n/16`. `Distinct xs n` holds (`Udr/RS.lean:23`).
* Radius: `e = (n − D)/2 − 1`, the L3 radius behind `agreeUdr` (`Udr/Rbr.lean:88`). Spot positions per step:
  `t = 24·9 = 216`. Working radius: `e' = e − t`.
  * The side conditions are `2e' + D ≤ n` (BW/strong line), `e' + D + t ≤ n` (shift lemma),
    `2e < n − D + 1` (uniqueness) and `t ≤ D` (needs `n ≥ 3456`). All hold for `logN ≥ 12`.
* Codes:
  * `C = rsCode xs n D` (`Udr/RS.lean:55`), with distance `n − D + 1`.
  * `C^J = rsInterleaved xs n D J` (`Udr/RS.lean:72`).
* Accumulator relation, at radius `r`:
  ```
  RAcc_r(a, Z) :⇔ ∃ p : Nat → K, dist n a (ev D p ∘ xs) ≤ r ∧ ∀ (x, y) ∈ Z, ev D p (xs x) = y
  ```
  `dist` is `Udr/Code.lean:42` and `ev` is `Udr/Poly.lean:27`. Here `a` is a committed word on `L` and
  `Z = [(x_k, y_k)]` are claims at **in-domain** positions `x_k < n`.

### 1.2 The accumulation IOP ("UDR-Arc")

**Front end.** These are R1's stages, unchanged in kind. Their output is a segment word `G_j` for each `j`.

* The prover commits all S segment main traces.
* Then come the global bus challenges (`α_fp`, `γ`), the aux commits, `α_c`, the quotient commits, and an OOD
  point `z_j ∈ K∖F` with values for each segment, as in `DESIGN.md` §4 rounds 1–4.
* Segment `j` then defines its DEEP interleaved word `G_j : Word Nat K`, the columns `(f_c − v_c)/(x − ζ)`
  (`deepW`, `Udr/Deep.lean:36`).
* **The bus challenges are common to all segments**, because the RAM, call-stack, gas and host buses cross
  segment boundaries. All S main commitments therefore precede them, exactly as in R1.

**Accumulator state.**
* `acc_i = (a_i, Z_i, φ_i)`: the committed word `a_i : L → K`, the claim list `Z_i` (`t' ≤ t` distinct
  positions after deduplication), and the prover-sent fills `φ_i` (one `K` element per claimed position).
* `acc_0 = (0, [], [])`, which satisfies `RAcc`.

**Derived words.** These are computable at any position from openings.
* `Q_i(x) = (a_i(x) − Ans_{Z_i}(x)) / V_{Z_i}(x)` for `x ∉ T_i`, and `Q_i(x) = φ_i(x)` for `x ∈ T_i`.
  * `T_i` is the set of claimed positions.
  * `Ans` is the interpolant of the claims, of length `t'`. It is defined for every `H` because the points are
    distinct domain points.
  * `V_Z = ∏_{x_k}(X − xs x_k)`; this is `gpP`, `Udr/GrandProduct.lean:54`.
* `W_i(x) = ( x^0·Q_{i−1}(x), …, x^{t'}·Q_{i−1}(x) ) ++ G_i(x)`, zero-padded to `2^b` columns.
* `h_i = batchAll (r_{i,1..b}) W_i` (`Udr/Deep.lean:141`).

**Step `i = 1..S`.**

| # | Slot | Content |
|---|---|---|
| 1 | `chal` × b | Batching challenges `r_{i,1..b} ∈ K` (multilinear line rounds). `b = ⌈log₂(t + 1 + m_seg)⌉`, about 13 at `m_seg ≈ 6000` DEEP columns. |
| 2 | `msg [oracle]` | Commitment to `a_i` (honestly `a_i := h_i`, an exact `RS[D]` codeword). |
| 3 | **`group`** (new) | 24 chunk answers `H(QUERY ‖ d ‖ j)` give 216 positions `X_i`. The next state is `d' = WH(GRP, d ‖ y_0 ‖ … ‖ y_23)`, so later rounds depend on the answers (see Q1). |
| — | verifier, at `X_i` | Opens `a_{i−1}` and segment `i`'s trees at `X_i` (MMCS multiproofs) and computes `y_k := h_i(x_k)`. Then `Z_i := dedup [(x_k, y_k)]`. **Nothing is accepted or rejected here** apart from Merkle and shape checks: a false claim is caught by the decider. |
| 4 | `msg [elems]` | Fills `φ_i ∈ K^{t'}`, the values of `Q_i` at `T_i` (honestly the true quotient-polynomial values). |

**Decider.** The words `x^c·Q_S(x)` for `c ≤ t'` are line-batched (`b' = ⌈log₂(t+1)⌉` challenges) into one
word. Then the **np-udr-stark FRI** runs on that word as-is: binary folds, arity-8 commits, final degree < 2,
and a final 24-chunk query phase at radius `e'`. At each final position the verifier opens `a_S` to compute
`Q_S`.

**Completeness for every `H` (no grinding).**
* Every challenge is used as it comes. Repeated positions are deduplicated deterministically.
* The two divisions are total: `V_Z(x) ≠ 0` off `T` (distinct points), and DEEP uses `x − z ≠ 0` (`z ∉ F`).
* Fills make the honest `h_i` an exact codeword: `a_i = h_i = p_i`, so `p_i(x_k) = y_k`.
* FRI on a codeword passes for all `β`.
* Proof shape and size depend only on the header (`S ≤ S_max`, heights).

### 1.3 The BCS-compiled verifier

The transcript encoding is that of `Bcs/Extract.lean:1-40`: `d₀ = WH(INIT, …)`, absorb
`d ← WH(ABS, d ‖ u8|ρ| ‖ ρ ‖ μ)`, and challenge `d ← WH(CHAL, d)` with the challenge equal to the first half.
R2 adds one entry kind:

```
group:  y_j = H(QUERY ‖ d ‖ le4 j)   (j < 24, = chunkQ d j, Bcs/Wide.lean:200)
        d  ← WH(GRP, d ‖ y_0 ‖ … ‖ y_23)        -- answers feed the state (see §4 Q1)
```

* **Proof format.** The header carries `S`, `logN` and the segment heights. Then come, per step, the
  accumulator root, the fills and the step-`i` multiproofs, followed by the decider. It is fixed-shape and
  little-endian, and the verifier rejects any oversize input, any `S > S_max` and any trailing bytes (as in
  `DESIGN.md` §4).
* **Verifier.** `accVerifier : TreeVerifier` (`Game.lean:56`) is
  `⟨fun pub cb pb => Bcs.compileQ (accIop A prm) pub cb pb⟩`, mirroring `starkTree` (`Bcs/Final.lean:28`) and
  `Stark.Bcs.compile` (`Stark/Bcs.lean:557`).
* **Query bound.** `NVu` is bounded from the header caps, with per-step multiproof counts given by
  `multiproof_qbp` (`Stark/QueryBound.lean:224`):
  * per step: about 216 positions × 4 trees (`a_{i−1}`, plus segment main, aux and quotient) × ≤ 26 levels × 2
    queries per `WH`, i.e. ≤ 2^15.5;
  * plus `2b` per chal and 24 per group;
  * at `S_max = 4096` this gives `NVu ≤ 2^28`, below the `2^30` that `stark_romSound_full`
    (`Assembly/RomFull.lean:30`) and the budget lemmas use.
* **Prover.** The honest prover hashes `O(S·n)` Merkle nodes, so `NPu ≈ 2^40` at `n = 2^26`, `S = 1000`. This
  exceeds the `NPu ≤ 2^32` of `budget32` (`Assembly/Budget32.lean:31`), so a re-instantiation is needed
  (request Q4). The numbers still fit, because `qH + qP·NPu + NVu ≈ 2^80 ≤ 2^100 = hN`.

### 1.4 Lean statements (the targets)

The names `Acc.*`, `IopSpecQ`, `RbrWithQ` and `compileQ` are new. Every other name is the actual one.

```lean
namespace ZkFormal.Acc
open ArenaCore ArenaCore.Security ZkFormal ZkFormal.Stark ZkFormal.Algebra

structure AccParams where
  logN : Nat                 -- accumulation domain 2^logN, 16 ≤ logN ≤ 26
  logBlowup : Nat := 4       -- D = 2^(logN - logBlowup)
  numChunks : Nat := 24      -- per query group and for the final query phase
  posPerChunk : Nat := 9
  posBits : Nat := 26
  Smax : Nat                 -- 1000 ≤ Smax ≤ 4096
  maxProofBytes : Nat

/-- Spot-check agreement bound on a domain of size n (radius e' = e − t). -/
def agreeAcc (prm : AccParams) (n : Nat) : Nat :=
  n - ((n - n / 2 ^ prm.logBlowup) / 2 - 1 - prm.numChunks * prm.posPerChunk) - 1

-- the IOP (front end of R1 + S accumulation steps + decider), with query groups
def accIop (A : SegAir) (prm : AccParams) : Stark.IopSpecQ Fp Fp8
def accVerifier (A : SegAir) (prm : AccParams) : TreeVerifier :=
  ⟨fun pub cb pb => Bcs.compileQ (F := Fp) (accIop A prm) pub cb pb⟩
def accProver (S : ChallengeSpec) (A : SegAir) (prm : AccParams) (traceOf : …) : TreeProver S

/-- (a)+(d) IOP level: round-by-round facts incl. query groups. -/
theorem accRbr (A : SegAir) (prm : AccParams) (hok : AccOk A prm) :
    Udr.RbrWithQ (accIop A prm) (SegLang A) Fp8.all (2 ^ 36) (agreeAcc prm) (AccDoomed A prm)

/-- (c) ROM soundness of the deployed verifier, at the profile budgets. -/
theorem acc_romSound_full (A : SegAir) (prm : AccParams) (hok : AccOk A prm)
    (hq : QueryOk' prm.numChunks ((prm.Smax + 1) * prm.numChunks) g16)   -- kernel `decide`
    (hNV : NVu' A prm ≤ 2 ^ 30)
    {S : ChallengeSpec} (P : TreeProver S) (pub : Bytes) (NPu : Nat) (hNP : NPu ≤ 2 ^ 44)
    (hPu : ∀ c w, OracleComp.QueryBound unitWeight (P.tree pub c w) NPu)
    (hPq : ∀ c w, OracleComp.QueryBound (qWeight Bcs.chunkDec) (P.tree pub c w)
                    ((prm.Smax + 1) * prm.numChunks)) :
    ∃ tapeLen num den : Nat, num * 2 ^ 128 ≤ den ∧
      RomSound S (SegLang A) (accVerifier A prm).toVerifier P.toProver pub
        (2 ^ 64) (2 ^ 40) tapeLen num den
```

The witnesses are explicit, read off `bcs_romSound` (`Bcs/Compose.lean:79`) and `bcsNum`
(`Bcs/Statements.lean:61`):

```
tapeLen = 2^64 + 2^40·NPu + NVu
num     = bcsNum 24 (2^36·Dm) (g^24) (2^64) (2^40) NPu NVu NPq NVq,  NPq = NVq = (S_max+1)·24
den     = roRange ^ 24
g       = chunkGood (agreeAcc prm) logN   (Assembly/Params.lean:43), dominated for logN ∈ [16,26]
B       = 2^36 = max(front-end badBudget (Udr/Np/Statements.lean:34), 3n + 2e' + 1 < 2^28)
```

(At `S = 1000` this `B` is too large under today's unit-weighted `badPot`. §1.5 and Q4 give the fix: charge
`RoundBad` only to challenge queries.)

`acc_admission` follows exactly the pattern of `np_admission` (`Assembly/Admission.lean:45`). It chooses
`P := accProver …` and then supplies three pieces:
* `ProverComplete ch.spec V P pub ch.maxProofBytes` (`formal-core/ArenaCore/Verifier.lean:94`);
* `VerifierComplete`, by instantiating `H := sha256 ∘ (roTag ++ ·)`;
* the `RomSound` above, at `num·2^targetBits ≤ den`.

Together these discharge `CryptoSound`'s `.randomOracle` arm (`Admission.lean:112-118`). The semantic link
`SegLang A cb → ch.spec.InLang cb` is §3.1/§3.4 of the requirements (segmentation), outside R2.

### 1.5 Numbers (Python check; to be re-done by kernel `decide`)

The query-phase term is `log₂((2^64 + 2^40·24·(S_max+1) + 24·(S_max+1)) · (agreeAcc(n)/n)^216)` at
`S_max = 4096`, against `agreeUdr` (np-udr-stark today):

| logN | 12 | 14 | 15 | **16** | 18 | 20 | 22 | 26 |
|---|---|---|---|---|---|---|---|---|
| np-udr-stark (`agreeUdr`) | −133.0 | −133.1 | −133.1 | −133.1 | −133.1 | −133.1 | −133.1 | −133.1 |
| R2 (`agreeAcc`, loss `t/n`) | −103.6 | −125.5 | −129.3 | **−131.2** | −132.6 | −133.0 | −133.1 | −133.1 |

`BudgetStmt` (`Bcs/Statements.lean:69`) needs ≤ 2^-129, so we require `logN ≥ 16` (`Dominates … 16 g16`).
The commit-phase term is a separate problem.
* `bcs_romSound` charges `badPot` with **unit weight**: every oracle query pays `B/2^256`
  (`Bcs/Compose.lean:111-112`). Merkle-node queries pay too, even though they can never be `RoundBad`.
* With the honest prover's `NPu ≈ 2^40` at `S = 1000`, `n = 2^26`, this gives
  `(2^64 + 2^40·NPu + NVu)·2^36·Dm / 2^256 ≈ 2^(80+49.7−256) = 2^-126.3`. That **exceeds the budget**.
* np-udr-stark today has `NPu ≤ 2^32`, which gives about 2^-134.

The fix (Q4) is to weight `badPot` by a challenge-query indicator (`x = whq (chalMsg d) 0`), exactly as
`queryPot` uses `qWeight chunkDec`.
* The term becomes `(2^64 + 2^40·NPc + NVc)·B·Dm/2^256`, where `NPc`/`NVc` are challenge queries per proof
  (about `S·(b+1) ≈ 2^14`).
* That gives `≈ 2^(64+49.7−256) = 2^-142`.

A "per-stage `B`" does not help under unit weight, because the uniform `B` is charged to every query, Merkle
nodes included.

The fix does not change the IOP.

---

## 2. Soundness decomposition and obligations

### 2.1 Doomed predicate (IOP level)

The predicate is defined by stage, as `Udr/Np/Stage.lean:195-211` does for np-udr-stark. Write
`SegFar j := ¬ Good (C^Nat) e' G_j 0 0`. Here `Good` is `Udr/Code.lean:56`; `Good C e u 0 0` means `u` is
`e`-close to `C`.

| Stage | Doomed | Transition bound |
|---|---|---|
| front end (R1) | `FrontDoomed` (bus, ALI and DEEP stages). At its end: `∃ j, SegFar j` | existing per-stage counts ≤ 2^36 (`Udr/Np/*`) |
| batch round `k` of step `i` | `¬ Good C^Nat e' (batchAll (r.take k) W_i) 0 0 ∨ ∃ j > i, SegFar j` | ≤ `3n + 2e' + 1` of `Kall` (strong line, §2.2) |
| commit `a_i` | `(∀ p, e' < dist n h_i (ev D p ∘ xs)) ∨ ∃ j > i, SegFar j` | message (frame) |
| group `X_i` | same | escape ⊆ "all of `X_i` in `Agr(u_i, h_i)`", where `u_i` is the unique `e`-decoding of `a_i`; `|Agr| ≤ n − e' − 1` (§2.3) |
| fills `φ_i` | `¬ RAcc_e(a_i, Z_i) ∨ ∃ j > i, SegFar j` (independent of fills) | message (frame) |
| decider batch / FRI | `¬ RAcc_e(a_S, Z_S)` → batch far → np FRI doom at radius `e'` | ≤ `3n + 2e' + 1`; FRI as `chalLate` (`Udr/Np/Late.lean:176`) |
| final query | FRI pass set `< n − e'` | `agreeAcc` (`fri_query_bound`, `Udr/Main.lean:33`) |

**Init.** `acc_0` satisfies `RAcc`, so `Doomed(step 1) ⇔ ∃ j, SegFar j`, which is the front end's exit doom.

**Step-to-step link.** This is the key implication. At radius `e' = e − t`, with `t' ≤ t` claimed positions:
```
Good C^Nat e' W_{i+1}  ⇒  RAcc_e(a_i, Z_i) ∧ ¬SegFar (i+1)
```
* The columns of `W` cover both.
* `shift_close` plus `quot_close` turn closeness of the shift columns into `RAcc_{e'+t'}`, and `e' + t' ≤ e`
  (§3).

### 2.2 (a) Accumulation step: IOP-level round-by-round soundness

**The algebraic lemma used.** This is the unique-decoding proximity gap for lines, in its strong
(containment) form:

> `strong_line_rs` (`Udr/Main.lean:18-22`): for interleaved RS with `2e + D ≤ n`, at most **`3n + 2e + 1`**
> challenges `z` in any duplicate-free list violate `Strong` (`Udr/Code.lean:62`).
>
> * It is derived from the correlated-agreement gap `RsGapStmt` (`Udr/Statements.lean:31`), proved as `rsGap`
>   (`Udr/BW.lean:89`, an elementary Berlekamp–Welch argument).
> * The derivation goes through `strong_of_gap` (`Udr/Code.lean:191`) and `gap_interleave`
>   (`Udr/Code.lean:338`).

Answers to the brief:

* **Is correlated agreement needed?** Yes, in its *line* form. The batching step needs the agreement set to
  be preserved (`Strong`), not just "the combination is far". It is already proved, at threshold
  `3n + 2e + 1` rather than BCIKS20's `n`. The cost is nil: `2^28 / |K| ≈ 2^-220` per query.
* **Is the brief's statement true?** "If `u` is `δ`-far, then at most `n` values of `α` make `u + αv`
  `δ`-close" is true in the unique-decoding regime by BCIKS20 Thm 4.1 (ε = n/|F|). It is weaker than what we
  use and **not new**. Its farness form, with bound `3n + 2e + 1`, is a 10-line corollary of `rsGap`. I proved
  it in the scratch PoC (`line_far`, §3), with axioms ⊆ {propext, Classical.choice, Quot.sound}.
* **Curves, affine spaces, list decoding and OOD binding are all avoided.** Batching is iterated lines
  (`batch_close` and `batch_chain`, `Udr/Deep.lean:105`/`:146`). Degree correction uses shifts plus batching
  instead of STIR's geometric-sum curve. Unique decoding makes the decoded `u_i` unique, so no OOD sample is
  needed.

**What is new for (a):**
* `shift_close` and `quot_close`, whose composition is `acc_close`, give the step-to-step link;
* `spot_doom` and `spot_escape` give the group transition;
* the stage plumbing: shape and frame lemmas, the stage decoder, and `Agr` as a function of the extracted
  transcript.

### 2.3 Spot-check group (the per-step query phase)

Before the group, `h_i` is `e'`-far.
* If `a_i` has no `e`-close codeword, `RAcc_e(a_i, ·)` fails for every claim set. No escape.
* Otherwise let `u_i` be the unique decoding (`LinCode.unique`, `Udr/Code.lean:104`).
  * If some `x ∈ X_i` has `u_i(x) ≠ h_i(x) = y`, then `¬RAcc_e(a_i, Z_i)` (`spot_doom`).
  * Hence escape ⇒ `X_i ⊆ Agr(u_i, h_i)`, and `count Agr + e' + 1 ≤ n` (`spot_escape`).

`Agr` is fixed before the group's answers are drawn: `a_i` is committed, and `h_i` depends only on earlier
entries. Each chunk's good-answer count is then exactly the `hG` bound of `stark_romSound_rbr`
(`Bcs/TransFinal.lean:95-96`): `agree^9 · 2^(256 − 9·logN)` (`chunkGood`, `Assembly/Params.lean:43`), with
`agree = agreeAcc`.

### 2.4 (b) Union bound over S steps

**It is absorbed by the potential.**
* `badPot` (`BadQuery.lean:30`, `bad_query_bound` at `:65`) charges each fresh query `B/2^256`, whatever round
  its extracted prefix is in.
* `queryPot` (`Product.lean:66`, `query_phase_bound` at `:313`) sums over **all touched prefixes** `p`. Its
  `QuerySuccess` (`Product.lean:73`) is `∃ p`, so intermediate groups and the final phase share one potential.

The bound is therefore `(#queries)·max-per-query-error`, independent of S. S appears only in
`NPu`/`NVu`/`NPq`/`NVq` (the honest and verifier query counts) and in `tapeLen`. The new work is only budget
arithmetic: a `budget32`/`QueryOk` variant with `NPq = NVq = (S_max+1)·24`, `NPu ≤ 2^44`, and
challenge-weighted `badPot` (Q4, §1.5). Unit weight makes the prover's `2^40·NPu` Merkle queries pay `B/2^256`
each, and that alone is 2^-126 at S = 1000.

### 2.5 (c) BCS / Fiat–Shamir in the ROM

What exists and is reused:

| Result | Location | Use in R2 |
|---|---|---|
| `romSound_of_potential` | `Game.lean:186` | as is (game → potential + deterministic acceptance) |
| `potential_simulate`, `prLE_of_potential` | `Potential.lean:129`, `:215` | as is |
| `bad_query_bound` | `BadQuery.lean:65` | as is (all `chal` rounds) |
| `product_step`, `query_phase_bound` | `Product.lean:201`, `:313` | as is (groups and final phase) |
| `pairPot_step`, `collision_bound` | `Collision.lean:291`, `:383` | as is (`N` grows to about 2^80) |
| `invPot` | `Bcs/InvPot.lean:489` | as is (`hN : N ≤ 2^100`) |
| `mmcs_binding_rooted`, `multiproof_sound` | `Bcs/Mmcs.lean:70`, `Bcs/Multiproof.lean:425` | as is (one MMCS per accumulator and segment) |
| `accept_imp_event_log` | `Bcs/Extract.lean:404` | **generalise**: `Chain` (`:151`) and `extPT` (`:126`) gain a `group` step |
| `bcs_romSound` | `Bcs/Compose.lean:79` | **generalise**: `hquery` covers both final and group prefixes, and `badPot` is weighted by challenge queries (Q4) |
| `transport`, `decQuery`, `posCount` | `Bcs/TransCompose.lean:38`, `Bcs/DecQuery.lean:355`, `Bcs/PosCount.lean:118` | adapt (group positions decoded like final ones) |
| `stark_romSound_rbr` | `Bcs/TransFinal.lean:85` | template for `acc_romSound_rbr` from `RbrWithQ` |
| `compile_accepts` | `Bcs/StarkMain.lean:105` (8 files `Bcs/Stark*.lean`) | **new instance** for the accumulation verifier (largest engineering item) |
| `np_romSound`, `stark_romSound_full`, `np_admission` | `Assembly/RomBound.lean:58`, `Assembly/RomFull.lean:27`, `Assembly/Admission.lean:45` | templates |

**Hypotheses the L2 results need, and how R2 meets them:**
* binding/rooted commitments: MMCS, unchanged;
* per-challenge bad count `B ≤ 2^50` (`BudgetStmt`): `2^36·Dm`;
* per-chunk good count `g j`: `chunkGood agreeAcc`;
* `2 ≤ numChunks ≤ 2^32`: 24;
* `qH + qP·NPu + NVu ≤ 2^100`: about 2^80;
* `QueryBound`s for `unitWeight` and `qWeight chunkDec` on the trees: from the header caps;
* a concrete verifier lemma `TableWF tbl → evalT tbl (V.tree …) = some true → AcceptsIn iop tbl ctx cb`
  (`AcceptsIn`, `Bcs/Extract.lean:178`): `compile_accepts` analogue.

**Why group answers must feed the state.** `Extract.lean:16-24` already notes that a challenge which does not
feed the state lets the adversary fix later rounds before drawing it. A group drawn as `H(QUERY ‖ d ‖ j)`, with
`d' = WH(GRP, d)` independent of the answers, has the same gap. In particular, `r_{i+1}`'s bad set depends on
`Z_i` through `W_{i+1}`. That is why `d'` absorbs `y_0..y_23`.

### 2.6 Why claims, not direct comparison (the radius-degradation trap)

Suppose step `i` checked `a_i(x) = h_i(x)` at `t` positions, with no claims. A cheating prover can commit
`a_i := h_i` with `σ` positions moved towards a codeword just beyond the radius. The check then passes with
probability `(1 − σ/n)^t`, and the radius shrinks by `σ` per step.
* For per-attempt error 2^-192 at `t = 216`, the slack must satisfy `σ ≥ 0.46·n`, i.e. the whole radius.
* Conversely, keeping `S·σ ≤ e` at `S = 1000` needs `t ≈ 4·10^5` per step.

Claims compare the **decoded** `u_i` with `h_i`, so the radius `e` is restored at every step. The only loss is
the in-domain quotient's `t/n`, inside one step (`quot_close`).

**The degenerate "deferred" variant.** All checks are at the final positions, with no `a_i` commitments. This is
literally R1's batched FRI (`batch_chain` + FRI roll-ins) and is provable today. "Accumulation" adds nothing
there.

### 2.7 Obligation table

| Obligation | Status | Reused results (file:line) | New LOC (est.) |
|---|---|---|---|
| (a1) Line gap / strong line at d/2 for batching rounds | **proved** | `rsGap` `Udr/BW.lean:89`; `strong_line_rs` `Udr/Main.lean:18`; `batch_close`/`batch_chain` `Udr/Deep.lean:105`/`:146` | 0 |
| (a2) Degree correction by shifts (`shift_close`) | **new** (PoC) | `IsPoly.mulX` `Udr/Poly.lean:141`, `coeffs_zero_of_roots` `:219`, `ev_pad` `:95`, `ev_eq_of_agree` `Udr/RS.lean:39` | 150–250 |
| (a3) Quotient with in-domain claims and fill (`quot_close`) | **new** (PoC) | `gpP`, `gpP_isPoly` `Udr/GrandProduct.lean:54`/`:83`, `IsPoly.mul` `Udr/Poly.lean:148`, `dist_mono` `Udr/Code.lean:80` | 150–250 |
| (a4) Spot-check doom/escape (`spot_doom`, `spot_escape`) | **new** (PoC, easy) | `LinCode.unique` `Udr/Code.lean:104`, `count_add_count_not` `Udr/Count.lean:138` | 60–100 |
| (a5) Accumulation stage machine: `AccDoomed`, `RbrWithQ` fields per slot, shape/frame lemmas, `Agr` from the extracted transcript | **new** | pattern `Udr/Np/{Stage,Shape,Frame*,Late}.lean`; `RbrWith` `Udr/Rbr.lean:59` | 2,500–4,000 |
| (a6) Multi-segment front end (S segments, global buses, DEEP doom at radius `e'`) | **shared with R1**, adapt | `Udr/Np/*` (8.8k), `rbrWith` `Udr/Np/Main.lean:29`, `msg8` `Udr/Np/Msg8.lean:282` | counted under R1 (radius parametrisation, Q5: 200–500) |
| (b) Union bound over S | **absorbed** by the potentials | `bad_query_bound`, `query_phase_bound` (any prefix) | 0, plus budget arithmetic and challenge-weighted `badPot` 300–800 (Q4) |
| (c1) BCS extraction with query groups | **adapt (medium)** | `accept_imp_event_log` `Bcs/Extract.lean:404`, `bcs_romSound` `Bcs/Compose.lean:79` | 1,500–3,000 |
| (c2) Transport `RbrWithQ` → BCS `Doomed` | **adapt** | `transport` `Bcs/TransCompose.lean:38`, `DecQuery`, `PosCount` | 1,000–2,000 |
| (c3) Deployed verifier + `compileQ` + `compile_accepts` analogue + `NVu` bound | **new** (engineering) | `Stark/Bcs.lean`, `Bcs/Stark*.lean`, `Stark/QueryBound.lean` | 3,000–5,000 |
| (d) Decider = batch + FRI | **proved**, small adaptation (radius `e'`, single word, no roll-ins) | `fri_query_bound` `Udr/Main.lean:33`, `FriStmt` `Udr/Statements.lean:110`, `chalLate` `Udr/Np/Late.lean:176`, `query_of_deepSem` `Udr/Np/Bridge7.lean:262` | 300–800 |
| (e) Completeness for every `H`, proof-size bound, `NPu` bound | **new**, following the np pattern | `np_proverComplete` `Prover/Compose.lean:89`, `npIopComplete'` `Prover/NpLocalMain.lean:127`, `Poly.lagrange_spec` `Algebra/Main.lean:24` | 3,000–5,000 |
| Assembly (`acc_romSound_full`, `acc_admission`, kernel numerics) | **adapt** | `Assembly/*` (0.5k) | 300–600 |
| **Total new (excluding R1's front end)** | | | **≈ 11–19k** |

Calibration: L3 (`Udr` with `Udr/Np`) is 11.2k lines, `Bcs` 5.5k, `Prover` 7.9k and `Stark` 2.9k. R2 adds to the
elaboration budget (candidate already at 647 s of 1,800 s per `V3-D0-DESIGN.md`): about 150–250 s at 12 s/kLOC.

---

## 3. PoC core lemma: exact statement, proof sketch, dependencies

**What is new.** The line gap is not new (`rsGap`). The genuinely new algebra is the **closeness transfer
through one accumulation step**. If the degree-corrected quotient word of `(a, Z)` is `e'`-close to the
interleaved RS code, then `a` satisfies the accumulator relation at radius `e' + |Z|`. To that we add the two
spot-check facts.

**Status: kernel-checked.** All six statements below are proved in the separate Lake package
`recursion-poc/` (`RecursionPoc/Accumulation.lean`, namespace `RecursionPoc`). The package imports
zk-formal's `Udr` layer read-only (`[[require]] ZkFormal = ../zk-formal`); zk-formal is not modified.
There is no `sorry`, no `native_decide` and no Mathlib, and `#print axioms` gives propext,
Classical.choice and Quot.sound for each. `shift_close` uses `coeffs_zero_of_roots` on the
coefficients of `x^t·p_0 − p_t` (new helper `ev_shiftC`). `quot_close` builds `p = ans + V·q` with
`IsPoly.mul`, using new helpers `gpP_ne_zero`, `gpP_root` and `count_mem_le`; these three are
request Q9. The proof is about 300 lines, below the 400–600 LOC estimate. The statements were
originally in the scratch file `R2Poc.lean` and are reproduced here with the `R2Poc` namespace.

```lean
import ZkFormal.Udr.Main
import ZkFormal.Udr.GrandProduct
namespace R2Poc
open ZkFormal.Udr ArenaCore.Security Lean.Grind
variable {K : Type} [Field K]

def RAcc (xs : Nat → K) (n D e : Nat) (a : Word Unit K) (T : List Nat) (y : Nat → K) : Prop :=
  ∃ p : Nat → K, dist n a (fun i _ => ev D p (xs i)) ≤ e ∧ ∀ i ∈ T, ev D p (xs i) = y i

def quotW (xs : Nat → K) (T : List Nat) (ans : K → K) (fill : Nat → K) (a : Word Unit K) :
    Word Unit K :=
  fun i _ => if i ∈ T then fill i else (a i () - ans (xs i)) * (gpP (T.map xs) (xs i))⁻¹

def shiftW (xs : Nat → K) (t : Nat) (Q : Word Unit K) : Word Nat K :=
  fun i c => if c ≤ t then xs i ^ c * Q i () else 0

theorem shift_close (xs : Nat → K) (n D t e : Nat) (hD : D ≤ n) (hxs : Distinct xs n)
    (htD : t ≤ D) (hn : e + D + t ≤ n) (Q : Word Unit K)
    (h : Good (rsInterleaved xs n D hD hxs Nat) e (shiftW xs t Q) (fun _ _ => 0) 0) :
    ∃ q : Nat → K, dist n Q (fun i _ => ev (D - t) q (xs i)) ≤ e

theorem quot_close (xs : Nat → K) (n D e : Nat) (hxs : Distinct xs n) (T : List Nat)
    (hT : T.Nodup) (hTn : ∀ i ∈ T, i < n) (htD : T.length ≤ D)
    (ans : Nat → K) (y : Nat → K) (hans : ∀ i ∈ T, ev T.length ans (xs i) = y i)
    (fill : Nat → K) (a : Word Unit K) (q : Nat → K)
    (hq : dist n (quotW xs T (ev T.length ans) fill a) (fun i _ => ev (D - T.length) q (xs i)) ≤ e) :
    RAcc xs n D (e + T.length) a T y

/-- **PoC core lemma** (closeness transfer through one accumulation step). -/
theorem acc_close (xs : Nat → K) (n D e : Nat) (hD : D ≤ n) (hxs : Distinct xs n)
    (T : List Nat) (hT : T.Nodup) (hTn : ∀ i ∈ T, i < n) (htD : T.length ≤ D)
    (hn : e + D + T.length ≤ n)
    (ans : Nat → K) (y : Nat → K) (hans : ∀ i ∈ T, ev T.length ans (xs i) = y i)
    (fill : Nat → K) (a : Word Unit K)
    (hW : Good (rsInterleaved xs n D hD hxs Nat) e
      (shiftW xs T.length (quotW xs T (ev T.length ans) fill a)) (fun _ _ => 0) 0) :
    RAcc xs n D (e + T.length) a T y

theorem spot_doom (xs : Nat → K) (n D e : Nat) (hD : D ≤ n) (hxs : Distinct xs n)
    (he : 2 * e < n - D + 1) (h a : Word Unit K) (p : Nat → K)
    (hp : dist n a (fun i _ => ev D p (xs i)) ≤ e) (X : List Nat) (hX : ∀ i ∈ X, i < n)
    (hbad : ∃ i ∈ X, ev D p (xs i) ≠ h i ()) :
    ¬ RAcc xs n D e a X (fun i => h i ())

theorem spot_escape (xs : Nat → K) (n D e' : Nat) (h : Word Unit K)
    (hfar : ∀ p : Nat → K, e' < dist n h (fun i _ => ev D p (xs i))) (p : Nat → K) :
    count (List.range n) (fun i => ev D p (xs i) = h i ()) + e' + 1 ≤ n

/-- Farness corollary of the proved BW gap (proved in the scratch PoC). -/
theorem line_far (xs : Nat → K) (n D e : Nat) (hD : D ≤ n) (hxs : Distinct xs n)
    (he : 2 * e + D ≤ n) (u v : Word Unit K)
    (hfar : ¬ ∃ w, (rsCode xs n D hD hxs).mem w ∧ dist n u w ≤ e)
    (Ks : List K) (hKs : Ks.Nodup) :
    count Ks (Good (rsCode xs n D hD hxs) e u v) ≤ 3 * n + 2 * e + 1
```

**Proof sketches.** Each statement was checked by hand to be true.

* **`shift_close`.**
  1. `Good` yields an interleaved codeword `w = (ev D p_c ∘ xs)_c` that agrees with `shiftW` on a set `A`
     with `|A| ≥ n − e`.
  2. On `A`: `Q = p_0` (column 0), and `x^t·p_0(x) = p_t(x)` (column `t`).
  3. Both sides are polynomials of length `D + t`. Since `|A| ≥ D + t` distinct points (`hn`),
     `coeffs_zero_of_roots` gives `x^t·p_0 ≡ p_t` coefficientwise. This needs a small lemma:
     `ev (D+t) (shift t p_0) x = x^t · ev D p_0 x`, by induction on `t` using `ev_succ`.
  4. Comparing coefficient `k + t` gives `p_0 k = 0` for `k ≥ D − t`, so `ev D p_0 = ev (D−t) p_0` (`ev_pad`).
  5. Take `q := p_0`. Then `dist ≤ n − |A| ≤ e`.
* **`quot_close`.**
  1. Let `p := ans + V·q` with `V = gpP (T.map xs)`. Its length is `D`: `IsPoly (t+1) V` and
     `IsPoly (D−t) q` give, by `IsPoly.mul`, length `D` (and `p = ans` if `D = t`).
  2. For `i ∉ T`, `V(xs i) ≠ 0`: no factor vanishes, by `Distinct`. So `quotW i = q(xs i)` implies
     `a i = p(xs i)`, by field algebra with `mul_inv_cancel` and `grind`.
  3. For `i ∈ T`, `V(xs i) = 0` because one factor is zero, so `p(xs i) = ans(xs i) = y i`.
  4. Hence `dist(a, p) ≤ dist(quotW, q) + |T|`, using `count (range n) (· ∈ T) ≤ |T|` for nodup `T`.
     **The fill value never matters.**
* **`acc_close`.** This is `shift_close`, then `quot_close`. It is proved in the scratch file.
* **`spot_doom`.** `RAcc` gives `p'` with `dist(a, p') ≤ e`. Both `p` and `p'` are `e`-close to `a` and
  `2e < d`, so `p = p'` on `[0, n)` (`LinCode.unique` on `rsCode`). That contradicts `hbad` at the bad
  position.
* **`spot_escape`.** This is `count P + count ¬P = n` (`count_add_count_not`) applied to the definition of
  `dist`.

**Dependencies.** Only `ZkFormal.Udr.*`: `Code`, `RS`, `Poly`, `GrandProduct`, `Count`, `Main`/`BW` for
`line_far`. These depend on `ArenaCore` (counting) and core Lean's `Lean.Grind.Field`. There is **no Mathlib**,
no `native_decide` and no new axioms. Estimate: **400–600 LOC** for all five.

**Packaging: importing zk-formal versus self-contained.**

A separate PoC package **can import zk-formal read-only**:
* zk-formal is the Lake package `ZkFormal` (`zk-formal/lakefile.toml`), with `require ArenaCore` from
  `../formal-core` and `NearSpec` from `../spec/lean`.
* Its toolchain is `leanprover/lean4:v4.34.1`, the same as `formal-core/lean-toolchain`.
* A package at, for example, `docs/research/../r2-poc/` with
  `[[require]] name = "ZkFormal" path = "../zk-formal"` resolves the transitive path dependencies relative to
  zk-formal.
* Caveat: building writes oleans into `zk-formal/.lake/`. That is build output, not sources. This worktree has
  no `.lake` yet, and the scratch check used the main checkout's build, whose `Udr/` sources are identical.

**For admission**, the R2 modules must live **inside the candidate package**. F4 limits the
`allowed_packages` to `ArenaCore` and `NearSpec`, so the modules would be a new `lean_lib` or namespace in
zk-formal, or a vendored copy (Q7). The PoC itself does not need to be self-contained.

---

## 4. Interface needs with zk-formal (requests; not filed)

**R2 would import:**
* **Udr:** `Word`, `dist`, `LinCode`, `line`, `Good`, `Strong`, `CA`, `LinCode.unique`, `rsCode`,
  `rsInterleaved`, `Distinct`, `ev`, `IsPoly.*`, `coeffs_zero_of_roots`, `ev_pad`, `gpP`, `gpP_isPoly`,
  `strong_line_rs`, `rsGap`, `batchAll`, `batch_close`, `batch_chain`, `deepW`, `deep_close`, `deep_value`,
  `Fri.Setup`/`Run`, `fri_query_bound`, `RbrWith`, `agreeUdr`.
* **Np front end:** `Udr.Np.Stage`/`Doomed`/`rbrWith`, generalised to S segments.
* **Stark:** `IopSpec`, `PT`, `Slot`, `Part`, `Oracle`, `Mat`, `positions`, `Bcs.compile`, `QueryBound.*`.
* **Bcs:** `Entry`, `Chain`, `extPT`, `AcceptsIn`, `RoundBad`, `Good`, `accept_imp_event_log`, `bcs_romSound`,
  `bcsNum`, `budget`, `chunkQ`/`chunkDec`, `mmcs_binding_rooted`, `multiproof_sound`, `transport`, `decQuery`,
  `posCount`, `hdec_deployed`.
* **Top level:** `Game.romSound_of_potential`, `TreeVerifier`, `TreeProver`, `Potential.*`, `BadQuery.*`,
  `Product.*`, `Collision.*`.
* **Assembly:** `chunkGood`, `QueryOk`, `Dominates`, `budget32`, the pattern of `np_admission`.
* **Algebra:** `Fp`, `Fp8`, `Fp8.all`, `decodeChal`/`decodeOod`, `Poly.lagrange_spec`.

**Requests:**

| Id | Request | Why | Size |
|---|---|---|---|
| **Q1** | **Intermediate query groups in BCS.** Add an `Entry.group (ys : List Bytes)` and `EntryV.group` with state update `d' = WH(GRP, d ‖ ys)` and answers `ys_j = H(chunkQ d j)` checked in `Chain`. Extend `extPT`, `accept_imp_event_log` and `bcs_romSound` so that `hquery` covers group prefixes too. Groups use `chunkQ`, so `queryPot` and `QuerySuccess` are unchanged. `opens` may reference positions from earlier groups. | The per-step spot checks need a product potential at intermediate states. A single 256-bit challenge cannot give 2^-192 per attempt. | 1.5–3k |
| Q2 | `Stark.IopSpecQ`: a `Slot.group` slot, `PT.pushGroup`, `NextIsGroup`, group positions via `positions`. `check`/`prep` may read openings at group positions, so that claims are computed from true openings. `trueOpenings` is extended to group positions. | So the IOP can express mid-protocol reads that define later claims. | 0.5–1k |
| Q3 | `Udr.RbrWithQ`: `RbrWith` (`Udr/Rbr.lean:59`) plus a `group` field: `∃ Agr`, `count Agr ≤ agree n`, and escape ⇒ every group position lies in `Agr`. A matching `stark_romSound_rbr` (`Bcs/TransFinal.lean:85`) for `compileQ`. | The L3→L2 interface for groups. | 1–2k (with Q1/Q2) |
| Q4 | **Challenge-weighted `badPot`** in `bcs_romSound` (`Bcs/Compose.lean:111`): use weight `[x is a CHAL first-half query]` instead of `unitWeight`, with new budgets `NPc`/`NVc`. Budget variants: `budget32` (`Assembly/Budget32.lean:31`) and `QueryOk` (`Assembly/Params.lean:49`) with `NPq = NVq = (S_max+1)·K`, `NPu ≤ 2^44` (`N ≤ 2^84`). | S = 1000 segments raise the honest prover's query count to about 2^40. Under unit weight the commit-phase term is 2^-126, which fails 2^-128. With challenge weight it is about 2^-142. | 0.3–0.8k |
| Q5 | Radius as a parameter: `rbrWith`, `np_romSound` and `Dominates` instances that take `agree` (radius `e' = e − t`) instead of a hard-coded `agreeUdr`. `FriStmt` is already generic in `e`. | The accumulator loses `t` positions inside a step. | 0.2–0.5k |
| Q6 | Multi-segment front end: Np stages for S segments with shared bus challenges, exiting with `∃ j, SegFar j` at radius `e'`. | Shared with R1; R2 cannot avoid it (§5). | (R1) |
| Q7 | Packaging: an R2 `lean_lib` inside the candidate package (or a policy for vendoring zk-formal), because of `allowed_packages`. | Admission (F4). | — |
| Q8 | A bridge from `Algebra.Poly.lagrange` to `Udr.ev` coefficient form, for the verifier's `Ans` and for completeness. | (e) | 0.2–0.4k |
| Q9 | Small `Udr.Count` additions: `count (range n) (· ∈ T) ≤ T.length` for nodup `T`, and a lemma that a product with a zero factor is zero (`gpP` at a root). | PoC convenience | < 0.1k |

---

## 5. Consequence for the R1/R2 decision (analytical, unmeasured)

1. **Openings do not shrink.** Each segment's oracles must be opened at about 216 positions to evaluate `G_i`.
   That is the same count as in R1.
2. **R2 adds openings that R1 does not have:**
   * the accumulator `a_{i−1}`, one 8-limb row per position;
   * a separate set of Merkle paths per step for segment `i`'s trees and the accumulator.

   In R1, all segments are opened at the **same** positions, so one MMCS per phase can hold every segment and
   its paths are shared.

   **Rough estimate.** At `W_seg ≈ 3000` (about 12 KB per row set) and about 1.2 KB per deduplicated path, R2
   costs about 40% more per segment.
3. **The prover schedule is the same.** Global bus challenges force all S main commitments before any
   challenge, in both R1 and R2. R2 therefore does not buy a single-pass prover. Per-segment memory is the
   same, since R1's batched DEEP word can also be accumulated while streaming.
4. **The verifier's work is the same or larger.** DEEP and batch evaluation per position per segment is
   unchanged, and R2 adds the quotient and interpolant work: `O(t²)` per step, about 5·10^7 `K`-operations at
   S = 1000.

Accumulation pays off when the verifier would otherwise **re-run** inside a circuit (R3), and that is
inadmissible here. With a native verifier, R2 looks dominated by R1 in proof size, verify time and prover
schedule. It is also about 11–19k LOC more formal work, plus Q1–Q3 in the riskiest lane (L2 extraction).
Unless the R1 cost curve shows a specific bottleneck that R2 removes, the decision memo should treat R2 as
**not worth pursuing**. The theorem above shows it is *provable* inside the existing admission theorem, so the
rejection is on cost, not on admissibility.
