# A formally admitted STARK backend for `chl_3be93793610370275ae40f36a475f01f`: design

Status: design phase, 2026-10-03. Branch `lane/zk-formal`.
Proofs of concept: `zk-formal/` (Lake package `ZkFormal`, depends only on
`formal-core`; 1.7k LOC; sorry-free; axioms ⊆ {propext, Classical.choice,
Quot.sound}; clean build about 1 s).

**Goal.** Get a succinct proof backend (a STARK) to PASS every strict formal
gate on challenge `near-transfer-receipt-v1-2`. That challenge uses the
`validity-classical-128` profile: random-oracle model, transparent setup,
target 128 bits, at most 2^64 hash queries and at most 2^40 prover
(honest-proof) queries. Zero knowledge is not required.

---

## 0. Decisions at a glance

| Question | Decision | Main reason |
|---|---|---|
| A. Proof system | **(iii) A custom STARK designed to be provable: "np-udr-stark".** It uses DEEP-ALI with batched FRI, analysed only in the unique-decoding regime. The field is BabyBear with a degree-8 extension. All hashing goes through the oracle, with 512-bit Merkle and transcript digests. There is no proof-of-work grinding, and the multiset argument is a grand product (not LogUp). The Rust prover reuses Plonky3 crates for the field, DFT and matrices. | Plonky3 as it stands cannot be admitted, whatever the parameters (§3). The profile forces 512-bit digests, perfect completeness for every hash function, and an error of at most 2^-192 per query. Every soundness step of (iii) reduces to an elementary unweighted line lemma, which has already been proved here without Mathlib (§6.4, PoC). |
| B. Arithmetization | **The AIR is defined in Lean and is the single source of truth.** It is a symbolic `Expr` DSL with tables and buses. The verifier evaluates constraints from that Lean definition, and the Rust prover consumes a JSON/codegen export of it. Tables are re-laid out to fit a width budget. SHA-256 uses an OpenVM-style layout (17 rows per block), following the openvm-fv proof structure re-proved without Mathlib. | Soundness then does not depend on the Rust prover at all: a mismatch between the Rust and Lean AIRs can only make honest proofs fail, and differential tests catch that. |
| C. Verifier connection | **native-lean (`.nativeTrusted`) first.** The verifier model is a hash-query tree (`TreeVerifier`), and a fast SHA-256 that is proven equal to the spec is installed with `@[csimp]`. Porting to NPAI (`.interp`, status *checked*) is optional later work. | reexec-witness was admitted on this route. NPAI bytecode proofs cost about 22k LOC per 3.8k instructions (reexec-npai). |
| D. Parameters | Rate 1/16, LDE domain ≤ 2^26, **216 queries** (24 oracle answers × 9 positions), FRI binary folds with arity-8 commitments, final polynomial degree < 2. **Bound ≤ 2^-132, checked by the kernel** (`ZkFormal.Params.udr2_ok`). Fallback with the elementary d/3 radius: 360 queries (`udr3_ok`). | Proof size about 3–4.5 MiB against an 8 MiB cap. Verifier hashing takes about 0.2 s with the fast SHA, or about 8 s with `ArenaCore.sha256` as compiled today. |
| E. Riskiest piece | **The Fiat–Shamir/BCS compilation inside ArenaCore's ROM game.** It has never been done for multi-round IOPs; ArkLib and VCVio stop at definitions or Σ-protocols. | Its probabilistic core is now proved (§10). What remains of that lane is the deterministic extraction lemma. |

Honest effort estimate: **70–105k lines of Mathlib-free Lean plus 8–12k lines of Rust, over 8 lanes.** The critical path for risk runs L1 → L3/L2 → L7. The critical path for volume is L6 (the NEAR AIR proofs). §9 has the details, and §11 lists what could make full admission infeasible.

---

## 1. Constraints imposed by the arena (facts)

| # | Fact | Source |
|---|---|---|
| F1 | The certificate must inhabit `AdmissionStatement ch art`. For the ROM branch, `CryptoSound` needs three things: an honest prover `P` with `ProverComplete` for **every** hash function `H`; a bound `num·2^128 ≤ den`; and `RomSound … (2^64) (2^40) tapeLen num den`. | `formal-core/ArenaCore/Admission.lean` `CryptoSound` |
| F2 | The ROM game runs the **deployed** verifier tree. Oracle answers are uniform 32-byte values from a tape. The adversary's `prove cb w` queries are answered by `P.run` through the **same** oracle. Overflowing the tape counts as a win. | `Security/ROM.lean` `romImpl`, `romWins` |
| F3 | `ProverComplete`: for all `H`, in-domain `c`, `w`, the honest proof is ≤ `maxProofBytes` and is accepted. `P` is the candidate's **Lean model**: it is never executed, but it must be total and correct for adversarial `H` (for example, constant `H`). | `Verifier.lean` |
| F4 | `allowed_packages = [ArenaCore, NearSpec]`. **No Mathlib, ArkLib or VCVio.** Every reused proof has to be re-proved. | challenge JSON `toolchain_policy` |
| F5 | Axioms ⊆ {propext, Classical.choice, Quot.sound}. No `native_decide`. `decide +kernel` is allowed and is used by reexec-npai. | `FORMAL_INTERFACE.md` §7 |
| F6 | Checker budgets: 600 s per module, **1800 s total elaboration**, 1200 s per recheck, 64 GiB by default. For comparison, reexec-npai (25k LOC) took 409 s to elaborate and 237 s for lean4lean. | `runners/formal-checker/src/pipeline.rs` `Limits`; `docs/e2e-results/reexec-npai` |
| F7 | Resource limits: proof ≤ 8 MiB, verify ≤ 10 s, prove ≤ 600 s, RAM 16 GiB, 8 vCPU. | challenge `resource_limits` |
| F8 | The deployed protocol hash is `Interp.deployedRO = sha256("NPAI-RO-v1" ‖ m)`, using the `Nat`/`List` `ArenaCore.sha256`. Measured compiled throughput (Lean 4.34.1, this host): **41 µs per 64-byte block**. A plain-Lean `UInt32`/`ByteArray` SHA-256 runs at **0.8 µs per block** and agrees on test vectors. A downstream `@[csimp]` lemma does redirect compiled calls of `ArenaCore.sha256`; I checked this in the generated C. | scratch benchmarks (§10.3) |
| F9 | `NearSpec.sha256` is an `abbrev` for `ArenaCore.sha256`, so there is one SHA-256 in the TCB. `NearRelation` is decidable and kernel-evaluable. | `spec/lean/NearSpec/SHA256.lean`; agent survey |
| F10 | Domain: `ClaimDomain` (PV 86, mainnet, 1 ≤ n ≤ 256, gas). `NearRelation` additionally implies `revealedBytes ≤ 3,000,000`, which allows about 100k SHA-256 compressions in the worst case (pre-root and post-root passes, plus receipts). | `TransferV1.lean`; survey |
| F11 | Core Lean's `grind` proves field identities over the abstract class `Lean.Grind.Field` (tested: solving for line coefficients, cancellation with inverses). That makes Mathlib-free algebra practical. | `zk-formal/ZkFormal/LineLemma.lean` |

## 2. Requirements derived from the facts

**R1. 512-bit digests (wide hashing `WH`).** The oracle log contains the adversary's 2^64 queries plus the honest prover's hashing for up to 2^40 proofs. Each proof hashes Merkle trees over the LDE: up to about 2^29 oracle calls. That gives Q ≈ 2^70. A 256-bit collision then has probability about Q²/2^257 ≈ 2^-117. Even with the prover's hashing ignored, Q = 2^64 already costs 2^-129 of the 2^-128 budget. Merkle nodes and the Fiat–Shamir state therefore use `WH(m) = H(0x01‖m) ‖ H(0x02‖m)` (64 bytes). Binding becomes a pair event at 2^-512. It is proved (`collision_bound`, §10).

**R2. Per-query RBR error ≤ about 2^-192.** Every Fiat–Shamir query is an attempt. The bound is roughly Q_FS·ε_rbr ≤ 2^-128 with Q_FS ≈ 2^64. This applies to the commit-phase challenges and to the whole query phase.

**R3. No proof-of-work grinding.** For an adversarial `H` (for example a constant), no grinding nonce may exist, which breaks `ProverComplete` (F3).

**R4. Totality for every `H`.**
* **Out-of-domain point.** `z` must avoid the trace and LDE domains (which lie in `F_p`). We sample `z` in `K \ F_p`: decode 8 limbs; if all non-constant limbs are 0, set limb 1 to 1. All 2-power roots of unity of order ≤ 2^27 lie in `F_p`, so `z^T ≠ 1`.
* **No LogUp.** With LogUp the honest prover needs `1/(β − fp_i)`, which fails when `β` equals a fingerprint, and that is possible for some `H`. Instead, buses use a **grand-product multiset argument** with separate numerator and denominator accumulators. That argument is total: honest products agree for every challenge. Provider multiplicities are bit-decomposed (exponents ≤ 2^25). Soundness: a bivariate Schwartz–Zippel argument, split into two single-answer rounds (fingerprint `α`, then product point `γ`), with error ≤ #messages·width/|K| and ≤ #messages/|K|.
* FRI division by `2x` and DEEP division by `x − z` are always well defined.

**R5. Challenge field of size ≥ 2^215 that is provably a field without Mathlib.** We use BabyBear `p = 15·2^27+1` and `K = F_p[X]/(X^8 − 11)`, which is Plonky3's `BinomialExtensionField<BabyBear, 8>`, with |K| ≈ 2^247.7. The proof that `K` is a field goes through a quadratic tower `F_p ⊂ F_p[y]/(y²−11) ⊂ (·)[z]/(z²−y) ⊂ (·)[x]/(x²−z)`. At each level `a + b·t` is invertible via the norm. Non-squareness propagates through norms because `−1` is a square. The base fact "11 is a non-square mod p" follows from Euler's criterion: 11^((p−1)/2) = −1 by kernel computation, plus Fermat's little theorem. Primality of `p` is a kernel trial division up to 44 869. Two-adicity is 27, the largest among BabyBear, KoalaBear (24) and M31.

**R6. The query phase needs many oracle answers.** 216 positions × 26 bits exceeds 256 bits, so positions come from 24 answers `H(QUERY ‖ d ‖ j)`, which the adversary can request in any order. This is handled by the product potential (`query_phase_bound`, §10).

**R7. Worst-case completeness.** `ProverComplete` covers **every** in-domain witness, including the 3 MB trie case. The maximum heights must fit the field's 2-adicity at rate 1/16 (LDE ≤ 2^27 means height ≤ 2^23; we cap height at 2^22 and LDE at 2^26). There must also be a Lean theorem bounding the honest trace heights from `NearRelation`.

**R8. Proof ≤ 8 MiB at the maximum heights; verify ≤ 10 s.** Native-lean verification at 41 µs per block exceeds the budget (§8), so it needs the fast proven-equal SHA (`@[csimp]`) or the NPAI route.

**R9. No Mathlib.** Every polynomial, coding-theory and probability lemma is written against ArenaCore's counting framework and `Lean.Grind.Field`.

**R10. One AIR definition.** The deployed verifier, the soundness theorem and the Rust prover's constraint evaluation must all come from the same Lean AIR value.

## 3. Decision A: which proof system

### (i) Keep Plonky3 batch-STARK as is: not admissible

Facts from `examples/stark-plonky3` (`source/src/config.rs`, `EVIDENCE.md`, `README.md`):

* **32-byte SHA-256 Merkle digests** violate R1.
* **20 bits of query proof-of-work** violates R3.
* **LogUp** violates R4.
* **Duplex `SerializingChallenger32`**: chained 256-bit sponge state, so state collisions fall under R1 again.
* **Degree-8 KoalaBear extension**: two-adicity 24, so the LDE is at most 2^24 (R7 is tight).
* **104 queries**: profile bits are UDR 38.5 and Johnson 107. Only the *conjectured* bound reaches 128, and the example states `SECURITY_BOUND_INSUFFICIENT` itself.
* The verifier is the stock `p3_batch_stark::verify_batch`, plus mixed-height FRI, quotient chunking and postcard decoding. About 70k lines of Rust would have to be modelled exactly in Lean.

### (ii) Re-parameterize Plonky3: still fails, and costs more

To reach the proven UDR bound at the profile's budgets, Plonky3's own sweep needs **240 queries, giving a ≈16 MB proof**, because each query costs ≈65 KB at a width of 10,817 + 3,800 (aux). R1, R3 and R4 still require replacing the hasher, the challenger, the PoW step and LogUp. At that point nothing of Plonky3's protocol is left, but its full complexity would still have to be formalized.

### (iii) Custom provable STARK: chosen

Every simplification below is driven by provability, and each has a modest cost.

| Choice | Provability gain | Cost |
|---|---|---|
| UDR-only analysis | Needs only the *unweighted* line lemma (§6.4). The Johnson regime needs weighted correlated agreement, which is the part still sorried in ArkLib (`Fri.fri_query_soundness`). | ≈2× the queries of the conjectured regime |
| Every challenge is one oracle answer, except the query phase | Every commit round is an instance of `bad_query_bound` | none |
| Full-prefix FS through a 512-bit hash chain | The transcript prefix is decoded from the log; no sponge or state-collision analysis | 3 oracle calls per round |
| Batching by multilinear line rounds (log₂ #columns rounds) | Only the line lemma for *interleaved* codes is needed, not curves or affine spaces | ≈12 extra challenges |
| Binary folds, arity-8 commitments (virtual middle layers) | Each fold is a line; virtual layers are consistent by definition | none |
| Mixed heights by roll-in (`f ← fold(f) + γ·G`) | Each roll-in is also a line | one challenge per distinct height |
| Grand product instead of LogUp | Total (R4); the soundness argument is elementary | provider multiplicities need about 25 bit columns per provider row (small tables only) |

**Ligero/Brakedown** was considered and rejected. Its proximity analysis is simpler (no recursion), but the proof contains a combined row of length about the trace height for each batched polynomial. At the maximum heights that is ≈2^22 × 32 B = 128 MB, which breaks R8, and its column openings cost width × queries, the same as the STARK's first layer. FRI is needed for succinctness at this width.

## 4. The protocol `np-udr-stark-v1`

Below, `H` is the protocol oracle. In deployment `H(m) = sha256("NPAI-RO-v1" ‖ m)`, the same function as `deployedRO`. All encodings are length-prefixed and injective, and domain tags are single bytes.

**Field and domains.**
* `F = F_p` (BabyBear), `K = F_p^8` (R5).
* Tables `t` have heights `T_t = 2^{h_t}`, with `h_t ≤ maxLog_t ≤ 22`.
* `D_t` is the LDE coset of size `16·T_t`. The largest LDE domain is `D₀` (≤ 2^26).
* Challenge decoding: `decodeChal(y)` reads 8 big-endian u32 limbs, each reduced mod `p`. At most 3^8 hash preimages map to any element of `K` (lemma L1.6).

**Hashing and commitments.**
* `WH(tag, m) := H(tag‖0x01‖m) ‖ H(tag‖0x02‖m)`, 64 bytes.
* MMCS: one binary Merkle tree per commitment round, over all tables. Leaf `i` of the largest domain holds the rows of the largest tables at `i`. At the level whose width matches a smaller table's LDE size, that table's rows are folded in: `node = WH(NODE, ℓ ‖ left ‖ right ‖ WH(LEAF, rows))`. This is Plonky3's MMCS idea with wide digests.
* Openings use a sorted, deduplicated multiproof.

**Transcript.**
* `d₀ = WH(INIT, protocolId ‖ pubDigest ‖ cb)`, where `cb` is the full claim bytes.
* Absorbing a message: `d_{i+1} = WH(ABS, d_i ‖ msg)`.
* Round challenge: `c_i = decodeChal(H(CHAL ‖ d_i))`.
* Query chunks: `H(QUERY ‖ d_fin ‖ j)` for `j < 24`; each answer yields 9 positions of 26 bits, reduced mod the domain size.

**Rounds.**
1. Absorb the commitment to the main traces (all tables).
2. Challenges `α_fp`, then `γ_mul`, each in its own round. The prover commits to the aux columns, which hold the running numerator and denominator products per bus.
3. Challenge `α_c` (constraint combination). The prover commits to the quotient chunks.
4. Challenge `z` (OOD, decoded into `K \ F_p`). The prover sends `v_c(z)` and `v_c(g_t z)` for every column, and `Q_j(z)`. The verifier checks the ALI identity at `z`: `C_{α_c}(v) = Z_{H_t}(z)·Σ_j z^{jT} Q_j(z)` for each table, together with the final bus product equalities.
5. DEEP functions `q_{c,ζ} = (f_c − v_{c,ζ})/(x − ζ)`, batched per height class by `⌈log₂ m⌉` **line rounds** (multilinear coefficients).
6. FRI over `D₀`. Binary folds `f ← f_e + β·f_o`; every third layer is committed (arity 8). Roll-in `f ← f + γ·G_t` when the domain reaches table class `t`. The final polynomial (degree < 2) is sent in the clear.
7. Query phase: 216 positions. For each one, check the MMCS openings, the DEEP values, every fold and roll-in, and the final polynomial.

**Proof format.** Fixed-shape, little-endian, with the heights in a header. The verifier rejects anything over 8 MiB before parsing, any height above its cap, and any trailing bytes. This bounds the verifier's query count, as `romSound_of_potential` requires.

**Completeness for every `H`.** Every step above is total and correct for arbitrary challenges (R3, R4). FRI on an honest low-degree function never fails, whatever the `β`s are.

## 5. Arithmetization (decision B)

### 5.1 Lean AIR DSL (lane L4)

```lean
namespace ZkFormal.Air
inductive Expr where
  | const (c : Nat) | col (col : Nat) (next : Bool) | pub (i : Nat)
  | isFirst | isLast | isTransition
  | add (a b : Expr) | mul (a b : Expr) | neg (a : Expr)
structure Interaction where (bus : Nat) (mult : Expr) (msg : List Expr) (send : Bool)
structure Table where (width : Nat) (constraints : List Expr) (interactions : List Interaction) (maxLog : Nat)
structure Air where (tables : List Table) (numBuses : Nat) (numPub : Nat)
structure Trace where (log : Nat → Nat) (cell : Nat → Nat → Nat → Fp)   -- table, row, column
def Expr.eval : Expr → Trace → (t r : Nat) → (pub : List Fp) → Fp
/-- Semantic predicate (no challenges): local constraints on every row, plus multiset balance
of every bus with multiplicities read as naturals (< 2^25). -/
def Holds (A : Air) (pub : List Fp) (tr : Trace) : Prop
def export : Air → String   -- JSON consumed by the Rust prover (interpreter or code generator)
```

The backend in the admission statement is
`bk := ⟨Air.Trace, fun c tr => Air.Holds nearAir (publicOf c) tr⟩`, with
`publicOf c = (encodeClaim c).map (·.toNat)`. Constraint generators are
structured Lean functions (families indexed by round or byte), so each family
is proved once instead of once per constraint. That avoids openvm-fv's 772
per-constraint `rfl` lemmas.

**Rust consistency.** The Rust prover evaluates constraints from `export nearAir`, either by interpretation or by generated code compiled into the prover. Three tests back this: honest proofs must be accepted by the compiled Lean verifier; each trace cell is mutated singly (the Plonky3 example already did 422k such mutants); and constraint polynomials from Lean and from Rust are compared at random points. None of this is part of soundness.

### 5.2 Tables and the width budget

Proof size is about `216 × (4·W_eq + paths)`, where `W_eq` is the number of base columns plus 8 × the number of extension columns, summed over all tables. **The budget is `W_eq ≤ 3000`.** The Plonky3 example has 14.6k: SHA alone has 7,803 columns, and LogUp aux adds 475 extension columns.

* **SHA-256: an OpenVM-style block hasher.** 16 rows of 4 rounds each, plus a digest row, so 17 rows per block and roughly 400–600 columns (that chip's layout). Message bytes go out on a `bytes` bus, block chaining on a `chain` bus, and digests on a `digest` bus. Padding is checked locally. Worst case: ≈105k blocks × 17 rows = 1.8M rows < 2^22.
* **NEAR tables.** These keep the decomposition already tested in the Plonky3 example (`rcpt`, `mrk`, `sort`, `acct`, `node`, `path`, `byte`, `r12`), with these changes:
  * multi-row layouts for `node` and `rcpt`, which today use 1,381 and 1,084 columns at one row per item;
  * grand-product aux columns that pack about 4 interactions each.

  Lane L6 owns the budget split, and the lane should reach `W_eq ≤ 3000` before writing any proofs.

### 5.3 Semantic proofs

* **SHA-256 (L5).**
  * Soundness, per row family: AIR row constraints imply `ArenaCore.SHA256.compress` on the block.
  * The chain and digest bus contract: every `(msg, digest)` provided satisfies `digest = ArenaCore.sha256 msg`.
  * Completeness: the trace generated from any list of messages satisfies the constraints.
  * Template: openvm-fv `equiv_SHA256_COMPRESS` and `sha2_block_soundness`, about 19k LOC with Mathlib and `omega`-heavy. It assumes bus semantics, which we supply from `Holds`.
* **NEAR (L6).** Soundness: `Holds ⇒ ∃ w, NearRelation c w`, through a relational intermediate spec that mirrors `runBatch`/`applyReceipt`, the trie walks and the outcome Merkle tree. Reuse comes from reexec-npai and reexec-witness at the NEAR level: codec round trips, trie lemmas (`Trie/Arena`, `Walk`), and account decoding. The bytecode-specific invariants do not carry over. Completeness: `honestTrace c w` satisfies `Holds`, plus a bound on trace heights.

## 6. Soundness architecture (lanes L2 and L3)

### 6.1 From `RomSound` to two obligations: proved (PoC)

`ZkFormal.Game.romSound_of_potential` turns the judge's game into the two
obligations below. The prover and verifier are hash-query trees; adversary
`prove` queries are inlined (`simulate_inline`); budgets are composed
(`inline_queryBound`); and tape overflow is ruled out because
`tapeLen = qH + qP·NPu + NVu`.

1. A potential `Φ : Table → Nat` on the oracle log with
   `StepBound Φ w C`. That is, a fresh query of weight `w x ≤ 1` raises
   `E[Φ]` by at most `C·w x`.
2. A **deterministic** acceptance lemma about the verifier tree alone: if
   `V` accepts `cb ∉ L` with no overflow, the final log has `Φ ≥ M`.

The result is `RomSound S L V P pub qH qP tapeLen (Φ[] + C·(qH + qP·NPw + NVw)) M`.

### 6.2 The potential, as a sum of four proved patterns

| Event | Potential | Bound | PoC theorem |
|---|---|---|---|
| A commit-phase challenge un-dooms a doomed prefix (the prefix is extracted from the log *at query time*) | `badPot` | `B·q / 2^256` | `bad_query_bound` (generalizes `rom_guess_bound`, which is re-derived) |
| The query phase succeeds on a doomed prefix: all 24 chunks good, in any order, with goodness judged against the log at each chunk's time | `queryPot` | `q·∏g_j / 2^(256k)` | `product_step`, `query_phase_bound` |
| Wide-digest collision (Merkle nodes or transcript chain) | `pairPot` | `2·N·q / 2^512` | `pairPot_step`, `collision_bound` |
| Wide-digest *inversion* (a digest used in a query before it was produced) | `queryPot` with history-dependent targets | `≤ Q²·2^-512` | instance of `product_step` (L2) |

They combine with `StepBound.add` and `StepBound.smul`, using common scales.

### 6.3 What L2 still has to prove: the extraction lemma

**Riskiest single lemma.** Suppose the final log contains no event from the
table above, the verifier tree accepts `cb`, and the claim is false. Then
there is a contradiction.

The proof walks the transcript chain backwards from `d_fin` by inverse
lookups in the log; inverses are unique because there are no wide
collisions. It extracts every committed MMCS tree as a total function, from
the log *as it stood at the corresponding `CHAL` query*. That is well
defined because there are no inversions. It then shows that the extracted
oracles agree with the verifier's openings. Finally it applies the IOP facts
of §6.4 round by round. The first un-doomed step is a `bad_query` event; a
doomed final state with accepted queries is a `QuerySuccess` event.

```lean
-- L2 (shape is final; the names of the IOP types are fixed by L3/L4 in week 1)
theorem accept_imp_event (A : Air) (prm : Params) (s : LazyRO) (cb pb : Bytes) :
    let r := OracleComp.simulate hashImpl ((verifier A prm).tree pub cb pb) s
    r.2.overflow = false → r.1 = true → ¬ (bk A).InLang cb →
      BadHist (commitBad A prm) r.2.table ∨ QuerySuccess 24 queryEnc (queryGood A prm) r.2.table ∨
      WideCollision 2 whEnc r.2.table ∨ WideInversion r.2.table
theorem compile_romSound (A : Air) (prm : Params) (hI : Iop.RbrFacts A prm) :
    RomSound challengeSpec (bk A).InLang (verifier A prm).toVerifier (prover A prm).toProver pub
      (2 ^ 64) (2 ^ 40) (tapeLen prm) (num prm) (den prm)
```

### 6.4 IOP facts in the unique-decoding regime (L3): all elementary

**Strong line lemma.** Let `C` be a linear code of distance `d` and let `3e < d`. For all but `max(1, n)` challenges `z`: if `u₀ + z·u₁` agrees with some codeword `c` outside `e` positions, then there are codewords `v₀, v₁` with `(u₀, u₁) = (v₀, v₁)` on **every** position where `u₀ + z·u₁ = c`.

This is **proved** in `ZkFormal.LineLemma.strong_line`, for any `Lean.Grind.Field`, without Mathlib (§10). The target radius `2e < d` replaces the `3e < d` step with the Berlekamp–Welch correlated-agreement theorem (port of ArkLib's `RS_correlatedAgreement_affineLines_uniqueDecodingRegime`, 2.2k LOC with Mathlib); the containment step is unchanged. Symbols may be vectors, so interleaved codes, which batching needs, are covered by the same proof (generalize `K` to `Fin m → K`).

**FRI query-phase argument (UDR, no weights).** Let `P_i ⊆ D_i` be the points from which all checks at layers ≥ i pass, and `Q_{i+1} ⊆ D_{i+1}` the points whose fold check passes and which lie in `P_{i+1}`. Then `P_i = sq⁻¹(Q_{i+1})`, and the pass probability equals `dens(P₀) ≤ dens(Q_{i+1})` for every `i`. Work down from `f_r = p_r` on `P_r = D_r`: if `f_{i+1}` equals a codeword on `P_{i+1}`, then `fold(f_i)` equals that codeword on `Q_{i+1}`. The strong line lemma, with `β_i` outside its bad set (which depends only on `f_i`), gives codewords `v₀, v₁` that equal `f_e, f_o` on `Q_{i+1}`. Hence `f_i = v₀(x²) + x·v₁(x²)` on `P_i`. At layer 0 this makes `f₀` `e`-close, which contradicts doomedness. Roll-ins and virtual folds are additional lines in the same induction.

The doomed predicates per round are:

| Round | Doomed state | Escape probability |
|---|---|---|
| init | no trace satisfies `Holds` for `publicOf c` | — |
| `α_fp` | ¬CA, or local constraints fail, or the fingerprint multisets differ | `#msgs·width / |K|` |
| `γ_mul` | the grand products differ, or a local constraint fails | `#msgs / |K|` |
| `α_c` | `C_α(P)` is not divisible by `Z_H` | `#constraints / |K|` |
| `z` | `C_α(P)(z) ≠ Z_H(z)·Q(z)` | `deg / |K \ F_p|` |
| send `v` | some `v ≠ P(z)` (otherwise the verifier's ALI check fails) | 0 |
| batch | the batch has no CA. A wrong `v` makes `(f − v)/(x − z)` far: `n − 2e ≥ D` forces `P(z) = v`. | `n / |K|` per line |
| FRI | as above | `n / |K|` per fold or roll-in |
| query | `|P₀| ≤ n − e` | `((n−e)/n)^9` per chunk |

Every count is `≤ 2^36`, which is `commitBad` in `Params`.

```lean
-- L3 → L2 interface (draft to freeze in week 1)
structure Iop.RbrFacts (A : Air) (prm : Params) : Prop where
  init   : ∀ cb, ¬ (bk A).InLang cb → Doomed A prm (PT.init cb)
  prover : ∀ τ m, Doomed A prm τ → NextIsProver τ → Doomed A prm (τ.push m)
  chal   : ∀ τ, Doomed A prm τ → NextIsChal τ →
             count Fp8.all (fun c => ¬ Doomed A prm (τ.pushChal c)) ≤ 2 ^ 36
  query  : ∀ τ, Doomed A prm τ → AtQuery τ → count (List.range (domSize τ)) (Agree A prm τ) ≤ prm.n - prm.e
  local  : ∀ τ x, AtQuery τ → ChecksPass A prm τ x (trueOpenings τ x) → Agree A prm τ x
```

## 7. Verifier connection (decision C)

* **Route:** `verify_route = "native-lean"`, `.nativeTrusted binDigest toolchain Model.verifier`. The edge status is *trusted*, the same as the admitted reexec-witness. `Model.verifier := (verifier nearAir prm).toVerifier`, a `TreeVerifier` that is executable Lean using `Array`/`ByteArray` and `UInt32` field arithmetic. `FORMAL_IMPL_CONNECTION` then holds by `rfl`.
* **Fast hashing:**
  * Define `sha256Fast` (`UInt32`/`ByteArray`; prototype measured at 0.8 µs per block against 41 µs) and prove `ArenaCore.sha256 = sha256Fast` (est. 1–2k LOC).
  * Attach `@[csimp]` to that theorem and a twin for `Interp.deployedRO`. The kernel never sees `sha256Fast`, so the TCB is unchanged; the compiled binary runs about 50× faster.
  * **The formal-checker lane needs to confirm that candidate-side `csimp` is acceptable for the native-lean route**, or alternatively formal-core could ship the same lemma itself.
* **Prover side:**
  * A Rust prover (L8) emits the Lean proof format.
  * The Lean prover *model* `P : TreeProver` is a mathematical definition, never executed.
  * `ProverComplete` is proved for it (L7), and `VerifierComplete` follows by instantiating `H := sha256 ∘ (roTag ++ ·)`, which is definitionally `deployedRO`.
* **NPAI (`.interp`, checked):** a later upgrade. The verifier would be written in the NpaiIR with `ROHASH`; it needs about 20M fuel against a 2^30 cap. Proof cost is projected from reexec-npai at about 22k LOC per 3.8k instructions, so 30–50k LOC. Not on the critical path.

## 8. Parameters and estimates (decision D)

Rate 1/16. The largest LDE is `n ≤ 2^26` and the degree bound `D = n/16`. The final polynomial has degree < 2, so `e/n` is the same at every layer. Kernel-checked in `zk-formal/ZkFormal/Params.lean`:

| Set | Radius `e` | Queries | Bound (log₂) | Kernel theorem |
|---|---|---|---|---|
| **UDR2** (target; needs the BW port) | `(n−D)/2` | **216** (24×9) | ≤ −132 (≈ −133.1; 207 queries fail) | `udr2_ok`, `udr2_margin`, `udr2_207_fails` |
| UDR3 (fallback; lemma already proved) | `(n−D)/3` | 360 (40×9) | ≈ −130.6 (351 fail) | `udr3_ok`, `udr3_351_fails` |

The bound terms are:
* query phase: `(2^64 + 2^40·k + k)·((n−e)/n)^216`;
* commit phase: `(2^64 + 2^46)·2^36·3^8/2^256 ≈ 2^-143`;
* wide pairs: `8·2^140/2^512`.

Estimates use a proof-size model of 4·W_eq per leaf, deduplicated 64-byte paths across 3 trees, FRI arity 8, plus OOD values.

| Set, max LDE, W_eq | Proof | RO blocks per verify | Hash time at 41 µs (`ArenaCore`) | Hash time at ~1 µs (`csimp`) |
|---|---|---|---|---|
| UDR2, 2^21 (typical batch-256), 3000 | 3.8 MiB | 180k | 7.4 s | 0.2 s |
| UDR2, 2^26 (worst-case domain), 3000 | 4.5 MiB | 236k | **9.7 s** | 0.24 s |
| UDR3, 2^26, 3000 | 7.2 MiB | 379k | 15.5 s | 0.4 s |
| UDR3, 2^26, 2000 | 5.8 MiB | 335k | 13.7 s | 0.33 s |

Prove time is extrapolated from the Plonky3 example: 0.95 s at batch-256 with 10.8k columns × 2^12 rows. Our traces are narrower but taller (SHA ≈ 85k rows), with 16× blowup and wide-digest Merkle trees. The estimate is ~5–20 s per batch-256 request and < 3 GiB RAM, against caps of 600 s and 16 GiB. The worst-case domain (2^22 rows) is not in the workloads, and only the Lean model `P` must handle it.

## 9. Work breakdown (decision E): 8 lanes

LOC figures are for Mathlib-free Lean unless marked. Calibration: reexec-npai produced 25k LOC (data refinement) in about 6.6 agent-hours. Mathematical lanes are assumed to be 3–5× slower per line.

| Lane | Scope | Exact deliverables (Lean) | Depends on | LOC | Agent-days | Risk |
|---|---|---|---|---|---|---|
| **L1 Algebra** | BabyBear, `K` as a quadratic tower, `Lean.Grind.Field` instances, Fermat/Euler, primality by kernel trial division, two-adic generators, `Poly` (eval, add, mul, degree, root bound, Lagrange interpolation), RS codes as `LinCode`, `decodeChal` fibers | `p_prime`, `Fp.pow_card_sub_one`, `eleven_nonsquare`, `instance : Field Fp8`, `Fp8.all`/`mem_all`/`nodup`, `Poly.card_roots_le`, `RS.sep` (distance `n−D+1`), `decodeChal_count : count Fp8.all B ≤ b → count (range roRange) (B ∘ decodeChal ∘ answer) ≤ b·3^8`, `decodeOod_not_base` | – | 5–8k | 2–3 | low |
| **L2 FS/BCS** | owns `ZkFormal.{Potential, BadQuery, Product, Collision, Game}` (done); WH and MMCS encodings; extraction from the log; inversion potential; `accept_imp_event`; `compile_romSound`; budget algebra | §6.3 signatures | L1, L4 (types), L3 (`RbrFacts`) | 6–10k (1.4k done) | 4–7 | **highest** (novel; the mixed-height MMCS extraction is intricate) |
| **L3 IOP math (UDR)** | `strong_line` for interleaved codes (d/3 done for scalars; generalize); BW port for d/2; multilinear batching; FRI `P`-set argument with virtual folds and roll-ins; DEEP farness; ALI divisibility; grand-product multiset soundness (bivariate SZ via `K[α][X]` cancellation) | `Iop.RbrFacts nearAir prm` and its five fields (§6.4) | L1, L4 | 8–14k (0.2k done) | 4–7 | medium (d/2 BW port is the hard part; d/3 fallback is in hand) |
| **L4 AIR DSL and protocol model** | `Air`, `Expr.eval`, `Holds`, `export`; the abstract IOP (`PT`, rounds); the executable `TreeVerifier` and its proof parser; `verifier A prm` refines the IOP verifier composed with BCS | `Air.*`; `verifier_eq_compile : (verifier A prm).tree pub cb pb = Bcs.compile (Iop.verifier A prm) cb pb`; `parse_total`; a query-count bound `NVu` | L1 | 5–8k + Rust export | 3–4 | medium |
| **L5 SHA-256 AIR** | block table, padding, chaining and digest bus contracts | `sha_block_sound`, `sha_bus_sound : Holds → ∀ (m,d) ∈ digests tr, d = ArenaCore.sha256 m`, `sha_complete` | L4 | 10–16k | 4–6 | medium (volume; template exists) |
| **L6 NEAR AIR** (may split into L6a trie/accounts and L6b receipts/outcomes/u128) | table re-layout to `W_eq ≤ 3000`; relational spec; soundness and completeness; height bounds | `nearAir_sound : ∀ c tr, Holds nearAir (publicOf c) tr → ∃ w, NearRelation c.1 w`; `nearAir_complete : ∀ c w, NearRelation c.1 w → Holds nearAir (publicOf c) (honestTrace c w)`; `honestTrace_fits : … → log t ≤ maxLog t` | L4, L5 (bus contract) | 25–40k | 8–14 | medium-high (volume, elaboration time) |
| **L7 Completeness and assembly** | Lean prover model `P` (interpolation-based LDE, MMCS, FRI); `ProverComplete` for every `H`; proof-size bound at the maximum heights; `sha256Fast` with the `@[csimp]` equality; `public.bin`; `Candidate.certificate : Judge.Expected` | `proverComplete : ProverComplete challengeSpec V P pub (2^23)`, `verifierComplete`, `certificate` | all | 6–10k | 4–6 | medium |
| **L8 Rust prover and conformance** (Rust) | `np-udr-stark` crate on p3-baby-bear, field, dft and matrix; codegen from `export nearAir`; MMCS/WH; transcript; FRI; serializer; differential tests against the compiled Lean verifier; mutants; benchmarks | `out/prove`; conformance, adversarial and resource-limit gates | L4 (format, AIR JSON) | 8–12k Rust | 4–6 | low-medium |

**Critical paths.**
* Risk: `L1 (field, poly) → L3 RbrFacts ∥ L2 accept_imp_event → L2 compile_romSound → L7 certificate`.
* Volume: `L4 → L6 → L7` (L6 is the longest lane).
* Recommended staging is **M2, a "toy admission"**: the complete `AdmissionStatement` for a small ROM toy `ChallengeSpec` (for example, a SHA-256 preimage relation using only the L5 table), running end to end through L1–L4, L7 and L8. That validates the whole cryptographic pipeline before L6 lands.

| Milestone | Content | When |
|---|---|---|
| M0 | PoC toolkit (this commit) | done |
| M1 | interfaces frozen: `Air`, `PT`/`RbrFacts`, proof format; Rust skeleton round-trips with the Lean verifier on a toy AIR | week 1 |
| M2 | toy admission (full gates on a toy challenge) | week 3–4 |
| M3 | SHA-256 AIR proved | week 3–4 |
| M4 | NEAR AIR proved; `W_eq` and size gates green | week 5–7 |
| M5 | admission on `chl_3be9…` | week 6–8 |
| M6 | (optional) NPAI route, edge status *checked* | later |

**Total:** 70–105k Lean LOC plus 8–12k Rust, about **35–60 agent-days**, or **6–8 weeks wall-clock with 8 parallel lanes**. The uncertainty is dominated by L6's volume and by the elaboration budget.

## 10. Proofs of concept (built now)

`zk-formal/` (Lake package `ZkFormal`, `require ArenaCore` from `../formal-core`, Lean v4.34.1). Every theorem below is sorry-free, with axioms ⊆ {propext, Classical.choice, Quot.sound}; the `Params` theorems use no axioms at all. Each module elaborates in 0.2–0.45 s.

| File | Main theorems | What it establishes |
|---|---|---|
| `Potential.lean` | `potential_simulate`, `prLE_of_potential`, `StepBound.add`, `StepBound.smul` | The lazy-RO supermartingale lemma for ArenaCore's `LazyRO`/`OracleComp` with weighted budgets. Exhausting the tape is harmless. |
| `BadQuery.lean` | `bad_query_bound`, `rom_guess_bound'` | Adaptive, history-dependent bad-answer bound: every commit-phase RBR round. Re-derives formal-core's `rom_guess_bound`. |
| `Product.lean` | `product_step`, `query_phase_bound` | Multi-answer events in any order, with goodness evaluated against the log at answer time: the FRI query phase and digest inversion. |
| `Collision.lean` | `pairPot_step`, `collision_bound` | Binding of wide (2×256-bit) digests: `Pr ≤ 2Nq/2^512`. |
| `Game.lean` | `simulate_inline`, `inline_queryBound`, `romWins_iff`, **`romSound_of_potential`** | ArenaCore's actual `RomSound` (with the `prove` oracle and the verifier continuing the oracle state) reduces to a potential plus a deterministic acceptance lemma, for tree-defined `P` and `V`. |
| `LineLemma.lean` | **`strong_line`** | The elementary strong line lemma (d/3) for any linear code over any `Lean.Grind.Field`, without Mathlib: the IOP-side core. |
| `Params.lean` | `udr2_ok`, `udr2_margin`, `udr2_207_fails`, `udr3_ok`, `udr3_351_fails` | The 128-bit budget as kernel `Nat` arithmetic on numbers of ~10^4 bits (`decide +kernel`). |

### 10.3 Measurements and experiments

All of these were run on this host.
* `ArenaCore.sha256` compiled: 41 µs per block (200 × 65-block messages).
* Plain-Lean `UInt32`/`ByteArray` SHA-256: 0.8 µs per block; output equal to `ArenaCore.sha256` on a 4 KiB vector.
* A downstream `@[csimp] theorem : @ArenaCore.sha256 = @alt` redirects compiled call sites: the generated `Main.c` calls `alt`. The replacement must be `@[noinline]`, otherwise inlining undoes the redirect.
* `grind` proves the field identities used by the line lemma over the abstract `Lean.Grind.Field`.

## 11. What could make full admission infeasible, and mitigations

1. **Elaboration budget (1800 s total).** 70–105k LOC at reexec-npai's rate (about 12 s per kLOC) comes to ≈850–1300 s, which is tight. Mitigations:
   * proof engineering: structured constraint families, avoid giant `simp` sets, cache by module;
   * ask governance for a larger `elaboration_budget` for this challenge class.

   The recheck time (1200 s per checker) is likely fine at ≈4× reexec-npai.
2. **Verify-time cap on the native route without fast SHA.** The UDR2 worst case alone is ≈9.7 s of hashing. If candidate `csimp` is not accepted and formal-core does not ship it, we need the NPAI route (large extra proof cost) or a narrower AIR together with a smaller worst-case LDE.
3. **Porting d/2 (Berlekamp–Welch) without Mathlib** needs some linear algebra over `K[Z]`. If it stalls, use UDR3: 360 queries. That is 7.2 MiB in the worst case at `W_eq = 3000`, too tight against 8 MiB, so the target becomes `W_eq ≲ 2200` (≈6 MiB), and the fast SHA becomes mandatory.
4. **Width budget.** If the NEAR tables cannot be brought to `W_eq ≤ 3000`, proof size grows linearly; at 5000 the UDR2 worst case is ≈6.3 MiB, still under the cap. The real limit is about `W_eq ≈ 7000` for UDR2.
5. **Worst-case witness bound (R7).** We need a Lean proof that every `NearRelation` witness yields ≤ 2^22 rows per table, for example ≤ 246k SHA-256 blocks. The estimated worst case is 105k, so there is a 2.3× margin, but the bound must be *proved* from `revealedBytes ≤ 3,000,000` and `n ≤ 256`.
6. **Extraction for mixed-height MMCS (L2).** This is subtle. Fallback: one MMCS tree per height class, at the cost of more paths per query (+15–30% proof size).
7. **Governance assumptions**, all already used by admitted candidates:
   * the native-lean edge stays *trusted* and is acceptable for admission (reexec-witness was admitted on it);
   * `decide +kernel` is allowed (reexec-npai);
   * the `sha256_rom` model treats `H = sha256("NPAI-RO-v1" ‖ ·)` as a random oracle *including* its use for Merkle hashing. This is what the profile authorizes, and it is the only way Merkle binding can be argued in the ROM branch, because `CryptoSound`'s ROM branch carries no collision-resistance hypothesis.

Nothing found so far makes admission impossible in principle. The two arena-side items to settle early are (2), whether `csimp` is acceptable, and (1), the elaboration budget.
