# End-to-end soundness of the PQ recursive SWIRL stack

> **2026-10-21 audit correction.** The previous family proof in §6.4 used an
> invalid `wide-bad` predicate that included ordinary transcript edges. Its
> advertised constants and unconditional family theorem are withdrawn. §6.4 now
> states the valid conditional operator bound and enumerates the missing
> instantiation. The numerical evaluations elsewhere are historical calculations,
> not established security guarantees. The Mathlib companion proves components;
> its corrected capstone does not close the protocol-specific premises. The
> DKT-to-WHIR list-regime transfer remains open (see the paper §6.1).


Lane `lane/pq-final-soundness`, 2026-10-18. Research and proof only; no backend change.
Companion files: `calc/bound.py` (every number below; output in `calc/bound.out`) and
`GAPS.md` (status of every step, and every code-vs-proof mismatch).

**Proximity basis U-13 (2026-10-18; MCA-UPGRADE.md):** §4 uses DKT26 (ePrint 2026/2056; Lean
proofs in github.com/quangvdao/ArkLib @ a5aa2677, verified on `lane/pq-dkt-verify` @ d9dc1c0e3,
DKT-VERIFY.md) instead of BCGM Thm 9.2 at m = 3: Thm 5.12 line MCA at the Johnson radius
(O-1) and first-order beyond-Johnson certificates (O-2). The superseded BCGM accounting is kept
in `calc/bound.py --bcgm`.

Contract: V3-D3A-STUDY §D, rows U-2 (proven bounds only), U-6 (failure ≤ 2⁻¹²⁸ against
≤ 2⁶⁴ quantum queries), U-7 (SHA-384 throughout), U-8, U-9, U-10 (42-B digests, z = 32,
WHIR-Y).

Tags used below:
* **[P]** proven in a cited published source, whose statement matches the use here.
* **[P′]** proven in a cited source that is a preprint or an unreviewed project note.
* **[T]** proven in this document. Complete as written, not yet reviewed.
* **[A]** an explicit assumption. Not proven; stated exactly.
* **[C]** a fact about the code, with file:line.

Code citations refer to the only tree that contains every lever: **U** =
`/data/illia/nearproof-deps/pq-nv-soundness/stark-backend-unified/crates/stark-backend/src`
(pinned v2.0.1 d667af5 + base patch + `stark-backend-unified.patch` from
`lane/pq-recursion-sha384`, `native/recursion/patches/`), and **SHA** =
`/data/illia/nearproof-deps/pq-recursion/levers-check/src/native_sha384_levers_config.rs`
(the SHA-384 hasher/transcript; the in-circuit twin is `crates/recursion/src/sha384/config.rs`
in the NV workspace). The levers-only and x15-only trees lack WHIR-Y and must not be used.

---

## 0. Target and current status

The target is failure probability at most `2^-128` against at most `2^64`
quantum oracle queries for the pinned recursive verifier and base relation.
It is **not currently proved**, even for the non-recursive layer: the concrete
family-QROM instantiation (§6.4) and DKT-to-WHIR transfer remain open.

The repaired Lean capstone proves the conditional bound
`p ≤ (Ahat + sqrt(slack))²` from operator evolution, transition estimates,
measured-event inclusion and a square-root replacement premise. For a Boolean
potential this becomes `p ≤ (t*g + sqrt(slack))²`. Instantiating these premises
for the actual protocol is substantive remaining work; the old family constants
are withdrawn.

Recursive semantic soundness additionally requires NV-faithfulness,
Base-faithfulness, statement/level linkage and a coherent recursive hash model.
Adopting an assumption is not proving it. In particular, a runtime cap alone
does not identify in-circuit SHA-384 with an independent random oracle.

The historical parameter calculation in §9 is retained for reproducibility,
not as a security theorem. The later G2 implementation reports `T*` enabled;
the older source snapshots discussed below do not establish its correspondence
to the required long-output model. See the paper's Appendix C for completion
criteria, model choices and the order of work.

---

## 1. Setting

### 1.1 Fields and parameters
* p = 15·2²⁷ + 1 (BabyBear). F = Ext12 = F_p[X]/(X¹² − 31), |F| = p¹² = 2^370.88.
* Per-round target 268 bits, accounted as **236 query bits + z = 32 PoW bits**:
  `protocol_security_level = security_bits − query_phase_pow_bits` (U config.rs:416), and
  q_i = ⌈236 / (−log₂ a_i)⌉, where a_i = A_i/n_i is the agreement at which round i is analysed
  (U-13): a_i = √ρ_i(1 + 1/128) (backend ListDecoding m = 64; O-1, base layer) or the certified
  first-order A_i of `calc/dkt_certs.json` (O-2, final and inner layers; per-round table bound
  into the vk). The O-1 rule is the existing config.rs:332-346, 405-457 formula with m = 64.
* ρ_i = 2^(−lir_i)/15 (×15 domains, config.rs:447-452). lir₀ = b and
  lir_{i+1} = lir_i + k_i (keep_domain). The first round folds k₁; the others fold k
  (config.rs:472-478).
* Shapes are those of the NV fixed point (`extrapolate_nv2.py`, 268/z = 32/42 B row):
  * final layer: b = 8, log h = 19, k₁ = 1, k = 3, final length 2⁹, W = 141, queries
    [38, 35, 29, 24] (U-13, O-2; were [42, 38, 31, 26] under BCGM m = 3);
  * inner layers: b = 6, k = 4, final length 2⁶, queries [45, 41, 31, 24] (were [50, 46, 33, 26]);
  * base (stress) layer: O-1, queries [48, 44, 32, 25].

  `bound.py` re-derives the schedules and asserts them.

### 1.2 The protocol
One SWIRL layer proves, for a multi-AIR verifying key vk with public values x:

> **R_vk(x; T):** T is a trace (one matrix per present AIR, height 2^{n_a}, rows at and
> beyond the tight height H_a equal to zero) such that
> (i) every AIR constraint polynomial vanishes on every row;
> (ii) every bus balances modulo p: for every message value v, the multiplicities m with which
> v is sent and received satisfy Σ m ≡ 0 (mod p);
> (iii) the program/preprocessed columns equal the table fixed by vk (Lemma 3.6).

The verifier's transcript order is fixed in §6.4 (it was audited line by line against U).
The sub-protocols are:
* the preamble;
* LogUp with a fractional-sum GKR (Gruen rounds, derived claims);
* the batch-constraint zerocheck with univariate skip (Gruen rounds);
* the stacking reduction (tight heights, rotation mask);
* WHIR (×15 domains, k₁, keep-domain, U-13 agreements, multiproof, coset leaves, WHIR-Y, grinding).

### 1.3 Hash, framing, oracles [C]
* Every hash is SHA-384. A framed hash is
  `H(tag, parts) = SHA-384(prefix32 ‖ tag_u8 ‖ Σ(le64(len) ‖ part))` (SHA:69-80), with
  prefix32 = `nearproof-sha384-ext12-v5-w42-c1` under the 42-B lever.
* Tags: 0 row leaf / vk pre-hash, 2 init, 3 flush, 4 commit, 5 squeeze, 6 coset leaf,
  7 PoW. The tag byte is at a fixed offset.
* A node is `SHA-384(np8 ‖ l₄₂ ‖ r₄₂)` truncated to 42 B (SHA:91-99). Under the lever,
  np8 = `NPQ5 ‖ 0x2a ‖ C ‖ ND`, not `NPQ4NODE` as the task text states; `NPQ4NODE` is the
  all-default prefix (SHA:35-37).
* Leaf digests and the vk pre-hash are also truncated to 42 B. The 48-byte transcript state
  is never truncated.

**Lemma 1.1 (oracle split) [T].** The framed inputs fall into three pairwise disjoint,
prefix-free sets:
* the **narrow-leaf** set N_L: tags 0 and 6;
* the **narrow-node** set N_N: node messages, all of length exactly 92 bytes;
* the **wide** set W: tags 2, 3, 4, 5, 7.

The framing is injective on each set. So, modelling SHA-384 as a random oracle H, the three
restrictions are independent random oracles: H restricted to N_L and N_N truncated to
336 bits, and H restricted to W at 384 bits.

*Proof.* Node messages start with byte `N` (0x4E); framed messages start with `n` (0x6E). Inside
the framed sets the tag byte at offset 32 separates leaf from transcript tags. The
length-prefixed parts make the encoding injective, and node messages have a fixed length.
Restrictions of a random function to disjoint domains are independent. A truncation of a
uniform function is uniform. ∎

Modelling the full SHA-384 (Merkle–Damgård, any message length) as one random oracle is the
standard ROM idealisation and is part of U-6/U-7. It is not an extra assumption of this note.
The *in-circuit* SHA-384 is a different matter (§8).

---

## 2. Round-by-round knowledge soundness: definitions

An IOP verifier move samples a challenge c. A prover move sends a message a, possibly an
oracle.

**Definition 2.1 (rbr-KS, doom form).** An IOP for relation R has round-by-round knowledge
error ε if there are a state function S(x, τ) ∈ {0,1} on partial transcripts and an extractor
E with:
* (K1) S(x, ∅) = 0 for every x.
* (K2) **Prover moves:** if S(x, τ) = 0 and S(x, τ‖a) = 1, then E(x, τ‖a) ∈ R(x).
* (K3) **Verifier moves:** if S(x, τ) = 0, then Pr_c[S(x, τ‖c) = 1] ≤ ε.
* (K4) **Acceptance:** if V accepts the complete transcript τ, then S(x, τ) = 1.

Consequence. For any accepting τ, look at the first prefix where S becomes 1. Either it
follows a verifier move (a "lucky challenge"), or it follows a prover move and E succeeds on
that prefix. Definition 2.1 implies CMS19's rbr knowledge soundness. It is the shape that
Theorem 6.4 consumes. An existential extractor can suffice for a query-only
relation-soundness statement. The computational peeling reduction in §7.3
requires a concrete bound on database readout and the actual list decoder;
existence or asymptotic polynomiality alone does not supply that bound.

**Definition 2.2 (list states).** Let F = (F₁..F_W) be the stacked round-0 oracle, a word of
the interleaved code RS^W[F, L₀, 2^{log h}]. Let δ₀ := 1 − a₀ (§1.1, U-13) and
Λ₀ := Λ^W(F, δ₀), the codewords within relative distance δ₀. By the list bound of §4 (DKT26
eq. (67) pairwise term for O-1, Lemma 5.11 / Cor 7.5 certificate for O-2; both width-free),

  |Λ₀| ≤ ℓ₀ (2¹⁰·⁹ … 2⁴⁰·⁰ at the §1.1 shapes; `calc/bound.out`).

For c ∈ Λ₀, write unstack(c) for the trace that c encodes. This is a deterministic map,
given the layout (Lemma 3.7).

**Lemma 2.3 (rbr soundness in list form ⇒ rbr-KS) [T].** Suppose the IOP's verifier moves
after the round-0 commitment admit a soundness state function of list form:

  S_snd(τ) = 1 ⟺ ∃ c ∈ Λ₀ : Claims_τ(c),

where Claims_τ(c) is a predicate in c and the non-oracle part of τ, and Claims at the
commitment is "unstack(c) ∈ R(x)". Later rounds may add conjunctions about later oracles,
which is the WHIR form of §4. Prover moves after the commitment never turn S_snd from 0 to 1,
and each verifier move turns it from 0 to 1 with probability at most ε. Then the IOP has
rbr-KS error ε, with E(x, τ) := "list-decode F; return unstack(c) for the first c ∈ Λ₀ with
unstack(c) ∈ R(x)".

*Proof.*
* Set S(∅) = 0 and, from the commitment on, S := S_snd. (K1) holds.
* At the commitment prover move, S flips to 1 iff some c ∈ Λ₀ has unstack(c) ∈ R(x). Then E
  succeeds, which is (K2). Later prover moves never flip S.
* (K3) is the hypothesis.
* (K4): acceptance satisfies every claim, by the definition of the states (checked per
  sub-protocol in §3–§4). ∎

**Lemma 2.4 (union over the list) [T; = HROB Lemma 4.7 at m = 0].** Suppose a verifier move
satisfies, for each fixed c, Pr_ch[¬Claims_τ(c) ∧ Claims_{τ‖ch}(c)] ≤ ε_P. Then the move's
list-form error is at most ℓ₀·ε_P.

*Proof.* Λ₀ is fixed by the commitment, before the move. Take a union bound. ∎

Every PIOP move (§3) precedes WHIR's first OOD sample. So its error is ℓ₀ times its usual
per-candidate error (ℓ₀ = 2^13.5 for the final layer). With several round-0 commitments
(app layers) the factor is the product of the lists; `bound.py` uses `commits = 2` for the
app stress shape.

**Lemma 2.5 (message restriction and derived messages) [T].**
* (a) If a protocol V′ accepts a subset of the prover messages that V accepts, and is
  otherwise identical, then any state function for V is one for V′, with the same errors.
* (b) Suppose V′ omits a prover message a that V would check through an equation
  E(a, τ) = 0 with a unique solution a = g(τ). Suppose V′ computes a := g(τ), absorbs it
  exactly as V does, and rejects when g is undefined. Then accepting transcripts of V′ are in
  bijection with accepting transcripts of V (insert a = g(τ)), with identical FS inputs. So V′
  has V's state function and errors.

*Proof.* (a) Restricting the prover can only lower the probability of each transition. (b)
Bijection; V′ rejects only where V would also reject or g is undefined, which affects
completeness only. ∎

Lemma 2.5 covers:
* Gruen GKR rounds: s(X) = eq_pre·eq₁(ξ_t, X)·t(X) with s(0) = claim − s(1). These are
  restrictions to degree-3 polynomials with a known linear factor (U fractional_sumcheck_gkr.rs:224-247).
* Derived GKR claims p₁ and q₀ (gkr.rs:95-113, 150-160).
* Gruen zerocheck rounds: s(d+1) derived, last wire value forced to 0 and not absorbed
  (batch_constraints.rs:369-412).
* The next-row mask (Lemma 3.8).
* WHIR-Y absorbing derived values (Lemma 4.6).

The soundness of Gruen's tweak was stated only informally in Gruen (ePrint 2024/108, App. A.3,
"V can compute what P would have sent"). Lemma 2.5 is the rbr form of that remark.

---

## 3. The PIOP before WHIR

Throughout, c ranges over Λ₀, T_c = unstack(c), and errors are per candidate. Lemma 2.4
multiplies them by ℓ₀.

**Lemma 3.1 (LogUp: α, β) [T, standard; cf. Papini–Haböck ePrint 2023/1284, Prop. 2].**
* Setting: N_int is the total number of interactions, and messages are tuples of length
  ≤ ℓ_msg over F_p, fingerprinted as fp_β(v) = Σ_j β^j v_j (bus index included).
* Suppose T_c violates (ii). Then with probability ≥ 1 − (ℓ_msg·N_int²/2 + 2N_int)/|F| over
  (α, β), sampled consecutively with no prover message between them (one verifier move,
  batch_constraints.rs:270-271), the true fractional sum Σ m/(α − fp_β(v)) of T_c is not 0,
  or some denominator vanishes. The latter is a rejection.

*Proof.*
1. Distinct messages give distinct polynomials fp_·(v) of degree ≤ ℓ_msg. A union over the
   < N_int²/2 pairs bounds Pr_β[some collision] by ℓ_msg·N_int²/(2|F|).
2. Without collisions, an unbalanced bus gives a non-zero rational function Σ_v M_v/(X − fp_β(v)).
   Here M_v ≢ 0 mod p for some v. It has ≤ N_int poles and ≤ N_int zeros.
3. Pr_α[α is a zero or a pole] ≤ 2N_int/|F|.

Condition (ii) is balance **mod p**. Whether mod-p balance means what an AIR intends (e.g.
boolean multiplicities, < p total uses) is part of NV-faithful/Base-faithful (Lemma 7.1(F4)),
not of this lemma. ∎

**Lemma 3.2 (fractional-sum GKR, with Gruen and derived claims) [T, standard].**
* Setting: L = l_skip + n_logup layers. Layer j runs j sumcheck rounds of degree 3, a batching
  challenge λ_j and a line reduction μ_j.
* Moves, in code order (gkr.rs:114-175): root claims observed, then μ₀; then per layer λ_j,
  then the rounds r_t after s(1), s(2) [, s(3)], then the layer claims observed, then μ_j.
* Errors per candidate: each sumcheck round ≤ 3/|F|; each λ_j ≤ 1/|F| (two claims combined
  linearly); each μ_j ≤ 1/|F| (two evaluation claims on a line, linear in μ).

*Proof.* State: "the current layer claims are the true layer values of T_c". These are the
usual sumcheck and batching arguments (Schwartz–Zippel in one variable). Gruen and derived
claims are covered by Lemma 2.5. ∎

**Lemma 3.3 (implicit zerocheck claims at the GKR point) [T].**
* The zerocheck point ξ is the GKR's final point, padded with fresh samples
  (batch_constraints.rs:305-307).
* Let Ẑ_c(Y, X) := Σ_{z∈D, x} L_z(Y)·eq(X, x)·C_c(z, x), where D is the univariate-skip
  subgroup (|D| = 2^{l_skip}) and C_c is the λ-free vector of constraint values of T_c.
* If T_c violates (i), Ẑ_c is a non-zero polynomial: degree < 2^{l_skip} in Y, multilinear in X.
* Add to Claims_τ(c) the conjunct "Ẑ_c with the already-fixed coordinates of ξ substituted is
  the zero polynomial".
* Then every move that fixes one coordinate of ξ adds ≤ (2^{l_skip} − 1)/|F| (the Y coordinate)
  or ≤ 1/|F| (an X coordinate) to that move's error.

*Proof.* The values {C_c(z, x)} are recovered from Ẑ_c by Lagrange and multilinear
interpolation, so Ẑ_c ≢ 0. Fixing variables one at a time: if P(fixed, rest) ≢ 0, then
substituting a uniform value for one more variable gives ≢ 0 except with probability
deg_var/|F|. The order in which coordinates are fixed does not matter. ∎

`bound.py` adds (3 + 2^{l_skip})/|F| to every GKR round move and (1 + 2^{l_skip})/|F| to
λ_j/μ_j. That is conservative.

**Lemma 3.4 (λ and μ batching) [T].** λ is sampled before the per-AIR claims (p_a, q_a) are
absorbed (batch_constraints.rs:311 vs 315-320). μ is sampled after them (329). The
combination is (204-210)

  evaluated = Σ_a μ^{2a}·num_a + μ^{2a+1}·den_a + Σ_a μ^{2N_air + a}·eq·Σ_j λ^j C_{a,j}.

* Errors: λ ≤ (n_constraints − 1)/|F|; μ ≤ (3N_air − 1)/|F|.
* **The order is sound.** The claims are chosen after λ, but λ enters only through
  Λ_a(c) := Σ_j λ^j Ẑ_{a,j,c}(ξ), which does not depend on the claims. The claimed-minus-true
  difference, as a polynomial in μ, is fixed before μ.

*Proof.*
* λ: if some Ẑ_{a,j,c}(ξ) ≠ 0, then Σ_j λ^j Ẑ_{a,j,c}(ξ) is a non-zero polynomial of degree
  ≤ n_constraints − 1 in λ.
* μ: the prover's claims (p_a, q_a) must pass the GKR-sum check (321-326). If the true per-AIR
  values of T_c differ from the GKR output, some claim is false. If some Λ_a(c) ≠ 0, a
  constraint term is non-zero.
* Either way the true batched sum minus the claimed batched sum is a non-zero polynomial in μ
  of degree ≤ 3N_air − 1, fixed before μ. ∎

**Lemma 3.5 (batch-constraint sumcheck with univariate skip) [T, standard].**
* The univariate round: s₀ has degree ≤ (d+1)(2^{l_skip} − 1), checked by
  Σ_{z∈D} s₀(z) = |D|·Σ_k coeff_{k|D|}, an identity for a multiplicative subgroup D
  (batch_constraints.rs:331-361).
* The n_max multilinear rounds have degree d + 1. Here d = max_constraint_degree = 21 (the
  k = 3 SHA AIR) and the eq factor adds 1.
* Errors: (d+1)(2^{l_skip} − 1)/|F| and (d+1)/|F|.
* The final check (batch_constraints.rs:211) compares the last claim with the constraint DAG
  evaluated on the absorbed column openings.
* After this lemma the claims about T_c are the column-opening claims {T̂_c,col(r),
  rot-T̂_c,col(r)}.

*Proof.* The standard sumcheck argument, per round. Gruen rounds are covered by Lemma 2.5. ∎

**Lemma 3.6 (program binding as an implicit claim) [T].** The NV program is ordinary main
columns (DESIGN §2.1). The native final verifier checks the final proof's program-column
openings against P̂_NV(r) (NV-faithful requires the same check in-circuit for the child).
Add "the program columns of T_c equal P" to R. If they differ, the multilinear difference is
non-zero, and the moves fixing r's coordinates carry the implicit claim "difference with fixed
coordinates substituted ≡ 0". As in Lemma 3.3, that costs ≤ 1/|F| per coordinate.

*Proof.* As Lemma 3.3. ∎

This is what makes the program part of the extracted relation, not merely a check on opened
values. Without it, a valid trace with a *different* program could pair with false program
openings.

**Lemma 3.7 (stacking reduction, tight heights) [T for the multilinear identities; see G-6].**
* The verifier samples λ_stack (stacked_reduction.rs:111), runs a univariate round
  (degree ≤ 2(2^{l_skip} − 1)) and n_stack rounds of degree 2. That reduces all opening claims
  to claims {Ĉ_w(u)} about the stacked columns, absorbed before WHIR.
* Errors: (#claims − 1)/|F| for λ_stack, 2(2^{l_skip} − 1)/|F|, and 2/|F| per round.
* Soundness requires the kernel identity below for every column v (length N = 2^n, real rows
  [0, H), zero beyond). Take H = Σ_i 2^{e_i}, descending, each e_i ≥ l_skip, with offsets
  o_i = Σ_{j<i} 2^{e_j}; each o_i is a multiple of 2^{e_i}.
  * (a) v̂(r) = Σ_i c_i·ĉh_i(r_{<e_i}), with c_i = eq(r_{≥e_i}, bits(o_i/2^{e_i})).
  * (b) With w(x) := v(x+1 mod N),
    ŵ(r) = Σ_i [ c_i·rot(ĉh_i)(r_{<e_i}) + ch_i(0)·( eq(r, o_i − 1 mod N) − c_i·Π_{t<e_i} r_t ) ].

*Proof.*
* (a) Alignment gives bits(o_i + y) = (y, bits(o_i/2^{e_i})), so eq(r, o_i + y) factors.
* (b) ŵ(r) = Σ_x eq(r, x − 1)·v(x). For x = o_i + y with y ≥ 1 the predecessor is inside the
  chunk and contributes c_i·eq(r_{<e_i}, y − 1). The chunk's own cyclic kernel would assign
  the y = 0 row the predecessor 2^{e_i} − 1, with weight c_i·eq(r_{<e_i}, 1^{e_i}) =
  c_i·Π r_t. The true predecessor of row o_i is row o_i − 1 mod N.
* Rows ≥ H contribute 0.
* The sumcheck errors are standard. ∎

(a) and (b) are exactly the code's `c_i` and `δ_i` (levers README "Mechanism";
stacked_pcs.rs:90-103, stacked_reduction.rs:220-236), written in the multilinear encoding.
The code uses the univariate-skip encoding (eq_D(ωr₀, ·) for the shift). Translating (b) into
that encoding was not re-derived line by line here (G-6). For a whole column, (c, δ) = (1, 0)
and (b) is the ordinary rotation kernel.

H is prover-chosen and absorbed (mod.rs:149-152). By (a) and (b), the statement proven is R
for the zero-padded trace, for every H. So tight heights cost nothing in soundness, provided
the AIRs are meant to accept zero rows: that is NV-faithful's (F5).

**Lemma 3.8 (next-row mask) [T].** The vk carries rot_mask (keygen/mod.rs:385-409;
types.rs:105-131). For unmasked columns the verifier sets claim_rot = 0 and still absorbs it
(batch_constraints.rs:104-105). The stacking reduction omits those claims.

If the mask contains every column that the constraint DAG reads at offset 1, the final DAG
evaluation never reads an unmasked rotated claim. So the protocol equals the unmasked protocol
restricted to claim_rot = 0 on those columns (Lemma 2.5(a)), followed by dropping claims that
nothing uses.

*Proof.* Immediate. The hypothesis holds because keygen computes the mask from the DAG. In
recursion the child's vk, mask included, is a constant of the parent program, so
NV-faithful(F2) covers it. ∎

---

## 4. WHIR (×15 domains, U-13 proximity inputs, k₁, keep-domain, WHIR-Y, grinding)

Notation as in WHIR (ePrint 2024/1586, Construction 5.1) with OpenVM round indexing:
* round i folds f_i k_i times;
* then it commits f_{i+1}, or sends the final polynomial;
* then the OOD sample z_{i+1,0} and answer;
* then the query PoW;
* then t_i shift queries;
* then the y_{i,·} are absorbed (WHIR-Y);
* then γ_i (U whir.rs:130-330).

n_i = |L_i| = 15·2^{log h + b} for every i (keep-domain). δ_i = 1 − a_i with a_i = A_i/n_i (§1.1).
C^(i,s) := RS[L_i^(2^s), m_i − s], s = 0..k_i. ℓ_i := max_s of the list bound of C^(i,s) at
agreement ⌈a_i·|L_i^(2^s)|⌉:
* O-1: the pairwise term ⌊n(A−D)/(A²−nD)⌋ of DKT26 Thm 5.12 eq. (67) [P, Lean
  `closePolynomialSet_finite_and_ncard_le_johnsonPairwise`] (the B_jet term is not used);
* O-2: the Lemma 5.11 bound of the certificate [P, Lean `finiteSquarefreeListBound_of_profile`;
  kernel-checked in lane/pq-dkt-verify `lean/DKTCerts.lean`].
Both hold at every interleaving width (DKT26 Lemma 7.4 / Cor 7.5).

**Status of the WHIR binding.** The RS-level statements above are Lean-proven. The step from
them to the WHIR round-by-round errors (Lemmas 4.2–4.7) is paper-level: WHIR Thm 5.2 as
corrected in Pus26 Thm 5.3. Pus26's hypotheses: char F ≠ 2; every C^(i,s) list-decodable at
δ_i (the ℓ_i above); MCA radius B⋆(C^(i,s), 2) ≥ ρ_i (holds: a_i > a₁(ρ_i) > ρ_i). Open item
GAPS S-28.

**Lemma 4.1 (WHIR on 15·2^K domains) [P′ x15-domains SOUNDNESS.md, checked here].** WHIR
Thm 5.2 and its lemmas hold verbatim for evaluation domains that are cosets of order c·2^K
(c odd, 2^{k_i} | |L_i|), with "smooth" replaced by "order c·2^K".

Of the domain properties, WHIR uses only:
* −x ∈ L;
* |L^{(2^j)}| = |L|/2^j;
* disjoint 2^k-fibres;
* power-of-two degree.

DKT26 Thm 5.12 and Prop 5.10 + Lemma 5.6 hold for any n distinct evaluation points. The
first-order ones need char > max(k−1, B∂): p = 2³⁰·⁹ > 2²¹ ≥ k and B∂ ≤ 52. The query terms need
exactly uniform indices. **[C]** The index sampler rejects x = p − 1 and returns x mod 15·2^j
(U traits.rs:62-71, odd_domain.rs:71-81). Since 15·2^j | p − 1, this is exactly uniform. The
circuit rejects the proof on p − 1 instead (NV verifier.rs:244-249): that changes completeness
by ≈ q/p and soundness not at all.

I re-checked the four uses (x15 SOUNDNESS.md table) against WHIR §4–5 and agree. The one
edit to WHIR Thm 5.2's hypothesis is the definitional one stated there.

**Lemma 4.2 (μ batching of the W stacked columns) [P DKT26 (Lean); P′ HROB Lemma 4.8 at m = 0].**
  ε_μ ≤ E_{W−1}/|F| + ℓ₀(W − 1)/|F|,
where E_{W−1} is the full agreement-set exceptional count of the powers curve of degree W − 1
at agreement a₀: DKT26 Prop 5.10 + Lemma 5.6 / Cor 7.3 with the support certificate of
`calc/dkt_certs.json` (Lean: `CurveCertificate.exists_exceptional_exact_powerAgreement_squarefree_sharp_optimized`;
the three instances, W = 141, 141, 601, are kernel-checked in lane/pq-dkt-verify
`lean/DKTCerts.lean`). This is valid at any a₀ > a₁(ρ₀), so also at the O-1 radius used by the
base layer; O-1 as configured is therefore not purely Johnson-regime. Values: 2⁻²⁸²·¹ (final),
2⁻²⁸³·⁰ (inner), 2⁻²⁸⁷·⁵ (base, W = 601). The batched stacking claims
are linear in the codeword, so Λ₀'s claims become one constrained-RS claim.

**Lemma 4.3 (fold moves α_{i,s}) [P WHIR Thm 5.2 / Pus26 Thm 5.3 + DKT26 (Lean)].**
  ε_fold(i,s) ≤ max_{s′} E(C^(i,s′))/|F| + 3ℓ_i/|F|.
O-1: E = `johnsonE0`, the constant the Lean theorem `johnson_lineMCA_probability` proves (the
4Dμh form of DKT26 Thm 5.12 (68), ≥ the paper's Ψ_D form). O-2: E = the Lemma 5.6 count of the
certificate. The fold word is a line in the 2-interleaved code, so Cor 7.7 transfers E with no
width factor: Thm 5.12 → Cor 7.7/7.8 is proven in Lean in lane/pq-dkt-verify
`lean/DKTGlue.lean` (`johnson_levelWitness`, `johnson_tensorFold`, `o1_line_mcaError`); for O-2,
`uniformExactInterleavedPowerAgreement_of_scalar_arbitrary` applied to `DKTCerts.mca_i`.
The WHIR sumcheck polynomials have degree 2; using 3 is conservative.

**Lemma 4.4 (OOD) [P WHIR Thm 5.2, ε^out].** ε_out(i) ≤ ℓ_i²/2 · (2^{m_i}/|F|)^{u_i}, where
m_i is the variable count of f_i and u_i the number of OOD samples; u_i = 1 suffices at every
shape here (worst 2⁻²⁷¹·⁹, final r1, with ℓ = 2⁴¹·⁰).

**Lemma 4.5 (shift queries) [P WHIR Thm 5.2, ε^shift and ε^fin; Lemma 4.1].** Without
grinding,
  Pr[query move flips S] ≤ (1 − δ_i)^{t_i} = a_i^{t_i}.
At m = 0 the candidate set Y has |Y| ≤ 1 after the OOD sample (HROB §4.3 variant L at m = 0).
In the final round Y ⊆ {p}. With grinding see Lemma 5.1.

**Lemma 4.6 (γ combination, WHIR-Y) [P WHIR Thm 5.2; P′ HROB §4.4 at m = 0].**
  ε_γ(i) ≤ ℓ_{i+1}(t_i + 1)/|F|; in the final round (t + 1)/|F|.

**[C]** WHIR-Y is implemented in U: whir.rs:315-320 absorbs every y_{i,j} before γ
(whir.rs:326), including the final round. The prover mirrors it (prover/whir.rs:368-377) and so
does the circuit (NV verifier.rs:1389-1392).

*Role of WHIR-Y at 42-B digests.* Under Theorem 6.4 (no tolerated collision, K = 0) every
opened leaf equals the canonically extracted oracle, so the y_{i,j} are functions of the
committed oracle. Absorbing them is Lemma 2.5(b) applied to values the verifier can derive,
and WHIR Thm 5.2 applies with or without WHIR-Y. WHIR-Y is **necessary** only for digests
< 256 bits: HROB Prop. 2.1 gives a ≈ t²/2ⁿ attack without it. At 336 bits it is harmless and
keeps the narrower-digest route open.

**Lemma 4.7 (WHIR rbr in list form) [P WHIR Thm 5.2 with Lemma 4.1].** The WHIR state
function (HROB §3 table at m = 0: Ent_i, Fold_{i,s}, OOD_{i+1}, Qry_i) is of the list form
required by Lemma 2.3. Every state is "∃ codeword in a list of the current oracle satisfying
the current constraints". Prover moves set S(τ‖a) := S(τ). The moves' errors are Lemmas 4.2–4.6.
(K4) holds: acceptance means all sumcheck and point checks pass and the final constraint holds
(whir.rs:341-399).

**Multiproof and coset leaves.** These are encoding choices.
* A leaf is the whole fold coset as one tag-6 message (SHA:100-107). So the IOP alphabet is
  "one fibre", which WHIR already reads as a unit.
* Multiproof acceptance implies per-leaf path acceptance (Lemma 6.2).

---

## 5. One layer: round-by-round knowledge error

**Lemma 5.1 (grinding inside one call) [T].** Under T\* (§6.2), the query move's challenge
is one random-oracle output c = (c_pow, c_idx), with disjoint bits. The verifier rejects
unless the z bits c_pow are zero. For a prefix with S = 0,

  Pr_c[S(τ‖c) = 1] ≤ Pr[c_pow = 0]·Pr[c_idx makes all queries land in the agreement set]
  = 2^{−z}·(1 − δ_i)^{t_i}.

*Proof.* The PoW bits and the index words are disjoint, uniform, independent bits of one
output. The rejection-sampled words give i.i.d. uniform F_p values: a word is accepted iff
< 2p, and the value is n mod p, which is exact (SHA:160-171). Lemma 4.1's sampler then gives
uniform indices. Lemma 4.5 bounds the second factor for every fixed c_pow = 0. ∎

*What this does and does not say.* The z PoW bits multiply the move's rbr error by 2⁻ᶻ.
Theorem 6.4 then charges t² against the product. So the per-round requirement is
2^{−z}·(1−δ)^t ≤ 2⁻²⁶⁸, i.e. 236 query bits with z = 32. This is the code's accounting
(config.rs:416). In the QROM this is Grover-tight: finding a c with a density-2^{−z}ε property
costs Θ(√(2^z/ε)) queries.

It does **not** hold for the code as written. There the PoW bits are bits of the absorb output
s′ = H(7, σ‖w) and the indices come from later calls H(5, s′), H(5, H(5, s′)), … (SHA:142-186).
The flip then happens at a later oracle point, conditioned on an already-good s′, and the
QROM technique (§6.5) cannot combine the two densities. Pure grinding in isolation is bounded
by DFMS22 Prop. 3.5 (Pr ≤ 152(q+1)²·2^{−z}) [P], but that bound does not compose with the query
move.

**Theorem 5.2 (rbr-KS of one SWIRL layer) [T, assembling §2–§5].** Under T\*, one SWIRL layer
(all levers) has rbr knowledge error

  ε_rbr = max over moves of {
    ℓ₀·(ℓ_msg·N_int²/2 + 2N_int)/|F|,
    ℓ₀·(3 + 2^{l_skip})/|F|,
    ℓ₀·(n_constraints − 1)/|F|,
    ℓ₀·(3N_air − 1)/|F|,
    ℓ₀·(d + 1)(2^{l_skip} − 1)/|F|,
    ℓ₀·(2·#cols − 1)/|F|,
    ε_μ (Lemma 4.2),
    ε_fold(i,s), ε_out(i), ε_γ(i) (Lemmas 4.3, 4.4, 4.6),
    2^{−z}(1 − δ_i)^{t_i} (Lemma 5.1)
  }

for relation R_vk (§1.2, including Lemma 3.6).

*Proof.* Lemmas 2.3 and 2.4 with §3, §4 and Lemma 5.1. The preamble has no verifier move
before the commitment, and the statement (vk pre-hash, commitments, heights, public values)
is absorbed before the first challenge (mod.rs:129-164). ∎

**Numbers** (`calc/bound.py`, shapes of §1.1):

| layer | worst move | 2nd | WHIR μ (W = 141) | PIOP worst | per-round query+z |
|---|---|---|---|---|---|
| final (O-2) | query r1: **2⁻²⁶⁸·⁰¹** | OOD r1: 2⁻²⁷¹·⁹ | 2⁻²⁸²·¹ | LogUp 2⁻²⁷⁹·² | 268.1 / 268.0 / 268.1 / 268.0 |
| inner NV (O-2) | query r2: **2⁻²⁶⁸·⁰²** | OOD r1: 2⁻²⁷⁴·³ | 2⁻²⁸³·⁰ | LogUp 2⁻²⁷⁹·⁶ | 268.0 / 268.1 / 268.0 / 268.0 |
| base (stress, W = 601; O-1) | query r3: 2⁻²⁶⁸·⁰⁶ | μ batching: 2⁻²⁸⁷·⁵ | 2⁻²⁸⁷·⁵ | LogUp 2⁻²⁹³·¹ | 269.2 / 271.5 / 270.2 / 268.1 |

**ε_rbr = 2⁻²⁶⁸·⁰¹** (U-13; 2⁻²⁶⁸·⁵⁵ under the superseded BCGM m = 3, `bound.py --bcgm`).
* The worst round is a WHIR query move: by design it sits at the 268-bit target, rounded up.
* Every fold MCA term is ≤ 2⁻²⁸⁰·⁷ (the BCGM-era binding term 2⁻²⁶⁹·⁶⁴ is gone); the binding
  non-query term is now OOD with one sample, 2⁻²⁷¹·⁹, driven by first-order lists up to 2⁴³·⁴.

---

## 6. Fiat–Shamir in the QROM

### 6.1 Oracle model
H is a quantum random oracle (Lemma 1.1). The adversary makes ≤ t superposition queries.
Analysis uses Zhandry's compressed oracle; notation as in weak-binding ANALYSIS.md §2–3
(database D, ⊥, Lemma 1 there).

### 6.2 The transcript T* (implemented schedule, incomplete proof correspondence)
The later G2 implementation uses counter-mode challenge words:
* **(T\*-1) Squeeze.** Let κ be the state right after the last absorb of a verifier move
  (flush H3, commit H4). Challenge blocks are B_j := H(5, κ‖le32(j)) for j = 1, 2, …,
  consumed with the existing rejection rule. When the next absorb happens, its input state is
  the last block consumed.
* **(T\*-2) PoW.** For a query move with witness w: B_j := H(7, σ‖w‖le32(j)), j ≥ 1, where σ
  is the state after flush. Accept iff the first z bits of B₁ are zero. Index words start
  after the PoW bits. The next state is the last block consumed.

The byte and compression costs must be taken from the pinned implementation;
they are not established by this schedule description. The historical source
snapshot used a sequential squeeze chain. The rebuilt G2 source uses
`ShaTranscript::sample` and `SqueezeSrc::block` in `sha384/config.rs` with T*
enabled. `observe_commit` flushes and hashes **one digest** per commit call.
Fixed VK roots must still be included in the extraction reference set.

**New implementation/proof mismatch (2026-10-21):** `sample` increments a `u32`
counter and loops until enough candidates are accepted. It does not reject at
`J = 2^20`. The finite-cap simulation below therefore does not yet apply to
this implementation. Circuit row limits might imply a bound for valid extracted
NV executions, but that implication and the native outer-verifier case require
proof. Do not silently use the hypothetical cap as an implementation fact.

### 6.3 Lemmas

**Lemma 6.1 (domain separation).** Lemma 1.1.

**Lemma 6.2 (multiproof ⇒ per-leaf paths) [T].** The multiproof verifier (whir.rs:470-515)
works as follows:
* it processes levels leaf → root over the known indices in ascending order;
* it pulls a sibling digest from the stream when the sibling is unknown;
* it requires the stream to be consumed and the root to match.

If it accepts, then for every queried leaf there is an authentication path whose every node
value the verifier computed as node_hash of its two children. So every evaluated point is a
(node input, output) pair that the verifier checks against H, exactly as with individual
paths. Duplicate indices must carry equal leaf digests, which the code checks.

*Proof.* Induction on the level: each known node is either a computed parent or a leaf, and
each parent's children are known or streamed. ∎

**Lemma 6.3 (finite counter-mode oracle simulation; protocol application open).** Let G(κ) := (H(5, κ‖1), …, H(5, κ‖J)). Its
components are independent random functions, so G is a random function with J·384-bit
output. Any t-query algorithm with oracle H can be simulated perfectly by a 2t-query algorithm
with oracle access to G (and to H on the other domains). The same holds for
(σ, w) ↦ (H(7, σ‖w‖j))_{j≤J}.

*Proof.* To answer a query |κ, j, y⟩: compute G(κ) into an ancilla, XOR component j into y,
and uncompute with a second query. This covers only queries whose counter
lies in `1..J`; the simulator also retains H on other domains. ∎

For a capped verifier, a move requiring `K` accepted 32-bit candidates can
exhaust `J` blocks without *all* candidates being rejected. For `N` available
candidate words, the classical fresh-prefix tail is
`Pr[Binomial(N, 2p/2^32) < K]`, where PoW-reserved words are removed from `N`.
The old `(1/16)^(12J)` expression was not this event. Applying a truncation
argument to adaptive quantum-selected keys additionally needs its own reduction
and loss. Neither an implemented cap nor that reduction is presently supplied.

### 6.4 Theorem: QROM straight-line knowledge soundness for families of layers

**Setting.** A finite family of IOPs {IOP_v} indexed by vk pre-hash v: all layers of the stack
and the base layer. Each has a state function S_v and extractor E_v as in Definition 2.1, with
errors ≤ ε. The BCS compilation uses T\*, 42-B Merkle trees and the framing of §1.3. A
transcript in D is a chain in D that starts at σ₀ = H(2) and alternates:
* absorb entries (σ, msg) ↦ κ, prover moves, where commitments are digests whose preimages
  are read from D;
* challenge entries κ ↦ G(κ) (or (σ, w) ↦ G₇(σ, w)), verifier moves.

Oracle strings are canonically extracted from D's narrow entries: unique preimage at each
reached node, default for unreached nodes.

**Theorem 6.4 (conditional operator bound; repaired).** Let `q` be the number
of queries in a specified simulated oracle model. Suppose a Boolean potential
`κ(D)` is zero initially, adversary evolution preserves its level projectors,
and every query, on the reachable support, satisfies

```
||Π_bad cO Π_good|| ≤ g.
```

Suppose failed extraction of an accepting proof gives a measured bad event of
probability `p' ≤ ||Π_bad ψ_q||²`, and the cited replacement step supplies
`sqrt(p) ≤ sqrt(p') + sqrt(ℓ_V / 2^336)`. Then

```
p ≤ (q*g + sqrt(ℓ_V / 2^336))².
```

*Proof.* Decompose each pre-query state into its good and bad projections.
Contraction preserves the old bad norm and the crossing contributes at most
`g` times the good norm, hence at most `g` for a normalized state. Iteration
from zero gives `||Π_bad ψ_q|| ≤ q*g`. Apply measured-event inclusion and the
square-root replacement inequality, then square nonnegative quantities. The
operator/path/probability composition is checked as
`Qrom.qrom_binary_bound`; a concrete database instantiation is not supplied. ∎

**Corrected candidate potential, not yet an established instantiation.** Use the
union of (a) narrow collisions, (b) collisions between *distinct* wide output
occurrences or an output equal to the initial state, and (c) a reachable parsed
transcript whose first state flip is at a verifier move. Normal output-to-input
edges are allowed. Never classify acceptance alone as bad: K1/K2/K4 imply a
safe accepting transcript has an extraction at a prover flip. The latter logical
step is checked in `Qrom.Transcript.first_flip_extract`.

The deleted proof incorrectly included every output-to-input equality in (b).
An honest pair `(σ,msg) -> κ`, `κ -> G(κ)` immediately contradicted its proposed
small probability. `Qrom.Transcript.honest_edge_not_bad` guards this distinction.

**What must be proved before substituting a numerical g:**

1. Bind the family index and public statement into canonical framing. Show each
   reachable state has a unique parsed prefix outside genuine output collisions;
   distinguish per-block outputs of a long-output challenge from logical moves.
2. Define canonical Merkle extraction, including missing nodes, and show how it
   changes when one database entry is inserted, removed, or reassigned. Count
   every root in an absorb message: `|Chg| ≤ 3q` does not follow from counting
   oracle entries when one message can contain multiple digests.
3. For the narrow query, bound the crossing block using the **disjoint** entry
   estimates. For absorb/challenge queries, treat matching an existing input as
   a *local extension possibility*, not a globally bad ordinary edge. Account
   for old downstream entries and changes to reachable transcript sets.
4. Account for long-output fanout. With J blocks per challenge there can be up to
   Jq state-output occurrences, and within-output collisions also need a count.
   The old `J(2q+1)/2^384` formula is not certified by the withdrawn argument.
5. Derive a uniform `g` for the entire family, including the base layer, prove
   measured-event inclusion, and justify replacement for the exact verifier's
   adaptive oracle accesses and mixed output widths.

The old substitution `g² = 10 max(3q/2^336, ε + J(2q+1)/2^384)` and the resulting
`2^-134.7` are **not established** until these obligations are discharged.
Counter-mode simulation by itself does not discharge them.

A successful instantiation would imply that, except on the bounded bad event,
**every reachable accepting transcript has a valid extraction**. It would not
imply the absence of honest accepting transcripts. Recursive use additionally
needs NV faithfulness and a coherent A-IC model; §7 is conditional on all of
these premises.

### 6.5 Transcript order vs code (which messages are absorbed before which challenges)
Audited against U, in execution order (file:line in `verifier/`):

| challenge | must be bound before it | absorbed in code before it? |
|---|---|---|
| α_logup, β_logup (batch_constraints.rs:270-271) | vk pre-hash, common-main commitment, per-AIR presence, heights, tight heights, cached commitments, public values (mod.rs:129-164) | **yes**. The logup PoW (265) has bits = 0 in the configs seen; an unabsorbed witness at bits = 0 is malleability only. |
| μ₀ (gkr.rs:134) | q0_claim and root (p0, q0, p1, q1), derived as in Lemma 2.5 (114-117) | yes |
| λ_j (141); r_t (228) | layer claims; s(1), s(2) [, s(3)] (224-226) | yes |
| μ_j (175) | layer claims, p₁ derived (156-162) | yes |
| ξ padding (305-307) | — | — |
| λ (311) | — (per-AIR claims may follow, Lemma 3.4) | sound as is |
| μ (329) | per-AIR (p_a, q_a) (315-320) | yes |
| r₀ (347); r (421) | univariate coefficients (342-344); round evaluations (383-389, Gruen value derived) | yes |
| λ_stack (stacked_reduction.rs:111) | column openings, masked rotated claims as zeros (batch_constraints.rs:101-121) | yes |
| u₀, u_j (146, 161-170) | stacking univariate coefficients and s_j(1), s_j(2) | yes |
| μ_whir (whir.rs:59) | stacking openings (stacked_reduction.rs:248); c (whir.rs:51) | yes |
| α_{i,s} (146) | ev1, ev2 (139-140) | yes |
| z_{i+1,0} (166) | commitment g_{i+1} (164) | yes |
| query indices (187-196) | OOD answer y₀ (171) or final polynomial (157-159); PoW witness (175-185) | yes, **but via a multi-call chain: G-1, G-2** |
| γ_i (326) | y_{i,·} under WHIR-Y (315-320) | yes (WHIR-Y on) |

**No missing absorption** was found. In particular:
* the statement is fully bound before the first challenge;
* every prover message that a later check uses is absorbed before the next challenge;
* the y_{i,·} are absorbed before γ_i in every round, including the final one.

The opened rows and Merkle siblings are never absorbed. That is the standard BCS pattern,
covered by the root binding of Theorem 6.4.

**Code-vs-proof mismatches** (details and ratings in GAPS.md):
* **G-1 (open).** Every verifier move's randomness is squeezed through a sequential chain
  σ_{j+1} = H(5, σ_j). Query moves need 4–7 blocks; an Ext12 sample needs a second block with
  probability ≈ 1 − (15/16)¹² ≈ 0.54.

  CMS19-type arguments, CDHZ and Theorem 6.4 all need the move's challenge to be one oracle
  output. With a chain, the flip happens at the last block, with the earlier blocks already
  fixed in D. The worst-case-over-D transition bound then degrades to ≈ ε^{1/k}.

  This is a proof gap, not an attack. A nested amplitude-amplification heuristic suggests the
  true loss is poly(k), but no theorem says so (Chiesa–Orrù ePrint 2025/536 is classical
  ideal-permutation only and lists the QROM case as open, §1.3). **Fix: T\*-1.**
* **G-2 (open).** The PoW bits are in the absorb output s′, and the query indices are in a
  separate later call. **Fix: T\*-2.** Without it, the provable per-round error is the
  ungrinded 2⁻²³⁶·⁵⁵, which gives 2⁻¹⁰⁵.
* Minor, not soundness bugs: G-9 (the tight-height None/Some ambiguity when common_main = 0),
  G-10 (`c` not in the pre-hash; the pre-hash not recomputed by the verifier), G-11 (PoW
  malleability at bits = 0), G-12 (the calculator ignores hash terms).

---

## 7. Recursive composition

### 7.1 Interfaces

**Lemma 7.1 (NV-faithful(i)) — required form [A here; to be proven by the circuit lane].**
For i = 1..d, let vk_i be NV_i's verifying key and P_i its program table: P_1 is the
app-verifier program, and P_i = P_NV for i ≥ 2. Let T be any trace with T ∈ R_{vk_i}(x_i)
(§1.2: constraints on all rows, including zero rows beyond tight heights; buses balanced mod p;
program columns = P_i). Then, with fixed deterministic maps dec_i and pv_i:

* (F1) **Verifier correctness.** π_{i−1} := dec_i(T) and x_{i−1} := pv_i(T) satisfy
  V_{i−1}^{SHA-384}(vk_{i−1}, x_{i−1}, π_{i−1}) = 1. Here V_{i−1} is the native verifier of
  §1.2/§6.4 with the T\* transcript, WHIR-Y, the ×15 sampler (rejecting p − 1), multiproof,
  coset leaves, 42-B digests and grinding z = 32, run with vk_{i−1}'s constants.
* (F2) **Constants.** vk_{i−1} is a constant of P_i: its pre-hash, all params including
  c = 15, m, target, z, k₁, k, b, l_skip, n_stack, rot_mask, max_constraint_degree and the
  interaction limit. The program/app binding of Lemma 3.6 is checked for the child, against
  P_NV when the child's level is ≥ 2 and against P_1 when it is 1. The extended verifier
  V′_{i−1} = V_{i−1} ∧ [child program openings = P̂_{i−1}(r)] is what is arithmetised.
* (F3) **Public values.** level(x_i) = level(x_{i−1}) + 1, the app-mode flag is 0 iff
  level(x_{i−1}) = 1, and the base-statement digest passes through unchanged.
* (F4) **Bus semantics.** Balance mod p of every bus (Lemma 3.1) suffices for (F1). For
  example, multiplicities are boolean or range-checked, and per-message uses < p.
* (F5) **Zero rows.** Rows beyond each tight height are all-zero, and (F1)–(F4) hold for every
  such T. Zero rows must be inert.
* (F6) **Hash rows.** Every SHA-384 evaluation that (F1) uses to verify π_{i−1} is a row
  sequence of NV_i's SHA AIR in T. Call the set of these message/digest pairs Q_i(T). This is
  what A-IC (7.3) refers to.

The native final verifier V_d checks:
* π_d under vk_d with the T\* transcript;
* level(x_d) = d;
* π_d's program openings = P̂_NV(r) (Lemma 3.6);
* that the base-statement digest equals the claimed chunk statement.

**Lemma 7.2 (Base-faithful) [A here].** For every T ∈ R_{vk_0}(x_0), the chunk-validation
statement named by x_0 holds.

**Former Assumption 7.3 (A-IC): withdrawn as a justification in the independent-oracle model.**
The old premise required every concrete SHA-384 pair in every extracted NV
trace to occur in the measured database of an independently sampled oracle H.
Adding a time cap does not justify that identification. At a fixed input m,
`Pr[H(m) = SHA384(m)] = 2^-384`. If acceptance has probability at least `1-δ`
and consistency requires this pair, consistency fails with probability at least
`1-δ-2^-384`. `Qrom.OracleBridge` proves the finite counting statement and the
corresponding general probability-space inequality. Applying the latter to a
particular extracted trace still requires establishing the fixed-pair occurrence
and acceptance premises; it is not an attack on SHA-384 or the concrete scheme.

### 7.2 Separate the outer relation from recursive semantics
The outer QROM theorem can meaningfully establish membership in the *concrete*
NV AIR relation. Such a trace certifies that the concrete inner verifier accepts.
It does not imply that an independently sampled H accepts the inner proof.
The old A-IC argument cannot transport acceptance between these verifiers.

Two possible research endpoints are distinct:
* Keep this implementation and explicitly assume appropriately quantified
  computational soundness of the inner concrete-hash proof system. This is a
  substantive cryptographic assumption, not a consequence of SHA collision
  resistance alone or a proved recursive security guarantee.
* Change the construction/model so that the inner verification relation and
  oracle semantics are linked by a valid theorem. A new construction needs its
  own quantum proof and measurements; the existing 293,077-byte artifact does
  not measure it.

### 7.3 A possible peeling reduction, not yet established
A valid reduction would need an extractor which, outside an event of probability
`ε_outer`, turns an accepted false outer statement into a satisfying NV trace.
NV-faithfulness and statement linkage would turn that trace into an accepted
false **concrete** inner proof. This would yield a bound of the form

```
ε_recursive(A) ≤ (sqrt(ε_inner(B) + ε_outer_bad + δ_sim) + sqrt(ℓ_V/2^336))²,
```

where B is the actual extraction reduction and δ_sim bounds its simulation
discrepancy. `Qrom.Peeling.bound` checks this scalar implication. The original
peeling formula omitted a replacement cross term. G-P1-C in
`aic-research/LEMMA.md` §6 supplies a written quadratic gate lower bound for a
universal fixed-interface online simulator; it does not cover QRAM or arbitrary
adversary-specific reductions. Its finite causal-cone count is kernel-checked.
 To use a computational assumption,
B must be efficient under an explicitly charged runtime/advice budget. Oracle
simulation and database extraction must be included; an existential witness
or the query substitution `q -> 2q` does not establish this requirement. If the
inner assumption permits an independent final-domain oracle, state that game;
otherwise prove and cost the simulation removing it.

No numerical `ε_inner` or validated reduction is supplied here. In particular,
assuming the desired concrete inner security and then calling the result
"proven recursive security" would conceal the central obligation. The prior
Theorem 7.4 and its depth-independent numerical conclusion are withdrawn.

### 7.4 Depth and resource accounting
Depth affects the verifier family, faithfulness obligations, extraction chain
and reduction cost. Whether the final failure probability needs a per-layer
sum depends on the completed game/reduction. No depth-independent security
number is currently established.

---

## 8. Model boundary and related composition work

An outer proof of concrete verifier execution and a recursive proof of the base
statement are different theorems. Section 7 now states the missing implication
without identifying concrete SHA with an independent oracle.

The prior-art discussion in the paper compares straight-line PCD composition
(CGSY24), algebraic-oracle PCD (CCGOS23), relativized-argument limitations (BCG25)
and QROM extraction (CMS19, CFHL21, CDHZ26). None is instantiated here as a
quantitative theorem for this concrete recursion circuit. In particular, the
classical composition literature does not by itself supply the required quantum
reduction or its runtime bound.

The contract remains open even for the outer layer until the family, sampler and
WHIR obligations are completed. For recursive semantics it additionally needs
NV faithfulness, statement binding and the model/reduction in §7. Merely adopting
A-IC or replacing its name with "hash security" does not close those obligations.

---

## 9. Historical numeric calculation (not an established bound)

For t = 2⁶⁴, T\*, z = 32, U-13 proximity inputs, ×15, 42-B digests. Output of `calc/bound.py`:

| term | value (log₂) | source |
|---|---:|---|
| worst per-move rbr-KS error ε (final, WHIR query r1, 236.01 + 32 bits) | −268.01 | Lemma 5.1 |
| next: inner NV query r2 | −268.02 | Lemma 5.1 |
| worst non-query: OOD r1 (final, ℓ = 2⁴¹·⁰, one sample) | −271.91 | Lemma 4.4 |
| worst PIOP (LogUp, ℓ₀ = 2⁴⁰·⁰) | −279.16 | Lemma 3.1 |
| worst fold MCA (DKT26) | −280.74 | Lemma 4.3 |
| WHIR μ batching, W = 141 / 141 / 601 (first-order curve) | −282.1 / −283.0 / −287.5 | Lemma 4.2 |
| narrow transition 10·3t′/2³³⁶ | −266.1 → below ε-term | withdrawn family estimate |
| wide transition 10·J(2t′+1)/2³⁸⁴ | −294.7 | withdrawn family estimate |
| challenge transition 10(ε + …) | −264.69 | withdrawn family estimate |
| Fact A √(ℓ_V/2³³⁶), ℓ_V ≤ 2¹⁶ | −160 | replacement parameter to justify |
| simulation factor t → 2t | +1 bit on t | Lemma 6.3 |
| **historical total (one database, all layers)** | **−134.69** | unestablished premises |
| total, union over 7 layers | −131.89 | — |
| contract | −128 | U-6 |
| margin | 6.7 bits (3.9 with the union) | |

**Required before reusing these numbers:** completion of the concrete family
instantiation and its constants, the DKT26 → WHIR transfer, validation of T*
against the pinned implementation, NV/Base-faithfulness, the sampler-cap correspondence and a precise recursive
hash model. These repairs may change the numbers. See GAPS.md.
Under the superseded BCGM m = 3 inputs the same table gave −135.23 (−132.42 with the union).

---

## References
* [ACFY] Arnon, Chiesa, Fenzi, Yogev. WHIR. ePrint 2024/1586 (21 Nov 2024). Thm 5.2, Thm 4.3,
  Lemma 4.4, Construction 5.1.
* [BCGM] Bordage, Chiesa, Guan, Manzur. All polynomial generators preserve distance with
  mutual correlated agreement. CCC 2026; ePrint 2025/2051 v5 (19 May 2026). Def 9.1, Thm 9.2
  (superseded basis; `bound.py --bcgm`).
* [DKT26] Dao, Kominers, Thaler. Reed–Solomon codes beyond Johnson. ePrint 2026/2056 (16 Sep
  2026). Thm 5.12, Prop 5.10, Lemmas 5.6, 5.11, Cors 7.3, 7.5, 7.7, 7.8. Lean: ArkLib fork
  github.com/quangvdao/ArkLib @ a5aa2677fee4e3a79d6bb05136631cce4a08587d; checked on
  `lane/pq-dkt-verify` @ d9dc1c0e3 (DKT-VERIFY.md, `lean/DKTGlue.lean`, `lean/DKTCerts.lean`).
* [Pus26] Puškin. An analysis of the WHIR IOPP. MSc thesis, Univ. Tartu, Feb 2026
  (hdl 10062/119861). Thm 5.3 (corrected WHIR Thm 5.2), Lemma 3.40, Thm 3.41.
* [BCIKS20] Proximity gaps for RS codes. ePrint 2020/654. Thm 5.1.
* [CMS19] Chiesa, Manohar, Spooner. Succinct arguments in the QROM. TCC 2019; ePrint 2019/834.
  Thm 8.6, §8.5.1–8.5.2, Lemmas 4.9, 5.13, 6.11, 8.13.
* [CFHL21] Chung, Fehr, Huang, Liao. Eurocrypt 2021; arXiv 2010.11658. Lemma 4.3, Cor 4.2.
* [Zha19] Zhandry. How to record quantum queries. ePrint 2018/276.
* [DFMS22] Don, Fehr, Majenz, Schaffner. Online-extractability in the QROM. ePrint 2021/280.
  Prop 3.5.
* [COS20] Chiesa, Ojha, Spooner. Fractal. ePrint 2019/1076. Thm 10.1, Thm 11.5.
* [BCG25] Barbara, Chiesa, Guan. Relativized succinct arguments in the ROM do not exist.
  TCC 2025; ePrint 2024/728. Thm 4.1, 5.1.
* [CCGOS23] AROM PCD. ePrint 2023/587. Thm 9.4.
* [CGSY24] Security bounds for PCD from straightline extractors. ePrint 2023/1646. Thm 5.1.
* [CDHZ26] Chiesa, Di, Hu, Zheng. ePrint 2025/2166 (2 Mar 2026). Thms 6.9, 6.10, 8.3, 11.3.
* [CO25] Chiesa, Orrù. A Fiat–Shamir transformation from duplex sponges. ePrint 2025/536.
  §1.3, Thms 6.1/6.2.
* [Gru24] Gruen. ePrint 2024/108. App. A.3.
* [PH23] Papini, Haböck. LogUp-GKR. ePrint 2023/1284. Props 1–2.
* Project notes [P′]: weak-binding ANALYSIS.md (Lemma 1, Lemma 2, Fact A, Thm 4),
  REVIEW-1.md, HROB.md (Thm R, Lemmas 4.7–4.8, Prop 2.1); x15-domains SOUNDNESS.md; levers
  README (spec, tight heights); recursion-nv DESIGN/README.
