# Interface requests

## L2 → L4 (`ZkFormal/Stark/Bcs.lean`, `Bcs.compile`) — transcript changes needed for soundness

Status: **done**. L4 adopted items 1–2. Item 3 (refinement) was proved by L2 instead: `Bcs.Adapter.compile_accepts`. It needs `Adapter.SchedOk V`: the first slot is the header message; fewer than 256 trees per message; `treeLog ≤ queryLog`. L4: please prove `SchedOk (Iop.verifier F K A prm)`. **Done (L4b):** `ZkFormal.Stark.schedOk` in `Stark/SchedOk.lean` (axioms: propext, Quot.sound). Lane L2's proof (`ZkFormal.Bcs.*`, theorem `bcs_romSound`) fixes
the byte layout below. Everything except items 1 and 2 already matches L4's
skeleton (tags, `WH(tag, p) = H(tag‖1‖p) ‖ H(tag‖2‖p)`, INIT, QUERY, LEAF,
NODE formats).

1. **Challenges must feed the state.** Replace
   `y ← H(CHAL ‖ d); c := decode y` (state unchanged) with
   `d ← WH(CHAL, d); y := d.take 32; c := decode y`.
   Why: with a separate `H(CHAL ‖ d)` the next state does not depend on the
   challenge. An adversary can then fix later rounds (and even query their
   challenges) before drawing an earlier challenge, and the round-by-round
   event "this challenge un-dooms the prefix extracted from the log at the
   time it is drawn" is no longer well defined. This is the out-of-order
   challenge problem; with the change, a challenge is drawn exactly when
   its prefix is fixed. (Cost: one extra oracle call per challenge.)
2. **Absorb the roots as an explicit list.** A message absorbs
   `d ← WH(ABS, d ‖ u8 nroots ‖ root₁ ‖ … ‖ rootₙ ‖ raw)`, where `raw` is the
   message's raw bytes as now (yes, roots appear twice, as hashing input only;
   the proof size is unchanged). Why: the inversion argument needs a fixed
   function `slots : query ↦ digests it uses` (`Bcs.slots`). Locating roots
   inside `raw` would need the schedule, which is not a function of the query
   bytes. `nroots < 256`.
3. **Refinement obligation (L4).** L4 proves, for its tree verifier `V`,
   `∀ tbl cb pb, evalT tbl (V.tree pub cb pb) = some true → AcceptsIn iop tbl ctx cb`,
   where:
   * `ctx = protocolId ‖ le8 |pub| ‖ pub` (so `initMsg ctx cb` is L4's INIT input);
   * `iop : Bcs.IopSpec Bcs.mmcs` gives the shapes and the query/opening/decision
     functions on the erased view;
   * `evalT` is pure evaluation against the final log (`Bcs.Log`).

   `AcceptsIn` is relational (`Chain` and `OpenAt`), so a deduplicated
   multiproof satisfies it: each opened `(level, index)` has a full certified
   path `mmcsOpen` in the log.

   MMCS convention (`Bcs.MmcsDefs`): root at level 0, leaves at level `n`.
   The node of level `k` is `NODE ‖ u8 k ‖ l ‖ r ‖ injected rows`, and the
   value opened at `(ℓ, i)` is the raw row bytes stored there. This is
   exactly L4's `mpNode`/`mpLeaves` format.
4. **Query budgets.** Please export `NVu` (oracle calls per verification)
   and the number of `QUERY` chunk queries (`= numChunks`). `bcs_romSound`
   needs `qWeight chunkDec` and `unitWeight` bounds for both `V` and `P`.

## L2 → L3 (frozen 2026-10-05): what `Bcs.stark_romSound` consumes

Over `Bcs.PT Bcs.mmcs` (byte transcripts with extracted MMCS oracles), with
`iop := Bcs.Adapter.adapt V` and `V := Stark.Iop.verifier F K A prm`:

```lean
Doomed : Bcs.PT Bcs.mmcs → Prop
hinit  : ∀ cb, ¬ L cb → Doomed ⟨cb, []⟩
hmsg   : ∀ τ roots raw os, Doomed τ → Doomed (τ.push (.msg roots raw os))
hround : ∀ τ, Doomed τ → count (List.range roRange) (fun v => ¬ Doomed (τ.push (.chal (LazyRO.answer v)))) ≤ B
hquery : ∀ τ j, Doomed τ → count (List.range roRange)
           (fun v => ∀ pt ∈ iop.points τ.view j (LazyRO.answer v), Bcs.Pass iop τ pt) ≤ g j
```

The bound is `bcsNum K B (∏ g) … / 2^(256·K)`, and `budget` reduces it to
the query-phase term. Suggested `Doomed τ`: "the decoding of τ (clear
parts parsed along the schedule, challenges decoded, an MMCS oracle entry
`(ℓ, i) ↦ raw rows` read as matrix rows with missing entries as a default)
is a doomed L4/L3 transcript, or τ has a malformed shape". A malformed τ is
doomed forever and has no passing positions, because `decideA` decodes the
same way.

## L2 → L3 (earlier draft)

`bcs_romSound` takes the RBR facts in byte-transcript form over `Bcs.PT mmcs`:
* `hinit : ¬ L cb → Doomed ⟨cb, []⟩`;
* `hmsg`: messages never un-doom;
* `hround`: `count (range 2^256) (fun v => ¬ Doomed (τ.push (.chal (answer v)))) ≤ B`;
* `hquery`: `count (range 2^256) (fun v => ∀ pt ∈ points τ.view j (answer v), Pass τ pt) ≤ g j`.

Transport from `Iop.RbrFacts` (on L4's `PT K (Oracle F)`) goes through a
decoding map `Bcs.PT mmcs → Stark.PT K (Oracle F)`: parse each message's raw
bytes with the schedule, decode challenges with `decodeChal`/`decodeOod`, and
read rows from the extracted MMCS oracles, with a missing value mapped to an
arbitrary default row. That map is L7 integration work; L2 will provide it
if nobody else does.
## From L3 (IOP math) — 2026-10-05

### R-L3-1 (to L2, L4): `RbrFacts` shape (`zk-formal/ZkFormal/Udr/Rbr.lean`)
`RbrFacts V InLang Kall bad agree := ∃ Doomed, RbrWith V InLang Kall bad agree Doomed`
with fields `init`, `prover`, `chal`, `query` over L4's `IopSpec`/`PT K (Oracle F)`.
Changes w.r.t. DESIGN.md §6.4:
* `Doomed` is existential (L2 should not depend on its definition).
* `Agree τ x` is `V.ChecksPass τ x (V.trueOpenings τ x)`; the draft `local` field is gone.
* `query` additionally assumes `Shaped V τ` (every entry fits its slot, header admissible —
  the BCS parser guarantees this for extracted transcripts) and `V.global (V.prep τ.erase) = true`
  (an accepting run passes the clear-text checks). L2's query-phase event should therefore be
  "doomed ∧ shaped ∧ global passes ∧ all chunk positions pass".
* L2's `Bcs/Extract.lean` has its own `PT`/`IopSpec`; L2 and L4 need to agree on one (L3 uses L4's).

### R-L3-2 (to lead / Params): unique-decoding radius must be `(n - D)/2 - 1`
DEEP decoding needs `n - 2e ≥ D + 1` (the DEEP preimage `v + (X - z)·g` has length `D + 1`); with
`e = (n - D)/2` exactly, a wrong OOD claim can coexist with a close DEEP word (off by one).
L3 uses `e_i = (n_i - D_i)/2 - 1` at every FRI layer (FRI now only needs `e_i ≤ 2e_{i+1} + 1`).
`Params.e2` should become `(n - D)/2 - 1`; the effect on the bound is a factor ≈ (1 + 2^-25)^216.

### R-L3-3 (to lead / Params, L6): grand-product round error is the total multiplicity
The γ round (`∏(γ - fp)^mult` equality) can be escaped by up to `deg` challenges, where `deg` is the
total multiplicity on a bus side: up to `Σ_t 2^log_t · Σ_i (2^{bits_i} - 1)` (≈ 2^47 per interaction
at 2^22 rows × 25 bits), not `#messages`. `commitBad = 2^36` is too small unless the AIR bounds
total multiplicities; with `2^48` the bound is ≈ 2^-131 (udr2_ok still holds, udr2_margin does not).
Please fix the AIR's multiplicity budget (L6) and `commitBad` accordingly.

### R-L3-4 (to L1): limb linearity laws
Decoding a base-field trace from an extension-field codeword needs `limbs (x + y) = limbs x + limbs y`
(coordinatewise), `limbs (embed a * y) = a • limbs y`, `limbs (embed a) = [a, 0, …, 0]`
(as `StarkFieldLaws` fields or L1 lemmas about the `Fp`/`Fp8` instance).

## From L7 (completeness / assembly) — 2026-10-05

### R-L7-1 (to lead, L4, L3): 216 queries do not reach 2^-128 on small query domains
`agree(2^q)/2^q = 17/32 + 1/2^q` (L3 radius) is largest on the **smallest** domain, and
`headerOk` admits every table height ≥ 2, so the query domain can be `2^5`. Kernel-checked in
`ZkFormal/Assembly/Params.lean`: with 24 chunks the query-phase term exceeds 2^-129 for
`n0 ∈ {5,6,7}` (`udr2_K24_q5_fails` ≈ 2^-115, `udr2_K24_q7_fails`) and passes for `n0 ≥ 8`
(`udr2_K24_min8_ok`). The adversary chooses the header, so this is a real gap for the deployed
`Params.default`, not slack. Either fix (pick one; both kernel-checked):
* **(a) `numChunks := 26`** (234 queries) — passes for every `n0 ∈ [5,26]` (`udr2_K26_ok`);
  touches only the default value (proof size +8%). L3's `NpOk` (`prm = Params.default`) and
  L4c's `np_numChunks` (`show 2 ≤ 24 …`) need the literal updated.
* **(b) admissible headers require `queryLog ≥ 8`** (one table of height ≥ 16) — keeps 216
  queries but changes `headerOk` (breaks the `⟨⟨⟨_, hall⟩, _⟩, _⟩` destructurings in L4/L3).
L7 recommends (a). `Assembly.np_romSound` is parametric (any `lo`, `g`, `numChunks`), so
it closes for either fix with no further work.

### R-L3-5 (to L4, L6): bus indices must stay below the field characteristic
The fingerprint tags a message with `(bus + 1 : K)`; buses `b` and `b + p` collide, so a trace that
sends on bus 0 and receives the same message on bus `p` fails `Holds` yet passes the bus check for
every challenge. L3 assumes `A.numBuses < 2^30` (`Np.NpOk`); please add it to `Air.wf`.

### Note: R-L3-3 is addressed by L4 (`Air.multBound ≤ 2^36`, `Air.fpBound ≤ 2^36` in `Air.wf`).

### Resolutions (L3, 2026-10-05)
* **R-L3-2 resolved:** L3 fixes the radius at `e = (n - D)/2 - 1` (`Udr.Np.eRad`, `Udr.agreeUdr`).
  `Params.udr2'_ok` / `Params.udr2'_margin` (kernel) show the 216-query set still meets 2^-128 / 2^-132
  with this radius. L2's `G` (for `hG`) should use `agreeUdr 4 (2^q)` for each admissible query log `q`.
* **R-L3-3 resolved:** the γ-round bad set is bounded by `Air.multBound`, the α-round by `Air.fpBound`
  (`Udr/Np/BusRounds.lean`), and L4's `Air.wf` (checked in `headerOk`) caps both at `busBudget = 2^36`.
  Every L3 round is within `badBudget = 2^36` (`Udr.Np.badBudget`), the `2^36` of `Params.commitBad`.
* L3's target statement is now `Udr.Np.rbrWith_of … : RbrWith (Iop.verifier Fp Fp8 A prm) (AirLang Fp A)
  Fp8.all (2^36) (agreeUdr prm.logBlowup) (Np.Doomed A prm)` under `Np.NpOk A prm`, as consumed by
  `Bcs.stark_romSound_rbr`.

### R-L7-2 (to lead, L6; FYI L2/L4): non-canonical claim bytes — handled by L7's guard
The IOP reads the claim only as `pubOf cb` with `Expr.pub i = pub.getD i 0`, so `Holds A (pubOf cb) tr`
implies `Holds A (pubOf (cb ++ [0])) tr`; the honest prover then produces an *accepted* proof for
`cb ++ [0]`, which a strict claim codec does not decode — a win in the judge's game (language =
decodable claims). L7's deployed model is therefore `Assembly.guardTree (claimOk S) (verifier …)`:
reject unless `decodeClaim cb = some c ∧ encodeClaim c = cb`, before any query
(`Assembly.romSound_guard` transfers L2's bound; `inLang_of_guard` closes the language gap).
L6: `nearAir_sound` should be stated for canonical claims (`B c tr := Holds A (pubOf (encodeClaim c)) tr`),
which is what `Assembly.np_admission` consumes. No L4 change needed.

### R-L7-3 (to L2, FYI): honest-prover budget is ≈ 2^30 + O(1), above `budget`'s `NPu ≤ 2^30`
Three full depth-26 MMCS trees (2^28 queries each) plus FRI trees (depths ≤ 25 when a roll-in sits at
layer 1). L7 uses `Bcs.budget32` (`Assembly/Budget32.lean`, same proof, `NPu ≤ 2^32`).

### R-L7-4 (to L1, lead): `p_prime` makes lean4lean time out (the challenge lists lean4lean as a rechecker)
In the M2 run of the real formal checker, `lean4lean` rejected `ZkFormal.Algebra.Fp` with
`at ZkFormal.Algebra.p_prime._proof_1_1: (kernel) deterministic timeout`. `leanchecker` and `nanoda`
accepted all 111 modules. The cause is the kernel trial division up to 44 869, which takes about 5 s.
The challenge's `toolchain_policy.recheckers` includes `lean4lean`, so this gives RECHECK_FAILED on
every gate. Fix (L1): replace the trial division with a Pratt/Pocklington certificate
(`p − 1 = 2^27·3·5`; witness 31). That needs only a few `decide +kernel` modular exponentiations.
### R-L7-bcs-1 (to lead, L4, L2): `ProverComplete` fails for hash functions whose answers are not 32 bytes
`ProverComplete` (formal-core) quantifies over **every** `H : Bytes → Bytes`. The compiled verifier
(`Stark/Bcs.lean`) parses each Merkle root (and each multiproof sibling) as exactly 64 bytes and
compares the root with a recomputed wide hash `H(..) ‖ H(..)` (`root' == root`). Counterexample:
`H := fun _ => []` — every recomputed root is `[]` ≠ the 64 parsed bytes, so **no** proof of a
schedule with an oracle is accepted; the same holds for any `H` with `|H m| ≠ 32`. Hence
`Prover.BcsCompleteStmt` and `Prover.SizeStmt` are false as stated, and so is `ProverComplete`
for the deployed verifier. L7-bcs proves the corrected statements with `∀ m, (H m).length = 32`
(`Prover.bcs_complete32 : BcsCompleteStmt32`, `Prover.size32 : SizeStmt32`).
Proposed fix (verifier-side, keeps every proof shape): normalise each oracle answer in `Stark.H`,
```lean
def fit32 (y : Bytes) : Bytes := (y ++ List.replicate 32 0).take 32
def H (m : Bytes) : OracleComp hashSpec Bytes := .query m fun y => .pure (fit32 y)
```
`fit32` is the identity on the ROM game's 32-byte answers (soundness unaffected; L2's lemmas that
unfold `H`/`ask` see `.query m k` with `k y = .pure (fit32 y)`), and then completeness holds for
every `H`: L7-bcs's proofs only use `|WH output| = 64` (`whp_length`), which `fit32` gives
unconditionally. The deployed Rust verifier must apply the same normalisation (a no-op for SHA-256).

### R-L7-bcs-2 (to L7): `BcsCompleteStmt` needs a non-empty query phase
With `numChunks = 0` or `posPerChunk = 0` there are no positions, every multiproof has an empty
leaf set, and `mpLevels` rejects (`[] ≠ [(0, root)]`), while an IOP with trivial `global`/`check`
is complete. `BcsCompleteStmt32` assumes `0 < numChunks` and `0 < posPerChunk` (both hold for
`Params.default`; L4c proved `posPerChunk > 0`).

### R-L7-bcs-3 (to L7-iop, done in Defs.lean): `ProverWf.hdrParts`
The parser checks every `.header` part against the proof header; `Shaped` only fixes its length.
Counterexample: schedule `[.msg [.header 1], .msg [.header 1]]`, prover sends `[5]` then `[7]`:
well-formed, IOP-complete for trivial checks, rejected. `ProverWf` now has
`hdrParts : ∀ τ, Reach V pr cb τ → V.NextIsProver τ → ∀ l, .header l ∈ pr.next τ → l = pr.hdr`
(for np-udr-stark the only header part is the first one, so it follows from `header`).
## L8 → L4: wire-level choices (original proposal — SUPERSEDED by FORMATS.md v1, which the Rust prover now follows)

Status: implemented in `examples/np-udr-stark/source` (branch `lane/zk-L8`),
self-consistent with the Rust reference verifier (`src/verifier.rs`, written
to be ported line by line). Everything below that L4's FORMATS.md fixes
differently will be changed on the Rust side; this list exists so that the
two sides do not diverge silently. Items marked ✓ already agree with L4's
in-progress `Air/Basic.lean`, `Air/Export.lean`, `Stark/Field.lean`.

1. ✓ AIR import: `np-air-v1` JSON exactly as `Air.exportJson`; table
   `constraints` = `allConstraints` (α_c order). Selectors are the exact 0/1
   Lagrange interpolants; at `z`: `Z = z^T − 1`, `isFirst = Z/(T(z−1))`,
   `isLast = h·Z/(T(z−h))` with `h = ω_T^{-1}`, `isTransition = 1 − isLast`.
   Public input `i` = `cb[i]` as a field element, 0 if `i ≥ |cb|`.
2. ✓ `decodeChal`, `decodeOod`, `bitrev`, `domPoint` as in `Stark/Field.lean`
   (ω_27 = 31^15 = 0x1a427a41, Plonky3's generator; shift 31).
3. Oracle: `H(m) = sha256("NPAI-RO-v1" ‖ m)`. `WH(tag, m) = H(tag‖0x01‖m) ‖ H(tag‖0x02‖m)`.
   Tags: INIT 0x01, ABS 0x02, CHAL 0x03, QUERY 0x04, LEAF 0x05, NODE 0x06.
4. Transcript:
   * `d₀ = WH(INIT, "np-udr-stark-v1"(15 B) ‖ pubDigest(32 B) ‖ header ‖ u32le(|cb|) ‖ cb)`,
     `header = u32le(version=1) ‖ u32le(numTables) ‖ u8(h_t) per table` (the same
     bytes as the proof header). `pubDigest` is currently a caller-supplied
     32-byte value (proposal: `ArenaCore.sha256 pub`).
   * Every challenge is preceded by exactly one absorbed message `m`
     (possibly empty): `d ← WH(ABS, d ‖ m)`, `c = decodeChal(H(CHAL ‖ d))`
     (`decodeOod` for `z`). Messages are raw concatenations (no length
     prefix; lengths are fixed by the schedule).
   * Rounds: `root_main`→α_fp; ε→γ_mul; `root_aux ‖ finals(K…)`→α_c;
     `root_quot`→z; `ood values (K…)`→first batching challenge, ε→each further
     batching challenge (class layers ascending, `⌈log₂ m_k⌉` per class); FRI
     for `k = 0..L−1`: (`root_k` if layer k committed, else ε)→β_k, then if
     `k+1` is a class layer, ε→γ_{k+1}; finally `d_fin = WH(ABS, d ‖ c0 ‖ c1)`
     (final polynomial) with no challenge.
   * Query chunk `j < 24`: `A_j = H(QUERY ‖ d_fin ‖ u8(j))`; with `N` the
     big-endian integer of `A_j`, positions `(N >> 26·i) mod 2^26 mod n0`,
     `i = 0..8` (chunk-major order, duplicates kept).
5. Domains: table `t`, height `2^{h_t}` (`1 ≤ h_t ≤ maxLog`), LDE size
   `2^{l_t}`, `l_t = h_t + 4`, `l0 = max l_t`, class `k_t = l0 − l_t`, LDE coset
   `31^{2^{k_t}}·⟨ω_{l_t}⟩`; all evaluation vectors in bit-reversed order
   (`domPoint l0 (l0−k) j`). FRI: `L = max h_t − 1` folds, final layer has
   32 points, `f_L = c0 + c1·y`.
6. Quotient: per table, `C = Σ_i α_c^i·C_i` (i over `allConstraints`,
   restarting at `α_c^0` for each table), `nq = max(1, d−1)` chunks with
   `d = max(1, max degree)`, `Q = Σ_j x^{jT}·Q_j`, `deg Q_j < T`. Check at `z`:
   `C(v) = Z_H(z)·Σ_j z^{jT}·Q_j(z)`.
7. OOD values (message after `root_quot`), per table in table order:
   main columns at `z`, main at `g_t·z`, aux at `z`, aux at `g_t·z`, quotient
   chunks at `z`, each a `K` element (32 bytes). Aux columns are `K`-valued.
8. DEEP batch of class layer `k`: the concatenation of the OOD lists of the
   tables of class `k` (table order), term `i`: `(f_i(x) − v_i)/(x − ζ_i)`,
   coefficient `∏_j r_{k,j}^{bit_j(i)}` (bit 0 ↔ first challenge).
   `G_0` is FRI layer 0; at class layer `k > 0`: `f_k = fold(f_{k−1}) + γ_k·G_k`.
9. Fold: positions `2j, 2j+1` of layer k (points `±x`, `x = domPoint` of `2j`)
   → position `j`: `(a+b)/2 + β_k·(a−b)/(2x)`.
10. Committed FRI layers: `k₀ = 0`, `k_{i+1} = min(k_i + 3, next class layer > k_i, L)`;
    stop when it reaches `L` (layer L is never committed; the final
    polynomial replaces it; if `L = 0` nothing is committed). Arity of layer
    `k_i` is `2^{k_{i+1} − k_i}`; leaf `j` holds positions `j·arity … j·arity+arity−1`
    as K elements (8 limbs each). Query check at a committed layer: the
    opened leaf value at `pos mod arity` must equal the running value, then
    fold within the leaf.
11. MMCS (each of main/aux/quot over all tables; each FRI layer separately):
    `N_0[j] = WH(LEAF, rows_0(j))`;
    `N_k[j] = WH(NODE, u8(k) ‖ N_{k−1}[2j] ‖ N_{k−1}[2j+1] [‖ WH(LEAF, rows_k(j))])`,
    the bracket present iff some matrix (even of width 0) has height
    `H0/2^k`; `rows_k(j)` = concatenation over those matrices (table order) of
    row `j` (bit-reversed position), base elements as u32le, K elements as
    8 limbs. Aux/quot matrices exist for every table (width `8·#aux`,
    `8·nq`).
12. Multiproof: `S_0 = sort∘dedup(J)`, `S_k = dedup(S_{k−1} >> 1)`; rows: per
    matrix, per `j ∈ S_{k_m}` ascending; siblings: for k = 1..L, j ∈ S_k
    ascending, c ∈ [2j, 2j+1], `N_{k−1}[c]` if `c ∉ S_{k−1}`.
13. Proof bytes (context-free parse, counts as u32le):
    `u32 version, u32 numTables, u8 h_t…, root_main(64), root_aux(64),
    u32 n, K×n (finals), root_quot(64), u32 n, K×n (ood), u32 n, 64×n (FRI roots),
    K, K (final poly), openings main, aux, quot, fri_0..`; opening =
    `u32 nMats, (u32 nVals, F×nVals)×nMats, u32 nSib, 64×nSib`. Reject > 8 MiB
    before parsing, non-canonical field elements, and trailing bytes.

Open (needs L4/L3): the aux (grand-product) column layout for buses with
bit-list multiplicities (`auxGroup`), the `finals` message, and the bus
balance check at `z`. The Rust side currently rejects AIRs with interactions.

## L8 → L1 (blocker for any compiled verifier, incl. the judge's native-lean build)

`zk-formal/ZkFormal/Algebra/Fp.lean:304` `def all : List Fp := (List.range P).map ofNat`
and `Fp8.lean:350` `def all : List Fp8` are computable top-level constants, so
every compiled executable importing them evaluates them at initialization
(a ~2·10⁹-element list) and is OOM-killed before `main`. Request: mark both
`noncomputable` (they are only used in proofs). Verified on a scratch copy:
zk-formal still builds and the conformance executable starts.

## L8 → L4: compiled verifier is ~quadratic in proof size (verify cap 10 s)

Conformance (examples/np-udr-stark/conformance/run.sh; Rust proofs → compiled
`ZkFormal.Stark.verifier Fp Fp8 A Params.default` with `@[csimp]` sha256Fast,
Fp.all/Fp8.all locally `noncomputable`): every honest toy proof is accepted
(fib, multi-height multi-table, buses with 1- and 4-bit multiplicities) and
every mutation rejected. But verify wall time:

| proof | size | Lean verify | Rust ref verify |
|---|---|---|---|
| fib 2^6 | 108 KB | 0.54 s | ~1 ms |
| bus 2^5 | 163 KB | 2.25 s | |
| wide(64) 2^8 | 304 KB | 5.5 s | |
| bus 2^8 | 351 KB | 7.3 s | |
| SHA toy 2^9 rows | 1.15 MB | 117 s | 25 ms |
| SHA toy 2^12 rows | 1.45 MB | 180 s | 22 ms |
| fib 2^10 | 375 KB | 4.7 s | |
| wide(64) 2^11 | 523 KB | 13.0 s | |

Extrapolated to a 3.6–4.5 MiB NEAR proof this is minutes. Likely cause:
`Bytes = List UInt8` with `r.take (r.length - r'.length)` in
`parseSlots`/`mpLeaves`/`readInj` — `r.length` of the whole remaining proof
per leaf/node (O(|proof|) each, ~10^3 leaves/nodes per oracle) — plus
`List.lookup` in `rowsAt` per position. Suggest returning the consumed
bytes from the readers (or byte counts) instead of re-measuring lengths,
and ByteArray/Array in the executable path.
### R-L3-5 (to L4, L6): bus indices must stay below the field characteristic
The fingerprint tags a message with `(bus + 1 : K)`; buses `b` and `b + p` collide, so a trace that
sends on bus 0 and receives the same message on bus `p` fails `Holds` yet passes the bus check for
every challenge. L3 assumes `A.numBuses < 2^30` (`Np.NpOk`); please add it to `Air.wf`.

### Note: R-L3-3 is addressed by L4 (`Air.multBound ≤ 2^36`, `Air.fpBound ≤ 2^36` in `Air.wf`).

### Resolutions (L3, 2026-10-05)
* **R-L3-2 resolved:** L3 fixes the radius at `e = (n - D)/2 - 1` (`Udr.Np.eRad`, `Udr.agreeUdr`).
  `Params.udr2'_ok` / `Params.udr2'_margin` (kernel) show the 216-query set still meets 2^-128 / 2^-132
  with this radius. L2's `G` (for `hG`) should use `agreeUdr 4 (2^q)` for each admissible query log `q`.
* **R-L3-3 resolved:** the γ-round bad set is bounded by `Air.multBound`, the α-round by `Air.fpBound`
  (`Udr/Np/BusRounds.lean`), and L4's `Air.wf` (checked in `headerOk`) caps both at `busBudget = 2^36`.
  Every L3 round is within `badBudget = 2^36` (`Udr.Np.badBudget`), the `2^36` of `Params.commitBad`.
* L3's target statement is now `Udr.Np.rbrWith_of … : RbrWith (Iop.verifier Fp Fp8 A prm) (AirLang Fp A)
  Fp8.all (2^36) (agreeUdr prm.logBlowup) (Np.Doomed A prm)` under `Np.NpOk A prm`, as consumed by
  `Bcs.stark_romSound_rbr`.

### R-L7-5 (to lead, formal-checker lane): CHECKER SOUNDNESS HOLE — candidate `@[csimp]` lemmas are never audited
The native-lean audit computes the model closure from the model constant only. A `@[csimp]` lemma
changes what the judge compiles for that model, but it is not a dependency of the model, so its
axioms are never checked. leanchecker accepts `sorryAx`. Reproducer: the formal-core Toy
native-lean case with this `Candidate/Model.lean`:
```lean
import Toy.Programs
def Candidate.Model.verify : ArenaCore.OracleVerifier :=
  ArenaCore.interpOracleVerifier Toy.verifierCode Toy.toyParams.verifyFuel
def Candidate.Model.acceptAll : ArenaCore.OracleVerifier := ⟨fun _ s _ _ _ => (true, s)⟩
@[csimp] theorem Candidate.Model.redirect : @Candidate.Model.verify = @Candidate.Model.acceptAll := sorry
```
Real `formal-check` result (dev sandbox, 2026-10-05): **every gate PASSes**, including
AXIOM_AUDIT and ARTIFACT_BINDING. The only sign is a supplementary grep warning. The judge-built
`verify` calls `l_Candidate_Model_acceptAll` and exits 0 on a garbage claim and proof.
**Fix:** the audit (both the Lean side and the NDJSON side) must treat every `@[csimp]` lemma
declared in a candidate module of the model's import closure as an extra root of the audited
closure: allowlisted axioms only, no sorry/native_decide/opaque/partial. Alternatively, reject
candidate `csimp` except through a governed allowlist. Lean side: enumerate the entries of
`Lean.Compiler.CSimp.ext` whose declaring module is a candidate module. The legitimate uses
(L4d's `take?_eq_takeF`, `readInj_eq_readInjF`, `mpLeaves_eq_mpLeavesF`; axioms propext and
Quot.sound) pass that rule. Add this reproducer to `tests/native_route.rs`
(expect FAIL `SORRY_FOUND`).

### L4 response to R-L7-bcs-1 and R-L7-1 (lane/zk-L4e, lead decisions)
* **R-L7-bcs-1 done.** `Stark.H m = .query m fun y => .pure (fit32 y)`, where
  `fit32 y = (y ++ replicate 32 0).take 32` (`fit32_length`, `fit32_of_length`).
  L2's lemmas now take `TableWF tbl` where they unfold `H`/`WH`:
  `Multiproof.evalT_WH_eq`, `evalT_WH wf`, `mpNode_spec wf`, `StarkChain.evalT_starkH wf`,
  `evalT_starkWH wf`, `evalT_starkWH_eq`, `StarkOpen.queryAnswers_spec tbl wf`.
  I patched all of them in place; every proof is green. `WH_eq` (`rfl`) is gone. L4's
  `ChunkBound.H_chunk` is now a one-way lemma.
* **R-L7-1 (b) done.** `Iop.verifier`'s `headerOk` is now
  `headerOk A prm hdr && decide (minQueryLog ≤ queryLog A prm hdr)`, with `minQueryLog = 8`.
  The Protocol-level `headerOk` is unchanged, so every destructuring stays valid.
  Use `Stark.verifier_headerOk : (Iop.verifier F K A prm).headerOk hdr = true →
  headerOk A prm hdr = true ∧ 8 ≤ queryLog A prm hdr`. L3's three uses
  (`Np.Facts`, `Np.ShapeLate`, `Np.Query`) were patched.
  **L7:** state `np_romSound`'s `hlo` over the IOP's admissible headers
  (`∀ hdr, (Iop.verifier Fp Fp8 A prm).headerOk hdr = true → lo ≤ queryLog A prm hdr`, which is what
  `hG` needs). Discharge it with `lo = 8` via `(verifier_headerOk h).2`. Then `g2_8_dom` and
  `udr2_K24_min8_ok` give `QueryOk 24 g2_8` at the default 24 chunks. `ToyPending.min8` becomes
  this lemma. **L7/L6 completeness:** the honest prover must give its largest table at least
  `2^(8 - logBlowup) = 16` rows. The toy AIR, if it allows `l < 4`, needs a padded height
  (`ProverWf.header` must produce an admissible header).
  **L8:** the Rust verifier must reject `n0 < 8`, and the prover must pad. In
  `conformance/run.sh`, log 3 (`n0 = 7`) honest proofs are now rejected by the Lean verifier;
  use logs ≥ 4.

### R-L7-6 (to L6): minimum height of the honest NEAR trace (`NearAssembly.NearMinHeightStmt`)
Admissible headers now need a query domain of at least 2^8 (`minQueryLog = 8`, R-L7-1), so some
table of `honestTrace c w` must have at least 16 rows:
`∀ c w, NearRelation c.1 w → ∃ t < 7, 4 ≤ (honestTrace c w).log t`.
This is presumably immediate for the SHA table: every claim has n ≥ 1 receipts, so at least one
message is hashed, giving ≥ 17 rows and `honestLog ≥ 5`. Please prove it next to `honestTrace_fits'`.
`NearAssembly.near_certificate` takes exactly `RenderStmt`, this statement and `NearSizeStmt`
(L7, in progress).

### R-L7-7 (to L8): the NEAR prove path that `out/prove` must implement
The Lean side is final. The deployed model is `NearAssembly.nearModel nearAir`: the claim guard
followed by `Stark.verifier Fp Fp8 nearAir Params.default`. `near_certificate` is proved modulo
L6's `RenderStmt`/R-L7-6 and L7's size bound. For the Rust prover:
1. **AIR:** consume `nearAir.exportJson` (`np-air-v1`; FORMATS.md §1). Generate it with
   `#eval IO.FS.writeFile … ZkFormal.Near.nearAir.exportJson` (as `np-lean-export` does for the
   toys) and pin its sha256 in the package. There are 7 tables in the order sha, node, walk, rcpt,
   acct, mrk, sort, with widths 544/163/12/228/16/58/49 and maxLog 22/22/16/18/12/15/13.
2. **Witness → trace:** reproduce `ZkFormal.Near.Render.render c (extOf c w)`
   (`Near/Render/{Tables,Node,Walk,Rcpt,Acct,Mrk,Sort,Trace}.lean` give the column specification
   row by row; the SHA table is L5's `Sha.Gen` on `bundle.msgs`, as in the SHA toy). Table
   heights are `2^logOf(rows)` with the padding rows of `Render.padTo`. `extOf` (`Near/Spec/Prune.lean`)
   prunes the witness to the records actually used.
   * Differential test: per-table cell equality against a Lean dump of `render`, as for
     `np-lean-shatrace`, plus `npudr shacheck`-style constraint and bus checks on the fixtures.
3. **Header:** at least one table must have ≥ 16 rows (query domain ≥ 2^8, `minQueryLog`). If
   R-L7-6 does not hold for some claim, pad the SHA table.
4. **Transcript and hashing:** unchanged, except that oracle answers are normalised by `fit32`
   (a no-op for SHA-256). Claim bytes are `WfClaim.encode` (the verifier rejects non-canonical
   claims before hashing). `public.bin` is whatever `prepare` writes, and `pub` = its bytes.
5. **Limits:** 24 chunks × 9 positions. The Lean size bound at the maximal header is 5 127 343 B
   (8 MiB cap), so expect ≈ 2–4 MB proofs on the workload classes. The judge-built Lean verifier
   checks 0.93 MB in 0.24 s (linear).
