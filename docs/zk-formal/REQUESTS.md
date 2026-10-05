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
