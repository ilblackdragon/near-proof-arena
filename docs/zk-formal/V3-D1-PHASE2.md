# D1a phase 2: from `nearAirV3D1` to the D1a admission statement — plan and status

Status: **in progress; R-5 decided (B, AIR walks every `txKeys` entry), design note in §5** (lane `v3-d1-phase2`, branch `lane/v3-d1-phase2`, from main `0a78f36d`),
started 2026-10-14 on the user's go-ahead. Log: `docs/logs/v3-d1-phase2-2026-10.md`.
Inputs: phase 1 (`docs/logs/v3-d1-tables-2026-10.md`, main `86fab5fd`), design
`V3-D1-DESIGN.md` §6–7, the D0a certificate (`Assembly/AdmissionV3.lean`:
`nearV3_admission_final`), the relation `NearSpecV3.RelD1a`
(`spec/lean/v3/NearSpecV3/ChunkValidationD1a.lean`) and the tier `Tier.d1a` of the signed
challenge `near-chunk-v3` (`chl_497bbbf1…`).

Ground rules (unchanged from the D0a lanes):
* the trusted spec (`spec/`), the challenges, `nearAirV3` and the D0a certificate are not edited.
  Every phase-2 module is new and lives under `zk-formal/ZkFormal/NearV3/D1/`.
* There is no `sorry`, `axiom`, `native_decide` or `implemented_by` in a committed module.
* Statements are never weakened. A phase-1 statement that turned out to be mis-stated gets a
  corrected sibling. The original is kept and the defect is recorded (see §4).
* Modules are small, there is no `decide` over real data, and no simp folds `Nat` literals
  against free variables (the lean4lean/nanoda pitfall of v3-recheck).
* The build root is `ZkFormal.NearV3.D1.Phase2`. It imports every finished phase-2 module and is
  not imported by D0a or by the verifier model.

---

## 1. Target statement

The judge's expected type for `near-chunk-v3` at a declared tier (`spec/lean/judge/ExpectedChunkV3.lean.template`) is

```
ArenaExpected.expectedType = AdmissionStatement
  (NearSpecV3.challengeParamsChunkWith .d1a (profileOf …) verifyFuel maxProofBytes maxReductionFuel)
  { publicDigest, impl := .interp verifierDigest }
```

At the frozen challenge's literals this is definitionally `challengeParamsChunk .d1a`, the same
way D0a's `params` matched `challengeParamsD0a`. So the certificate is

```
theorem nearV3D1_admission_final (art) (pub) (hpub : sha256 pub = art.publicDigest)
    (himpl : art.impl.Connection (challengeParamsChunk .d1a).verifyFuel
      (npVerifierP (challengeSpecChunk .d1a) nearAirV3D1 split prepD1b).toVerifier) :
    AdmissionStatement (challengeParamsChunk .d1a) art
```

* `challengeSpecChunk .d1a` has `Rel = RelTier .d1a = RelD1a B0` on `c.1.encode`, and
  `Domain = DomainTier .d1a` (a `RelD1a` witness of at most 64 MiB).
* Soundness for the challenge statement (`RelChunkV3`) follows from `NearSpecV3.sound_lift` /
  `rel_mono` (`relD1a_relD1`), which are already in the trusted spec. Nothing more is owed.
* `npVerifierP` reads the spec only through `claimOk S`, i.e. through `decodeClaim`. The phase-1
  model `VerifierD1Defs` uses `challengeSpecD1a`, which has the same `decodeClaim`. Item A3
  checks that the two verifiers are equal (`rfl`). If they are not, the model is restated with
  `challengeSpecChunk .d1a`.
* The proof size is bounded by `nearAirV3D1_sizeMaxAligned = 6,927,206` (kernel-checked in
  phase 1), plus the hint: transactions plus new transactions ≤ 8 MiB, refunds ≤ 1.3 MB. This
  is well below the 64 MiB cap.

## 2. Dependency graph

The D0a split is reused: per-table views → link `GoodD1` → factor theorems → admission.

```
                    V0 AirD1 ✔ ─┬─ V1 relays ✔ (kib, plf, rid)
                                ├─ V2 txV3 view ──────────┐
                                ├─ V3 akmV3 view ─────────┤
                                ├─ V4 rcptV3D1 view ──────┤
                                ├─ V5 mrkV3@20 view ──────┤
                                └─ V6 21 unchanged views ─┤ (D0a theorems, reindexed)
 P0 public bindings D1 ───────────────────────────────────┤
 P1 prep lemmas ✔ (TxVerdict, LocalNative, TxNative) ─────┤
 P2 prepD1 decomposition ─────────────────────────────────┤
                                                          ▼
                                   L1 GoodD1 / LinkD1  (views + balance ⇒ GoodD1)
                                                          │
                     F1 FactorSoundD1 (prepD1 ok ∧ GoodD1 ⇒ RelD1a B0) ──► ExtractD1StmtT
                                                          │
 R1 renders (5 new tables, rcptV3D1, mrkV3@20) ─┐         │
 R2 FactorCompleteD1 (checkD1a ⇒ ∃ GoodD1 …) ───┼──► CompleteD1StmtT + header/aligned (FitsD1)
                                                          ▼
                                   A1 nearV3D1_admission_final (+ A2 hint codec, A3 model)
```

## 3. Items, sizes, status

Sizes are Lean lines. ✔ marks a finished item, with its measured size. Every other size is an
estimate, calibrated on the D0a counterparts (`Rcpt/` 71 k, `Render/` 75 k, `Assembly/` 96 k
lines).

| id | item | depends on | est. lines | status |
|---|---|---|---|---|
| **V0** | `Extract/AirD1`: table indices of `nearAirV3D1`; `getElem?_d1_same` (indices `< 25` other than 16 and 23 are `nearAirV3`'s); `TableLocal` from `HoldsP` | — | 90 | ✔ |
| **V1** | relay views `kib_view`, `plf_view`, `rid_view` (`TableLocal → ∃ es, Wf ∧ TableTraffic`, as `BndProof`) | — | 400 | ✔ |
| **V2** | `tx_view : TxViewStmt` (`Extract/TxView`, `TxProof`, `Tx/*`, 15 modules). One entry per 16-row op: the op constants, the flag algebra (`stage = s1 + s2`, `cand`, `wr`, gates), the written values (`mo`, `nk`), the memory times (`tp + d = op`, `d < 2^14`). Under byte hypotheses on the inputs, the seven chains give integer facts: `N > kn`, `N = kn + 1`, `N < Bd`, `amt ≥ C` / `aft = amt + dep`, the overflow and stake tests, and `okP = okC`. Reuses `RcptChain.chain`/`sumL`/`convS` | V0 | 2,190 | ✔ |
| **V3** | `akm_view : AkmViewStmt` (`Extract/AkmView`, `AkmProof`, `Akm/*`, 15 modules). Each value segment decodes (`akm_decode`: `decodeAccessKey b = some k`, nonce = the first 8 bytes, `k.perm = FullAccess ⇔ t₁`, a FullAccess value is `nonce ‖ 1`, the nonce rows are exactly offsets 0…7). Built from the borsh walk (`field`, `u32field`, `body`, `str`, `methods`, `vecMethods`, `fcPerm`, `gki`, against `Wire.pU*`/`pString`/`pVec`/`pOption`), `body_utf8` (`utf8_rows`: the class / pending-count / E0-ED-F0-F4 automaton accepts only `utf8Ok`), and exact traffic on VBYTES/AKMEM/VSLOT/BYTES/AKC | V0 | 2,656 | ✔ |
| **V4** | `RcptD1.rcptD1_view : RcptD1ViewStmt` (`D1/R/View`). The D0a receipt-view chain is copied by `scripts/rcpt_d1_copy.py` from a declaration-level taint (`scripts/RcptTaint.lean`: 428 theorems / 126 modules); 21 hand-written deltas (`scripts/rcpt_d1_overrides.lean`, `D1/R/Delta/*`). `RcptV3WfD1` / `rcptTraffic3D1` (`D1/R/ViewDefs`) carry `TOK0`, `M0`, `O0`, `T0`. Hypotheses for L1: `ExtOk pub` (extension bytes, `M0, T0 < 2^24`, `O0 < 2^30`), `ReceiptPublicRanges`, `MEM` versions ≤ 2^25 | V0 | 11.0 k generated + 1.3 k hand | ✔ (≈ 125 s serial, 131 modules) |
| **V5** | `MrkD1.mrkViewD1` (`D1/M/View`): D0a's `mrkView` for `mrkTableD1` (`maxLog 20`). Generated copies `D1/M/*` (`--profile mrk`, 47 theorems / 5 modules); the only delta is `height_le_m20` | V0 | 1.5 k | ✔ (≈ 27 s) |
| **V6** | `Extract/ViewsD1`: the ten `Assembly.ViewsV3` views (node, walk, head, val, uniq, ups, acct, akey, bnd, size) from `HoldsP nearAirV3D1` through `getElem?_d1_same`. The SHA, ChaCha, scheduler, srcp, qv and sort views enter D0a's link through `HoldsP nearAirV3`-level lemmas (L1), not through `ViewsV3` | V0 | 150 | ✔ (see log) |
| P0 | D1 public bindings: `pubOf (preparedBytesD1 p ov)` decoded. The D0a header and the nine segments keep their offsets. The extension `M0, T0, O0, TOK0` at `E0 = 322`. The six new segments: body-prefix send (cancels positions `8 … O0−1` of the D0a body receive), `TXP`, `SIG`, `PKEY`, `PLEAF`, `PRID`. `txOverhead` in `PH_WOVH`. `pubFit`. Reuses `Public/Prepared*` | — | 3–6 k | ✔ parts 1–5 (`D1/Public/Ext`, `Layout`, `Split`, `NewSegs`, `ExtPrep`, `Ranges`: `extOk_of_prepD1`, `pubCountD1_split`, `newMsgs_eq`, `preparedD1_pubFit`, `prepD1_receipt_ranges`). `PreparedBindingsD1` dropped: D0a's bundle has no consumer |
| **P1** | `txVerdict : TxVerdictStmt`, `prepLocalNative : PrepLocalNativeStmt` (+ `localApply_of_applyReceipt` with the outcome), `prepTxNative : PrepTxNativeStmt` (step simulation `prepTx_step`, `prepTxs_sim`) | — | 420 | ✔ |
| P2 | `prepD1` decomposition: `prepD1 cb h = ok p` ⇒ the D0a-shaped `prepClaimD1` facts (`walkD0`, contexts, sched), the decoded tx vectors, the T1 bound, both tx roots, `newTxs` sizes, the forwarded / compute checks, the header equalities, the RS body and `p`'s fields as functions of these | P1 | 2–4 k | parts 1–3 ✔ (`D1/Prep/Facts`, `Bounds`, `SpecDefs`/`Spec`: `prepD1_roots`, `prepD1_m0_t0`, `prepD1_leaves`, **`prepD1_spec`**: every check of `prepD1` and `p = w.prep h`) |
| L1 | `GoodD1 B cb k h p x` (the D1 analogue of `GoodV3`: D1 witness shape, transaction run, local receipts, the `MEM`/`AKMEM` timelines, the read keys ⊆ `txKeys`, A7ᴰ¹ against the AIR's sums) and `LinkD1`: views + bus balance ⇒ `GoodD1`. The D0a link modules apply unchanged wherever `rcptV3D1` reduces to D0a's traffic at `T0 = M0 = TOK0 = 0, O0 = 8`. The new parts are the tx/credit ops ↔ `processTxs` (with P1), the access-key memory and the leaf/rid/key relays | V*, P0, P2 | 10–20 k | in progress:
  * `D1/Link/Bus`, `MemBound` (`rcptD1_view_prep`);
  * `RecordsDefs` / `Records` (`linkInputsD1_of_holdsP`);
  * `GoodD1Defs` (`GoodD1Core`);
  * `Statements` (**`extractD1_of_parts`**, with A7 isolated in `A7D1Step`);
  * the generator's `link` profile: 981 constants / 11.2 k lines; **64 of 113 copies build and are
    committed** (only list), with the hand deltas `Link/Count`, `ClaimFields`, `BusUsers`,
    `PlfIds`, `ShaExtra`, `Kinds`, `Rids` (local receipt ids; `RidLRange` discharged by `ridV3`'s
    range check, `ridLRange_of`), `RidBytes`, `Keynib` (`kibD1`, `uwalks`), `RfBody`, `TxOps`, `MemEv`,
    `MemD1` (`mem_bal_d1`, `memHypA_of`), `WalkU` / `WalkProv` (`walkU` on `EDGE`/`BMAP`: `WalkBalD`,
    `BusBalD`, `edge_provided3D`), `VPost` (post streams `pnOfD1`: acct or FullAccess akm writer),
    `RunC` (`applyReceiptsC` from the ledger, `RunModelC`);
  * the generator's `walk` profile (after the a7b merge, 33 tables): 97 constants, **19 copies**
    (`D1/W`: `Walk3`, `Ups*`, `Post3OccWalk`, …) over `BusBalD` / `WalkBalD`;
    frontier (`LinkSched`: ups `DIGEST` ids vs the `plfV3` provider; `RecChain`: the run; `A7Bound`)
    and next steps in log milestone 14 / checkpoint 12.

  A7 waits on R-5 |
| F1 | `FactorSoundD1`: `prepD1 cb h = ok p ∧ GoodD1 … ⇒ checkD1a B0 cb (witnessOfV3D1 k x h) = ok ()`. Needs the D1 witness codec (`decodeStateWitnessD1 ∘ encode`, `pTxD1` round trip on the hint's raw transactions) and `applyNewChunkD1` = the tx prefix (P1) + `applyReceiptsC` over local then incoming receipts. The A7ᴰ¹ measure: the relation's main pre trie covers **all** `txKeys` (keys whose values are never read are absent, not revealed), whereas the AIR walks only the read keys, so `unfoldBytesD1 ≤` the AIR's running sums needs a monotonicity lemma for the unread keys' paths (see §5, R-2) | L1, P1, P2 | 15–30 k | ✔ 0.8 k (`D1/F1`: **`factorSoundD1_B0`**, 2026-10-21; produced by an automated prover fleet (fm5) and ported) |
| R1 | renders: `txV3`, `akmV3`, the relays, `rcptV3D1` (D0a's `HonestRcptQ` with the offsets), `mrkV3@20`; honest bus balance of the six D1 buses and of the changed MEM / MPOS / BYTES traffic | V* | 8–15 k | |
| R2 | `FactorCompleteD1`: `checkD1a B0 cb w = ok () ⇒ ∃ k h p x, GoodD1 …`, `hintOfD1`, heights at the D1a bounds (`FitsD1`: `txV3` ≤ 2^19 at NT0 + n_loc ≤ 8,192 ops, `akmV3` ≤ 2^22 by A7, `mrkV3` ≤ 2^20), `headerOk`, roll alignment | R1, P2 | 6–12 k | |
| A1 | `nearV3D1_admission_final`: `ExtractD1StmtT` + `CompleteD1StmtT` into `ZkFormal.Prover.Np.G.admission_v2H` (as `NearAdmission.nearV3_admission`) with `nearAirV3D1_npOkPg_g2`, the size bound, `NVu`, `tables_ne_nil`, profile facts | F1, R2 | 1–2 k | |
| A2 | hint wire codec: `decodeHintD1 (HintD1.encode h) = ok h`, split/join `readBorshBytes` framing (D0a's `HintCodec` pattern) | — | 0.3–0.6 k | |
| **A3** | `ModelTier.verifierD1_tier`: `npVerifierP challengeSpecD1a … = npVerifierP (challengeSpecChunk .d1a) …` (not `rfl`: the two `claimOk` matches differ in their instances, so the proof does a case split on `WfClaim.decode`); `paramsD1a_tier` (fuel, profile, cap and reduction fuel coincide); `relTier_d1a` | — | 40 | ✔ |
| | **total remaining** | | **≈ 57–125 k** | |

Calibration and reality check: the estimates for the large items (V4, L1, F1, R1, R2) are D0a's
proportions scaled by the new surface, with the design doc's assumed 2–3× over-run already
included. The finished items came in at the low end (V0 + V1 + P1 ≈ 0.9 k lines, about 5 s of
elaboration).

## 4. Statement corrections (candidate side, `D1/PrepD1Lemmas.lean`)

* **`ExtractD1Stmt` / `CompleteD1Stmt` use the tape `preparedBytesD1 p 0`, but the verifier
  (`prepD1b` = `preparedTapeD1`) uses `preparedBytesD1 p (txOverhead h)`.** With overhead 0, the
  AIR's `w.size` check (`8 MiB − OVH − Σ x ≥ 0`) does not count the hint's transaction vectors.
  The extracted witness carries them, so the phase-1 `ExtractD1Stmt` is (very likely) false: an
  accepted overhead-0 trace can extract a witness above 8 MiB, which `RelD1` rejects.
* **Decision (coordinator, 2026-10-14): accepted.** `ExtractD1StmtT` / `CompleteD1StmtT`
  (`D1/StmtsT.lean`, on the verifier's tape `preparedBytesD1 p (txOverhead h)`, completeness
  with `headerOk`) are the canonical targets. The overhead-0 drafts were removed from
  `PrepD1Lemmas.lean`; no module or tool referenced them. The `prepD1b` docstring now states
  `txOverhead`.

## 5. Risks and open questions (no spec change proposed so far)

* **R-1 (V4 volume).** D0a's receipt view is 70 k lines, and 153 files take
  `TableLocal RcptV3.table`. The six changed expressions touch the `tok` chain, the body
  offsets, the count, the MEM time with the age no-wrap, and MPOS. If the copy-and-modify
  footprint exceeds ≈ 15 k lines, the alternative is a candidate-side AIR change: keep `tableQ`
  verbatim and move the four offsets into a 1-row "prefix" table that emits the
  pre-incremented values on new buses. That is a phase-1 design revision (new
  `nearAirV3D1`, Rust prover change), so it needs the user's go-ahead, but it is not a
  spec or challenge change.
* **R-2 (A7ᴰ¹ over unread transaction keys). Superseded by R-5: the argument below is wrong (the store is hash-addressed).**
  `RelD1a`'s `unfoldBytesD1` measures the main pre trie built over **all** `txKeys` (every
  transaction's signer account and access key, read or not). The AIR walks only the keys it
  reads (phase-1 decision 7). `partialTrie` = `buildFor (mkStore values)` never fails: it
  reveals exactly the nodes that lie on some key path *and* are in the witness store, and
  leaves every other subtree as `.hash`. `processTx` reads a key only at steps 5/6, so an
  undetermined unread key is no error. For the extracted witness, whose store holds only the
  AIR-revealed nodes and values, the extra keys therefore reveal nothing new. Every store node
  is already on a read path, and a value slot is revealed only for an exact key match.
  `unfoldBytesD1` then equals the AIR's count, which is ≤ `B0`. For completeness, the honest
  witness may reveal more (nearcore records prefetched reads), so its measure is ≥ the AIR's,
  as phase 1 noted. Obligation: a `buildFor` monotonicity / "store ⊆ read paths" lemma (part
  of F1, ≈ 0.5–1.5 k lines).
* **R-4 (V4: the re-proof is ~22 k lines; the "small prefix table" fallback does not hold; decision
  requested, 2026-10-14).**
  * *Measured.* D0a's receipt view (`Assembly.RcptViewV3`) has a closure of 1,331 modules. Of
    these, **228 modules (22,454 lines)** mention `RcptV3.table` / `tableQ` / `tableR` directly,
    and every lemma there carries `hL : TableLocal RcptV3.table …`. A D1 trace satisfies
    `TableLocal RcptD1.tableQD1` instead, so the re-proof means copying that chain (≥ 22 k
    lines, mostly verbatim, with local edits). That is over the 15 k threshold.
  * *A trace transport does not rescue it.*
    * The `tok` register is byte-decomposed (`tok₁₅ ← bitsX 31 8`, carries in `xb`), so
      starting it at `TOK0` instead of `0` cannot be shifted out.
    * The deposit age needs `r + T0 − tprev < 2¹⁴`, whereas `tableQ`'s 13-bit window cannot
      hold `r + k` for `k` up to `T0 ≈ 8,192`.
  * *The verbatim-`tableQ` fallback (coordinator decision 2) needs more than a prefix table.*
    These parts are small:
    * a "virtual" rcpt header: `PH_N = n`, `PH_BURNT = burnt − TOK0`, body
      `= u32 0 ‖ encodeReceipts(incoming refunds)`; only `rcptV3` and `mrkV3` read these;
    * an `mrkV3` remap: its count read from a new `M0 + n` field, its `MPOS` positions
      shifted by `−M0`;
    * `plfV3` sending `pos − M0`.

    The memory ordering is the obstacle. `tableQ` writes accounts at `r + 1` and its readers
    accept only `tprev ∈ [r − 2¹³ + 1, r]`. So the transactions' account writes (which come
    first) would have to happen at time ≤ 0. That needs a **memory bridge**: the transaction
    ops on their own bus `MEMT`, plus a 16-rows-per-account table that receives `acctV3`'s
    time-0 value, opens the `MEMT` chain, closes it, and re-emits the post-transaction value
    at time 0 for the receipts. It also needs **per-account uniqueness** of the bridge rows:
    two bridge chains for one account would let the prover run the account twice in
    parallel, which is unsound. That is a new table with sorting or uniqueness, Rust
    prover work and a new link argument. It is not a small prefix table.
  * **Decision requested.** Either (a) V4 by copy-and-modify on the phase-1 AIR (≈ 22–30 k
    mechanical lines, no AIR change, about 2–4 % more judge elaboration), or (b) the
    bridge redesign above (AIR + prover + conformance work, plus a bridge view and a
    uniqueness proof, ≈ 3–6 k proof lines, and V5/P0/P2 change shape). The lane recommends
    (a): it is mechanical and low-risk, and (b)'s uniqueness argument is new soundness
    surface. Until you decide, the lane works only on items that are the same under both
    choices.
* **R-5 (A7ᴰ¹ over unread transaction keys is not implied by the AIR; PROPOSAL, 2026-10-15).**
  R-2's argument is wrong. It assumed that a value slot of the extracted store is revealed only
  for a key the AIR read. But `mkStore` is **hash-addressed**: `mkSlot` reveals a leaf's value
  whenever a wanted key matches the leaf exactly *and* some store entry has the value's hash,
  that is, the same bytes.
  * *Counterexample (sketch).* The main pre-state holds accounts `A` and `B` with identical
    `AccountV1` records `v` (72 bytes; plausible for equal balance, code hash and storage). The
    path of `[0]‖C` (`C` absent) ends at `B`'s leaf. The last chunk carries:
    * `t₁` from `A` (a candidate, so it reads `v`);
    * `t₂` from `B` with `tx_valid = 0`, or an invalid signature (not a candidate, never read,
      not walked: phase-1 decision 7);
    * `t₃` from `C` (a candidate; the absence walk reveals `B`'s leaf node, without a value).

    `checkD1`'s `tMain = partialTrie store root (mainKeys ++ txKeys)` wants `[0]‖B`. At `B`'s
    leaf, `storeGet (sha256 v)` finds `A`'s value, so `B`'s slot becomes `.val v`. `B` is
    never written, so the post trie keeps it too. Hence `unfoldBytesD1 = AIR's Σ + 2·72`.

    Every witness `checkD1` accepts must reveal `B`'s leaf (for `t₃`'s read) and hold `v` (for
    `t₁`'s read). So pad the state until the AIR's `Σ ∈ (B0 − 144, B0]`: the AIR accepts, and
    `RelD1a B0 cb w` fails for every `w`. **`ExtractD1StmtT` is false.**
  * *The same effect without equal values:* identical subtrees (same leaf suffix and value at
    two positions) let an unread key re-reveal store nodes off the read paths. The excess is
    not bounded by a useful constant (per key, up to a path's nodes plus a value; × ≤ 8,192
    keys), so tightening the AIR's bound (`Σ ≤ B0 − slack`) does not work.
  * **Options** (both outside this lane's authority):
    * **(A) spec, recommended.** Restate A7ᴰ¹ (`triesD1`, D1a amendment only; `RelD1` is
      unchanged): the main pre trie of the measure is built over
      `mainKeys … ++ readTxKeys`. `readTxKeys` is the signer key of every candidate (first
      occurrence, flag set, `Tx.valid`, `txCost ≠ none`), plus its access key when the signer
      account is present in the pre-state. Presence is static in D1: no transaction creates
      or deletes an account or key.

      These are exactly the AIR's walks (`prepTx`'s `walks`), so D0a's "every revealed
      occurrence lies on a walked path" argument applies. The run over the smaller trie is the
      same, because unread keys are never read (an F1 lemma). Completeness gets easier: the
      honest measure equals the AIR's count. Cost: re-sign the D1a tier of `near-chunk-v3`.
    * **(B) AIR, no spec change.** Walk **every** `txKeys` entry, including duplicates and
      flag-0 or invalid transactions, and consume present values through `VAL` in a small
      sink table, so that the AIR counts what the relation reveals. Cost: a new table (FINAL
      / VBYTES sink), a `PKEY` segment over all keys, Rust prover and conformance changes, a
      new view and ≈ 1–2 k proof lines, and up to 8,192 more walks.
  * Until a decision, the lane works only on the parts that are the same under both options
    (L1 plumbing, the R1 renders). `GoodD1.unfoldedBytes` and F1's A7 part are on hold.
* **R-5 → (B) (user decision 2026-10-15): design note.** The signed spec is unchanged.
  `nearAirV3D1` must count exactly what `checkD1`'s main pre trie
  `partialTrie store root (mainKeys ++ txKeys)` and its post trie reveal.

  The relation reveals a node occurrence iff its key path passes through it **and** its hash is
  in the store. It reveals a leaf value iff a wanted key matches the leaf exactly **and** the
  value's hash is in the store. The store is every node and value record (hash-addressed;
  `x.store`). The AIR must therefore decide store membership by hash, in both directions.

  1. **Walk every `txKeys` entry.** For every transaction of the witness, including duplicates,
     flag-0, invalid and cost-overflow transactions, walk the signer key and the access key.
     * `prepD1` emits `PKEY` records for all `2·|txs|` keys. The walk ids of the unread ones
       get their own range `W_UNR + j`.
     * The candidates' walks are unchanged. Walks of an equal key share occurrences, as D0a's
       repeated receiver walks do.
  2. **A new walk terminal "stub".** Every unread walk ends at one of:
     * an absent key (leaf/ext mismatch or empty branch slot): as today;
     * a present leaf whose key matches exactly;
     * a child hash `h` that is **not in the store**. The relation then stops there with
       `.hash h`.

     The candidates' walks never take the stub: their reads need the full path.
  3. **Non-membership from `uniqV3`.** `uniqV3` already sorts every store entry (node records
     and value records) by `(τ, digest)`, non-strictly. A D1 extension `uniqD1` (replacing table
     6, as `rcptV3D1` replaces 16) answers `NMEM (τ, h)`. Two consecutive segments with
     `digest_{t−1} < h < digest_t` consume the query, as do the first and last segments of the
     instance for the boundary cases. The strict comparison reuses the segment's byte-serial
     subtractor. The stub terminal and the absent-value case (step 4) send `NMEM`.
  4. **A value sink `uvalV3` (new table).** For every distinct present-leaf occurrence reached
     only by unread keys, exactly one of:
     * the value is in the store: a `VAL` occurrence record `vid` (one row per byte, counted by
       `valA7`'s running sum like every value occurrence) whose digest is the leaf's value
       hash, consumed through `FINAL (w, τ, 0, vid)`;
     * the value is not in the store: `NMEM (τ, value hash)`.

     Occurrence-level dedup: the sink receives `LEAFOCC (nid)` once per leaf node record (the
     node record is the occurrence), so several unread keys reaching one leaf reveal its value
     once. The candidates' reads already make their leaves' values revealed, and the sink skips
     those leaves (flag `rd` on the node record).
  5. **A7.** Node occurrences on unread paths are ordinary node records, already in `nodeA7`'s
     running sum. Revealed unread values are ordinary value records, already in `valA7`'s
     running sum. The post trie keeps them, because unread keys are never written. So
     `sizeA7`'s `u` equals `unfoldBytesD1` exactly, with no new accounting row.
  6. **Duplicates and identical values** are handled by construction:
     * "revealed iff hash in store" is decided per occurrence (steps 3–4), never per key;
     * equal-hash entries are byte-equal (`uniqV3`'s `DUP` copy), so the revealed bytes are the
       store's.

     This covers the R-5 counterexample: `B`'s leaf (reached by `t₃`'s absence walk, and now
     also by `B`'s own unread walk) takes the sink's first case, with a value record equal to
     `A`'s value.

  Costs:
  * ≤ 8,192 extra walks at NT0 = 4,096, i.e. ≤ 8,192 · (key nibbles + 1) walk rows (about 1.2 M
    rows for 64-byte account ids);
  * `uniqD1` +1 bus;
  * `uvalV3` ≤ 8,192 segments, plus the value rows it reveals.

  Lean: tables `uniqD1`, `uvalV3`, the walk terminal, the `PKEY` range, `prepD1` (all keys),
  the views, and **`A7D1Step`** (exact count). Rust: `v3d1prove` walks, `NMEM` witnesses, the
  sink. Conformance: bus balance, Lean = Rust, the bound mutants, the R-5 fixture.

  Open questions:
  * whether the walk table can end at a stub child with no node record (it needs a `NMEM`
    send on the parent's child slot);
  * the honest witness (nearcore) may hold an unread key's value, so the sink's first case must
    be available to the honest prover from `w` alone (it is: the value is in `w.main.values`).
* **R-3 (budget).** The D0a closure is 5,953 s single-core (after the elab-budget lane) of the
  judge's 14,400 s. The D1 closure adds the D1 modules. The modules so far take < 1.3 s each.
  The V2–V4 and R1 module families are kept < 60 s per module.

## 6. Milestone log (summary; details in the log)

| date | milestone | theorems | modules (elab, s) |
|---|---|---|---|
| 2026-10-14 | V0, V1, P1 | `tableLocalD1`, `getElem?_d1_same`, `kib_view`, `plf_view`, `rid_view`, `txVerdict`, `prepLocalNative` (+ `localApply_of_applyReceipt`), `prepTxNative` (+ `prepTx_step`, `prepTxs_sim`) | 7 modules, each ≤ 1.2 s |
| 2026-10-14 | V3 | `akm_view` (+ `akm_decode`, `body_utf8`, `utf8_rows`, `str`, `vecMethods`, `fcPerm`, `gki`) | 15 modules, Σ ≈ 22 s (max `Akm.Decode` 3.4 s) |
| 2026-10-14 | V6, A3, V3 part 1 | `nodeViewD1` … `sizeViewD1` (10), `verifierD1_tier`, `paramsD1a_tier`, `AkmProof.segInfo` | 3 modules, each ≤ 0.6 s |
| 2026-10-14 | P0 (4), P2 (1–2) | `newMsgs_eq`, `preparedD1_pubFit`, `prepD1_roots`, `prepD1_m0_t0`, `prepD1_leaves`, `extOk_of_prepD1` | 4 modules (max `Prep.Bounds` ≈ 48 s) |
| 2026-10-14 | V5, P0 (1–3) | `mrkViewD1`; `extOk_prepared`, `m0V/t0V/o0V/tok0V_prepared`, `descriptorD1_msgs`, `pubMsgsD1_split`, `pubCountD1_split` | 7 + 3 modules |
| 2026-10-14 | V4 | `rcptD1_view`, `rcptV3D1_view_nearAir` (+ `traffic_shift`, `chainByteMsgs_eq_viewG`, `tok_first`, `o2_first`, `count_last`, `age_row`, `local_K`, `memD1`) | 131 modules, ≈ 125 s serial (max `CharClass` 27 s) |
| 2026-10-15 | P0 (5), P2 (3), L1 (start) | `prepD1_receipt_ranges`, `prepD1_spec`, `sender_of_recv`, `tx_op_lt`, `rcptD1_mem_bound`, `rcptD1_view_prep`; **R-5 PROPOSAL** (A7ᴰ¹ not implied) | 5 modules, each ≤ 6 s |
| 2026-10-14 | V2 | `tx_view : TxViewStmt` (+ `chainN/B/C/T/Q/D/S`, `zN_iff`, `msum_val`, `debit_arith`, `credit_arith`, `verdict_debit/credit`, `opWf`, `rowLane`) | 15 modules, Σ ≈ 25 s (max `Tx.OpWf` 5.1 s) |

## 7. V4: copy-and-modify plan (coordinator decision (a), 2026-10-14) — done

**As built (checkpoint 4, log milestone 5).** The declaration-level taint is 428 theorems in 126 modules, not the module-level 564. Copies keep their **original namespace** and are named `N_d1`, so that name resolution in a copy is the original's; a copy imports only modules already in its original's import closure. The hypothesis is the bundle `LocalD1` (`TableLocal rcptK ∧ ExtOk`). The rest of this section is the plan as written before the build.

**What must be copied (measured).** Inside the closure of `Assembly.RcptViewV3` (1,325 modules),
93 modules mention the receipt table directly (`TableLocal RcptV3.table`, `tableQ`, `tableR`,
`ReceiptCandidateRouting.candidateTable`). Their forward import taint is **564 modules, 45,294
lines**: 93 under `Rcpt/` and 471 under `Assembly/`.

The mapping D0a module → D1 copy (`ZkFormal.NearV3.D1.R.<suffix>`) is in
`docs/zk-formal/v3-d1-v4-map.tsv`. That list is an upper bound. Many `Assembly` modules import
a tainted module only for unrelated declarations, so the generator must taint at
**declaration** level: copy a declaration only when its type or value refers, transitively, to
a tainted constant. The expected result is well below the module-level bound. The 22,454 lines
of the 228 directly-mentioning modules are the practical lower bound.

**Generator (to build; `zk-formal/scripts/`).**
1. A Lean metaprogram (as `scripts/TypeHashes.lean`) walks the `RcptViewV3` closure. It marks
   as tainted every constant whose type or value mentions `RcptV3.table`, `tableQ`, `tableR`,
   `candidateTable` or the view statement `RcptV3ViewStmt`, and propagates the mark.
2. Source copy, per tainted declaration, using the declaration ranges (the model-split lane's
   `DeclInfo` technique):
   * each copy goes into `D1/R/<module>.lean` under the namespace `ZkFormal.NearV3.D1.R.<orig ns>`;
   * every reference to a tainted constant is rewritten to its copy;
   * untainted references stay fully qualified to the D0a original, so originals and copies
     never clash;
   * `TableLocal RcptV3.table` becomes `TableLocal RcptD1.tableQD1` (the constraints
     themselves: through a membership-transport lemma; see below).
3. Constraint membership: one lemma
   `memD1 : e ∈ RcptV3.table.constraints → e ∉ changed → e ∈ RcptD1.tableQD1.constraints`
   (`replC` is the identity off `substC`, a decidable fact). Copied proofs that use an
   unchanged constraint go through it. Only the proofs that touch one of the six changed
   expressions fail. Those are rewritten **by hand into small dedicated delta lemmas**:
   * `D1/R/Delta/Tok`: the first-row `tok = TOK0` and the token totals;
   * `Delta/Body`: `o2 = O0` and the body offsets;
   * `Delta/Count`: `r + rowE + M0 = PH_N`;
   * `Delta/Mem`: the MEM write time `r + 1 + T0`;
   * `Delta/Age14`: the 14-bit deposit age, `xb52…65`;
   * `Delta/Mpos`: the leaf position `r + M0`.

   A later refactor could then re-unify the two chains by parameterising over the offsets.
4. The view statement `RcptV3D1ViewStmt` is `RcptV3ViewStmt` with `rcptTraffic3` using the D1
   times and positions, and `RcptV3Wf` with `toks.head = TOK0`, `count + M0 = PH_N`, body
   offsets from `O0`.

**Elaboration estimate.** D0a's mean is 2.2 s per module, so the module-level upper bound of
564 copies is ≈ 1,240 s serial. The declaration-level copy is expected at ≈ 400–900 s. Judge
estimate for the D1a certificate closure:

| part | estimate (s, serial) |
|---|---|
| D0a closure (shared; elab-budget figure) | 5,953 |
| D1 phase-2 modules so far (V0–V3, P1, A3), ≈ 50 modules | ≈ 70 |
| V4 copies | ≈ 400–1,240 |
| V5 + P0 + P2 + L1 + F1 + R1 + R2 + A1/A2 (≈ 600–1,000 modules at 1–3 s) | ≈ 1,000–2,500 |
| **total** | ≈ 7,400–9,800 of the 14,400 budget (51–68 %) |

This assumes the D0a assembly roots that D1 does not use are dropped from the D1 closure.
