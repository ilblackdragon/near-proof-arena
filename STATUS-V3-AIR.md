# STATUS-V3-AIR: succinct v3 D0 prover (np-udr-stark-v2), program state at hand-over

Program lead's hand-over, 2026-10-07.

**Resumption, 2026-10-07:** `lake build ZkFormal` at `399af714` passed (694 jobs)
under the 16 GiB `heavy` wrapper on CPUs 8–15,24–31. This was an incremental
build using cached artifacts, not a clean elaboration-budget measurement.
The receipt lane was interrupted by a usage limit, not paused by the user;
its outstanding work remains on the active critical path. Its saved branch was
actually unmerged at handover; it is now merged at `8c40110e`. Main already contains
the D0a spec merge (`5ce7c42e`). These facts supersede the stale merge/pause
instructions below. The domain choices in §5 remain unresolved.

The default root does **not** check all merged v3 work: the import-graph audit
found 339 unreached modules before the receipt merge. New target
`lake build ZkFormal.V3.Integration` adds 369 previously unreached proof modules
including the receipts (executable drivers and compiler fast paths remain their
own targets). Its full incremental build passes all 1,089 jobs. Root success alone must not
be reported as integration success. Seven guarded axiom checks pass.

The expanded gate found a stale synthetic upsV3 width: 186 instead of 187.
The corrected kernel size bounds increase by 928 bytes per group; g2 is
7,147,423 bytes, plus up to 1,295,017 hint bytes (53,832 over 8 MiB). This
is still a synthetic 23-table model with one SHA and no qvV3, not the final
assembled proof. All six trie, five scheduler and six receipt shapes now
match their actual tables in kernel checks for g ∈ {1,2,3}. These numbers
supersede the older size summaries below. Evidence and exact source hashes:
`docs/e2e-results/v3-integration/report.json`.

The conditional `lane_770k_22` row-count theorem and `laneMaxes_770k` compile:
at W = 770,000 and T ≤ 33 the conservative ChaCha bound is 4,141,411 rows with
padding. This fits 2^22, but exceeds the current `Chacha.Table.maxLog = 21`.
The existing W = 360,000 theorem remains unchanged. No new domain conjunct or
table-height change has been made; 770,000 would require updating the table,
its completeness bounds and size accounting before assembly.

**Alignment milestone:** the integration target now passes 1,092 jobs. New
`Size.Aligned` proves the smaller opening bound for the actual verifier
schedule under `RollAligned`; `rollAligned_of_layout` states the sufficient
condition on actual LDE heights. `Size.HonestAdmission` requires the size bound
only on honest trace headers, retaining all adversarial soundness and query
obligations. This makes honest-prover padding usable without imposing an
unproved property on every verifier-admissible header.

`Size.AlignedModel` kernel-checks 6,164,160 bytes for the proposed padded
24-table/two-SHA model at g=2. With the 1,295,017-byte hint, 929,431 bytes remain
under 8 MiB. This still omits qvV3 and does not construct padded traces or
change actual table caps. Final padding correctness, multiplicity/security
bounds, missing tables and assembly remain required. Six guarded axiom audits
pass. See `docs/e2e-results/v3-alignment/report.json`.

**Padding milestone:** `Size.PadHeader` now proves that rounding required logs
into {1,4,7,…,22} yields `RollAligned`, and provides an assembly criterion on
`trHdr` using each table's actual log. `NearV3.Render.Padded` constructs
array-backed aligned generators for head, value, boundary and access-key,
with closed proofs of local constraints, full traffic preservation and the
log residue. The head generator uses proposed cap 13 (was 11);
`head_view_at` proves its soundness view for caps up to 22. Existing table
constants and minimum-height interfaces remain unchanged. The other three
fit their existing caps. Integration passes 1,094 jobs, seven new axiom
guards and all six prior alignment guards. Evidence:
`docs/e2e-results/v3-padding/report.json`. Remaining tables and the assembled
HoldsP proof are still required; four completed generators do not establish
padding for the final prover.

Program goal: a succinct STARK for `RelD0a B0` (v3 chunk validation, domain D0a), formally admitted to the unified challenge `near-chunk-v3` with declared tier D0a.

Design: `docs/zk-formal/V3-D0-DESIGN.md`. §10–§16 are the review decisions, §12 the SHA kind registry, §13/§15/§16 the size accounting.

Rules that apply to everyone:
* No `sorry`, `axiom` or `native_decide`. Axioms must stay within {propext, Classical.choice, Quot.sound}.
* Run every heavy command as `HEAVY_MEM=16G taskset -c 8-15,24-31 /data/illia/nearproof-deps/bin/heavy …`, one at a time.
* Never edit v1 code, or files pinned by a signed challenge.
* Every lane keeps an unconstrained-cells register in its STATUS file.

## 1. Branches

Each lane has a worktree `/data/illia/nearproof-wt/<lane>`. Heads are as of hand-over; see §8 for the final heads.

| branch | worktree | content | state |
|---|---|---|---|
| `lane/v3-air` | v3-air | integration branch: saved receipt lane merged; `ZkFormal.V3.Integration` builds; helper WIP remains separate | integration |
| `lane/v3-bus` | v3-bus | np-udr-stark-v2: public-message bus (`AirP`, `HoldsP`, `PubSeg`, `verifierP`), `rbrWithP`, `stark_romSound_fullP`, `npIopCompleteP`, `admission_v2`, P1 `sizeMaxSched`, toy `toyP_admission` | **proved**, merged |
| `lane/v3-p2` | v3-p2 | `auxGroup` g ∈ {1,2,3} for v2: `rbrWithPg`, `stark_romSound_fullPg`, `npIopCompletePg`, `admission_v2_pg`, `toyP_admission_g3`. The Rust `AUX_GROUP` change is documented only. | **proved** (Lean), merged |
| `lane/v3-store` | v3-store | trie store semantics: `storeBuildStmt`, `trieOpsStmt`, `absent_iff`, `upsert_absent` | **proved**, merged. Its A6-based completeness was superseded by v3-trie (`treeRecs_spec`). |
| `lane/v3-spec` | v3-spec | NearSpecV3 additive: `RelD0a`/`checkD0a` (A1, A2, canon0f, A7 `unfoldBytes ≤ B`, A8), `relD0a_iff`, `relD0a_relD0`, `relD0a_mono`, `InD0a`/`relD0a_iff_in`, `B0 = 2,000,000`, `ChallengeD0a`, `PrepD0` (`prepD0`, `Hint`, `SchedPub`, `run_eq_core`, `convertRequests_eq_raw`), oracle/v3-d0a, D0a difftest, witness encoder `encodeWitness_roundtrip`/`encodeWitness_normal`, refund codec `pRefund_encode`/`decodeBody_outgoing`, `@[csimp]` fast paths | **proved/tested**. The B0 = 2.0 MB edits were finished at wrap-up (§6). |
| `lane/v3-d0a-spec` | v3-d0a-spec | clean main-merge branch carrying only the spec-side D0a files | **see §6** |
| `lane/v3-trie` (+ helper `lane/v3-trie-h`) | v3-trie, v3-trie-h | trie tables `nodeV3`, `headV3`, `valV3`, `walkV3`, `uniqV3`, `upsV3`; views; renders (all but upsV3); link: `root_tau`, `build_tau`, `walks_tau`, `store_hashFunctional`, `post_tau`, `post_sets_tau`, `root_chain`/`ups_chain`, `upsV3_linkB`, `upsV3_s0f` | soundness **proved**; upsV3 render (M7d) **partial** |
| `lane/v3-chacha` | v3-chacha | `chachaV3`, `genV3`, `shufV3`: block, stream, genIndex and shuffle contracts plus completeness (`chacha_complete`, `gen_complete`, `shuffle_complete`) | **proved**, merged |
| `lane/v3-sched` (+ helper `lane/v3-sched-h`) | v3-sched, v3-sched-h | in-AIR bandwidth scheduler (`schV3`, `sprV3`, `ssdV3`, `smmV3`, `scpV3`, 781 W_eq). M1 `core_compose`; M3 `schedCore_sound''`, `codec_schedVal`, `schedCore_fwd_prep`, `Granted` (`core_granted`), `PubIdx`, `KindReg`; M4 `cmp_complete`, `mem_complete`, `heights`, `steps_pv86`, `lp_draws`, `worstK_exceeds` | soundness **proved**; completeness **partial** (M4) |
| `lane/v3-rcpt` (+ helper `lane/v3-rcpt-h`) | v3-rcpt, v3-rcpt-h | receipt side: `rcptV3` (431), `acctV3`, `akeyV3`, `bndV3`, `srcpV3`, `sizeV3` (867 W_eq). Proved: views and renders of acct/akey/bnd/size; `body_eq`, `body_sha0`, `rcpt_keynib_syms`, `srec_ee`/`srec_neq`, `lex_lo`/`lex_hi`, `rcptShaRows_A1` | **partial**, active; merged at `8c40110e`. The helper's srcp WIP is committed as `WIP:` 4ae51a13. |
| `lane/v3-size` | v3-size | lever (a): `multiproof_size_le`, `size32D`, `sizeBoundD_le_dedup`, `sizeMaxDedup_le_sched`, `admission_v2_dedup`, `sizeMaxDedup_eq_model`, `V3.v3_bound`, kernel evaluations | **proved**, merged |

## 2. Soundness picture: open hypotheses and how each is discharged

The target is `Holds_v2(prep cb h) ⇒ ∃ w, RelD0 cb w`. The assembly additionally uses `relD0a_relD0` for the tier lift. Hypotheses still open on proved theorems:

| hypothesis | where | discharge |
|---|---|---|
| bus ownership (`SchedOwn`, `ScanOwn`, `OpOwn`, `CodecValOwn`, `SparOwn`, `PubbOwn`, `InitOwn`, `SdlOwn`, `PubbRecv`, `ShaOwn`, `SdlxOwn`, trie bus ownership) | sched, trie | decide on the final assembled AIR (`decide +kernel`) |
| `PubIdx` (public records = rendered prep records: SPAR, SPUBB, SDL, SRC, BND, body …) | sched, rcpt | instantiate once the **indexed public segments** protocol extension (R1) exists. **Not started.** |
| `KindReg` (SHA kind separation; sched `ShaKind`, trie `othersId`/`othersU`) | sched, trie | per-table proofs from each view against the registry (design §12) at assembly. Trie TODO: restate `othersId` through `KindReg.avoid`. |
| `SchedVal` | trie `upsV3_linkB` | `codec_schedVal` (sched) at assembly |
| `KeynibOk` (key-nibble providers send only nibbles/END) | trie walks | rcpt `rcpt_keynib_syms` (provider side, proved) plus public walks at assembly |
| `VPostOk`, `vpostLen`, `hpl`, `hperm` (account writes ↔ trie tw windows) | trie `post_tau`, upsV3 | rcpt `acctV3` (VSLOT bijection, R3 implemented in nodeV3) |
| `ShaHyp` / `ShaFacts` (per SHA table instance) | trie, rcpt | L5 `sha_digest_contract_closed` per instance |
| `prepD0 cb h = .ok p` plus prep facts | sched | the verifier runs prepD0 natively; lemmas `prepD0_sched`, `prepD0_rawOk`, `prepD0_seed`, `prepD0_ids`, `prepD0_fwd_lt` are proved |
| global id-range disjointness (all SHA ids, all kinds) | assembly | one global lemma (design §12) |
| rcpt links: lists ⇒ `verifyReceiptProof`, run ⇒ `applyReceipts`/`applySystemReceipt`, R5 `inIntervals_iff_shardOf` | rcpt | **not done** (receipt work remains active) |

## 3. Completeness: what is open

* **Trie:**
  * every view and render is done except the upsV3 render;
  * M7d: 2 of 10 constraint groups done (cSeg, cDigest), plus cBool in progress on the helper; about 3k lines left.
* **Scheduler (M4):**
  * done: cmp and mem;
  * left: sprV3 (in progress), ssdV3, schV3, then `schedCore_complete`;
  * heights: `lane_22` is proved, conditional on the ChaCha-words bound `hW` (§5).
* **ChaCha:** complete.
* **Receipt side:** rcptV3 view about 40 % done; rcptV3 and srcpV3 renders not done; `qvV3` (queue-value parsers) not started; `mrkV3`/`sortV3` copies not done.
* **Assembly (not started):**
  1. the full `nearAirV3` value;
  2. `FactorSound`/`FactorComplete` against `checkD0`, with `buildFor` = `treeOf` via store lemmas;
  3. `honestTrace_fits` under A1/A7/A8 and W;
  4. `admission_v2_dedup` instantiation.

## 4. Size cap (formal 8 MiB = 8,388,608 B)

* **Lever (a), proved:** the dedup bound `sizeMaxDedup` is 4,134,191 B on nearAir, against 5,473,967 B with P1.
* **v3 synthetic AIR** (23 tables, ONE SHA table, `qvV3` not counted): 7,450,143 B (g=1), **7,146,495 B (g=2)**, 7,193,567 B (g=3).
* **Hint `B` maximum:** 8 + 4481 · 289 = **1,295,017 B**. This corrects the design's 0.91 MB; the spec lane is to confirm it.
* **Margin** at g = 2 with one SHA table: **−52,904 B**, and ≈ −150 KB once `qvV3` is counted.
* **B0 = 2.0 MB (user-approved) does not fit one SHA table:** ≈ 31.7 k rows over 2²² (`single_2M_fails`). So **two SHA tables** stay, which adds +704 W_eq ≈ +0.65 MB.
* **The cap can only be met with lever (1), roll-in alignment.** The honest prover pads table heights so FRI roll-ins land on committed layers. That is about −1.62 MB; the expected result is ≈ 6.8 MB + B including two SHA tables. The conditional schedule/size theorem is now proved; honest-trace padding and final accounting remain.
* Other levers: a compact refund codec (≈ −0.45 MB of B), and width cuts (928 B per base column).

## 5. Decisions pending (user / coordinator)

1. **Size cap:** retain B0 = 2.0 MB and 8 MiB. Implement honest-trace padding for the now-proved conditional roll-in alignment bound with two SHA tables.
2. **ChaCha words bound W:** a new execution-level conjunct of `RelD0a`, "Σ ChaCha words drawn by all scheduler runs ≤ W".
   * Why it is needed: the formal worst case (`worstK_exceeds`: genV3 ≈ 9.9 M rows, chachaV3 ≈ 53 M rows) exceeds 2²².
   * Options: W = 360,000 (≈ 16 % over twice the worst-case expectation) or W = 770,000 (the 2²² limit).
   * It is not a deterministic nearcore invariant: rejections depend on hash outputs. The liveness note is the same as A7's.
   * If approved, it should go into `RelD0a` **before** `lane/v3-d0a-spec` freezes.
3. **Receipt lane:** active after a usage-limit interruption, not a user pause.
   * The saved work is merged; continue the remaining view/render/link proofs.
   * Required implementation work includes edits to `spec/lean/v3/NearSpecV3/PrepD0.lean` (R2: header fields `|B|`, witness overhead, per-list and routing records)? PrepD0 is unsigned and is NOT part of the d0a-spec branch.
4. **Source-proof path length:** RelD0a allows unbounded Merkle paths (`rootFromPath`); nearcore produces ⌈log₂ shards⌉. Options: a domain conjunct, or count path bytes into a budget. srcp heights are kept parametric in `Dp`.
5. A8 is **decided**: it is in RelD0a (nearcore-enforced, `congestion_control.rs:503-523`, `validate.rs:280-298`), with difftest 0 disagreements and 845/845 mutants out of domain.

## 6. `lane/v3-d0a-spec` (RelD0a for near-chunk-v3) and main

* Contents: the spec-side files only.
  * `ChunkValidationV0a` with `B0 = 2000000`, `inD0a`/`InD0a`/`InD0a0`, `relD0a_iff_in`, `relD0a_relD0`;
  * `ChallengeD0a` and `spec/near-chunk-validation-v0a.md`;
  * `oracle/v3-d0a` and the D0a Python tools, public-d0a fixtures and difftest report.
* It must be rebased onto current main (832549c6 or later), show only `A` entries, build, and have the D0a difftest and boundary tests rerun at B0 = 2.0 MB.
* The D3 lane (agent adc6aa5fe4a25279e) needs the bytes-level `RelD0a B0`, `relD0a_relD0` and `InD0a`/`relD0a_iff_in`. It waits for the merge commit before it re-freezes and signs near-chunk-v3.
* State at hand-over: see §8.

## 7. Remaining work, in order (estimates)

1. Merge `lane/v3-d0a-spec` to main and notify the D3 lane. Small.
2. Decisions §5.1–§5.4.
3. Receipt lane, resumed: the rcptV3 view (≈ 60 % left), renders for rcptV3/srcpV3, `qvV3`, links to `applyReceipts`/`verifyReceiptProof`, R2/R5/R6. ≈ 10–15 k lines.
4. Indexed public segments (R1, v2 protocol): instantiate `PubIdx`. ≈ 1.5–3 k lines.
5. Trie M7d (upsV3 render, ≈ 3 k lines) and the KindReg restatement.
6. Scheduler M4: sprV3, ssdV3, schV3, `schedCore_complete`. ≈ 4–6 k lines.
7. Size: lever (1) roll-in alignment (≈ 0.5 k lines plus prover padding), then the final `nearV3_size` at the chosen g.
8. Assembly: `nearAirV3`, the KindReg/ownership/id proofs, `FactorSound`/`FactorComplete` against `checkD0`/`RelD0a`, `honestTrace_fits`, admission certificate, verifier UNSUPPORTED interface for near-chunk-v3. ≈ 8–12 k lines.
9. Rust prover v2: v2 bus, auxGroup parameter, every v3 table generator, hints, prep mirror. ≈ 10–15 k Rust.
10. Real checker run and judge-verify timing.

Elaboration budget risk: v1 alone is 647 s of the 1,800 s budget. The v3 additions are large (copied L3/prover ≈ 9 k lines, the trie ≈ 25 k+, the scheduler ≈ 15 k+), so measure early.

## 8. Final heads at hand-over

| branch | head | worktree |
|---|---|---|
| `lane/v3-bus` | ba97293b  | /data/illia/nearproof-wt/v3-bus |
| `lane/v3-p2` | b559e433  | /data/illia/nearproof-wt/v3-p2 |
| `lane/v3-store` | af88b6b0  | /data/illia/nearproof-wt/v3-store |
| `lane/v3-spec` | 4fd2f4ad  | /data/illia/nearproof-wt/v3-spec |
| `lane/v3-d0a-spec` | 5ce7c42e  | /data/illia/nearproof-wt/v3-d0a-spec |
| `lane/v3-trie` | 2e2bad36  | /data/illia/nearproof-wt/v3-trie |
| `lane/v3-trie-h` | 1d8b2f12  | /data/illia/nearproof-wt/v3-trie-h |
| `lane/v3-chacha` | 6db8ea9b  | /data/illia/nearproof-wt/v3-chacha |
| `lane/v3-sched` | e77002ac  | /data/illia/nearproof-wt/v3-sched |
| `lane/v3-sched-h` | e77002ac  | /data/illia/nearproof-wt/v3-sched-h |
| `lane/v3-rcpt` | fad713e5  | /data/illia/nearproof-wt/v3-rcpt |
| `lane/v3-rcpt-h` | 4ae51a13  | /data/illia/nearproof-wt/v3-rcpt-h |
| `lane/v3-size` | 578e5c04  | /data/illia/nearproof-wt/v3-size |

`lane/v3-air` is the commit carrying this file. It merges the final heads of v3-sched (e77002ac), v3-trie (2e2bad36) and v3-spec (4fd2f4ad), plus all earlier lanes. Every lane built at its own head. The integration branch was **not rebuilt in full** after the last three merges: run `lake build ZkFormal` (heavy + taskset) first thing.

WIP commits that do **not** build:
* `lane/v3-trie-h` 1d8b2f12: `Render/Ups/GPlan.lean`. Nothing imports it, and it is not merged.
* `lane/v3-rcpt-h` 4ae51a13: the srcp view, unverified, not merged.

**`lane/v3-d0a-spec` = 5ce7c42e is READY to merge to main.**
* Based on main 832549c6; `git diff --name-status main` gives 931 A, 0 M/D.
* `lake build NearSpecV3.ChunkValidationV0a NearSpecV3.ChallengeD0a` succeeds, and so does the oracle/v3-d0a cargo build.
* Tests at B0 = 2 MB:
  * full D0a difftest: 11,616 cases, 0 disagreements;
  * public-d0a: 303 cases, 0 disagreements (deterministic);
  * A7 boundary: 245/245 and 64/64;
  * honest amendment violations: 0, except A1 on the 1500-Tgas chain by design.
* Theorems relD0a_iff, relD0a_iff_inD0a, relD0a_iff_in, relD0a_relD0, relD0a_mono and WfClaim.relD0a_rel/domainD0a_domain use only {propext, Quot.sound}.
* Caveats:
  * the committed full report predates an A2-mutant determinism fix; rerun difftest_v3_d0a to refresh;
  * no constructed case near 2.0 MB yet;
  * the challenge draft JSON is not regenerated (run spec/tools/build_challenge_draft_v3_stark.py after merging, if wanted).
* After the merge: send the merge commit to the D3 lane (agent adc6aa5fe4a25279e) so it can add tier d0a, re-freeze and sign near-chunk-v3.
* **Note:** if W (§5.2) is approved, it changes RelD0a. Decide whether it goes in before this merge (re-freeze once) or as a later D0a revision.

Scheduler wrap-up specifics:
* Heights take prepD0, A7 and a per-instance `Replay`; Gen.run → Replay is still to prove.
* `lane_22`/`lane_prep` are conditional on W = 360,000.
* SchedTablesTest was rerun after the clog2 change: 600/600, 48/48. The SchedFullTest rerun is incomplete; its last full pass predates the clog2 change.

Trie wrap-up specifics:
* M7d groups done: cSeg, cDigest, cWalk, cRows/cConst, cBool.
* Open: cPlan (WIP), cFields, cBytes, cMem (≈ 2 k lines).
