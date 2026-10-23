# A formally admitted STARK for v3 D2 (all non-WASM actions, queues, epoch boundaries): design

Status: **design phase**, 2026-10-23.  No decisions taken; §3 lists what the user must decide.
Statement: `spec/near-chunk-validation-d2.md`, `NearSpecV3.RelD2`
(`spec/lean/v3/NearSpecV3/ChunkValidationD2.lean`, `D2/*.lean` — 3,990 lines); tier
`challengeParamsChunk .d2` of `near-chunk-v3` (classes `d2-actions`, `d2-queues`, `d2-epoch`).
Builds on `V3-D0-DESIGN.md` (the C/H/W split, §1; the native verifier `prepD0`, §2) and
`V3-D1-DESIGN.md` (the two-table-delta method, §2.2, and the effort calibration, §6).
Companion design: `V3-D3-DESIGN.md` (WASM execution; D3 = D2 + WASM).

Labels: **measured** (run in this repo), **estimated** (arithmetic from a stated model),
**PROPOSAL** (a relation, spec, challenge or protocol change: **the user decides**; nothing in this
document changes any of them).

---

## 0. Summary and decisions requested

**Finding 1: there is no D2 AIR, and no design document for one, until this file.** `grep -rn
'nearAirV3D2\|nearTablesD2'` returns zero hits repo-wide. D0a has an AIR and a certificate; D1 has
an AIR (`nearAirV3D1`, 33 tables) and `pq_d1_rel`; D2 has the *relation* (proved, kernel-checked,
52 249-case difftest agreement) and **no AIR at all**. Every claim below about D2 therefore starts
from a real relation but zero arithmetization.

**Finding 2: `RelTier .d2 = RelD2` is unbounded — D2 cannot be made complete as it stands.**
`ChallengeChunkV3.lean:60` maps tier `.d2` to `RelD2` with no amendments. `RelD2` carries none of
D0a's amendments (`a1` gas-limit, `a2` routing, `canon0f` scheduler canonicality, `a7` unfolded
bytes, `a8` bandwidth duplicates, `a9` ChaCha words, `a10` path depth, `a12` layout) and no bound
on the receipt count: delayed receipts are popped in a loop with no cap, and a failed action burns
0 gas, so an 8 MiB witness can carry an unbounded action list. This is the identical defect
Finding 1 of `V3-D1-DESIGN.md` records for D1, and it has the identical cure: a **bounded tier
`D2a`** (§3, PROPOSAL P-D2-1). Note D1a exists and D2 does not; the ladder is `D1a ⊂ D1`, and
`D2 ⊇ D1` with no `D2a`.

**Finding 3: much of D2 is class H, not W, and that is what makes it tractable.** Reusing the
C/H/W split: the *queue arithmetic* (congestion limits, receipt-group push/pop, bandwidth-request
generation, delayed-queue index deltas) is a deterministic function of claim facts plus a small
hint. D0a already establishes the pattern for an H computation: `schedStep` runs the scheduler
natively and the AIR proves only that the read value is `s₀` and the written value is `out₀`
(digest-bound). The D2 analogue is the same shape and is the single largest saving in this design.

| | **D2-N** (recommended) | **D2-S** (in-AIR queues) |
|---|---|---|
| queue arithmetic | native (`prepD2`, spec functions) | in-AIR, new tables |
| new AIR tables (est.) | 5–7 | 14–20 |
| receipt-count bound needed | yes (§3) | yes, and tighter |
| formal effort (est.) | 55–110 k lines | +60–120 k on top |
| fits the judge budget | **only with extraction** (§6.3) | no |

**Decisions requested (PROPOSALS; the user decides):**

| id | question | proposal |
|---|---|---|
| **P-D2-1** | Bounded tier | `RelD2a := RelD2 ∧ a1 ∧ a2D2 ∧ canon0fD2 ∧ a7D2 B ∧ a8 ∧ a9D2 W ∧ a10D2 Dp ∧ a12 ∧ t2 NT2 ∧ tDel DR2`, in new files, plus `Tier.d2a` at rank 4 (shifting `.d2` to 5). `RelD2` unchanged. |
| **P-D2-2** | Queue arithmetic location | Native (`D2-N`), exactly as D0a's `schedStep`. The AIR proves the key/value digest binding only. |
| **P-D2-3** | `NT2` (receipt bound) | `|receipts processed| ≤ NT2 = 8,192`. Honest maximum needs measuring (§5.2); this is a domain bound, costing liveness only. |
| **P-D2-4** | `DR2` (delayed-queue pop bound) | `≤ DR2 = 8,192` pops per chunk. Same reasoning. |
| **P-D2-5** | Corpus before air | Extend the D2 oracle corpus with the receipt-count/congestion distributions needed to fix `NT2`/`DR2` empirically rather than by guess. |
| **P-D2-6** | Native prep location | `prepD2` candidate-side (zk-formal), as P-D1-6 decided for `prepD1`. |

---

## 1. What `RelD2` requires beyond `RelD1a`: gap list

`RelD2` is `InD1` weakened plus new state. The D1a AIR covers trie reads/writes, the access-key
decode, nonce/balance comparisons, refunds, and the receipt credits. D2 adds, per
`spec/near-chunk-validation-d2.md`:

| # | area | spec § | what it adds over D1 | class (C/H/W) |
|---|---|---|---|---|
| G1 | Delayed receipts | §9.1 | `DelayedReceiptIndices` load; push and pop, two encodings; per-pop state read of the receipt | H (indices) + W (values) |
| G2 | Receipt sink / forwarding | §9.2 | `BufferedReceiptIndices` + per-shard `Meta`; `tryFwd`, `bufferReceipt`, `forwardOrBuffer`; instant receipts | H (limits) + W (metadata writes) |
| G3 | Receipt groups | §9.3 | `groupsPushBack` / `groupsPopBack` / `metaPushed` / `metaPopped`; `Meta` codec | H (arithmetic) + W (encode) |
| G4 | Bandwidth requests | §9.3 | `allowed_shard` finalization; requests generated from outgoing buffers; header comparison | C (claim) + H |
| G5 | Congestion info | §9.4, §10.1 | `own_congestion_info`; sink info + delayed deltas; `validator_update` matching | C + H |
| G6 | Yield timeouts | §9.4 | `PromiseYieldIndices` read/write; timeout receipts enqueued | H + W |
| G7 | Nine non-FC actions | §7.1–7.9 | CreateAccount, DeployContract, Transfer, Stake, AddKey, DeleteKey, gas-key pair, DeleteAccount, instant DeleteAccount | W (state) |
| G8 | Delegate / DelegateV2 | §8 | nested action list, permission checks, nonce and gas-key nonce | W + C |
| G9 | Multi-action receipts | §6.4 | action loop with commit/rollback points and per-action AR merge | W |
| G10 | Refund receipts | §6.5 | system-predecessor refunds, gas-key and allowance refunds, deposit burns | C + W |
| G11 | Multi-epoch segments | §11 | `epochs` table, `same_layout`, per-epoch PV 86, `epoch_start_after` | C |
| G12 | `ValidatorAccountsUpdate` | §10.2 | stake_info filtering, rewards, `locked`/`return` arithmetic, treasury | H (filter) + W (writes) |
| G13 | Missing chunk | §10.3 | implicit transition with only steps 1–3 | C + H |
| G14 | `InD2` conditions | §12 | `c.same_layout`, `w.size` (two conjuncts), `w.shape`, `e.wasm`, `e.secp` | C/W as in D0a |
| G15 | Trie: delete + squash + prefix | §3.4 | `PTrie.del` with squash; `prefixKeys` — already proved in the spec (`TrieProps.lean`) but **not yet arithmetized** | W |

**G15 is the deepest single item.** D1 never deletes a trie key in the main transition in a way
that needs squash; D2's `DeleteAccount` / `ContractData` removal / `finalize` do. The spec proves
the *semantics* (`find_del`, `del_false`, `prefixKeys_sound/complete`) but the AIR must show the
squashed shape is the one the node table renders. That is new table work, not new mathematics.

---

## 2. Architecture for D2-N

### 2.1 Verifier pipeline

Identical in shape to D0a's (§2.1 of `V3-D0-DESIGN.md`):

```
verify(pub, cb, pb):
  guard:  claimOk cb
  split:  pb = hintBytes ‖ π
  prep:   p ← prepD2 cb (decodeHint2 hintBytes)      -- native, spec functions
  stark:  Stark.verifier Fp Fp8 nearAirV3D2 prmV2 (cb' := Prep2.encode p) π
```

`prepD2` runs every C and H check, computes the `InD2` out-of-domain conditions decidable from
`(c, h)`, and emits `cb'`: a fixed header plus public-bus segments (applied-order source lists,
own boundaries, the hint body `B`, fixed-key walks, value digests, `ROOT` endpoints). The D2
additions to `cb'` are the queue-state digests (§2.3) and the receipt-list commitment.

### 2.2 New and changed AIR pieces (`nearAirV3D2` = `nearAirV3D1` + delta)

Following the D1 method (reuse every unchanged table, patch only what moves):

| piece | change | why |
|---|---|---|
| the unaffected D1 tables — both SHA instances, the trie tables other than `node`, ChaCha ×3, scheduler ×5, `acctV3`, `akeyV3`, `bndV3`, `srcpV3`, `qvV3`, `sortV3`, `txV3`, `akmV3` | **verbatim** | their definitions do not change; per-table view/render theorems carry over |
| `nodeD1` → `nodeD2` | squash-aware | G15 |
| `mrkTableD1` → `mrkD2` | multi-epoch instance count | G11 |
| new `delqV3` | delayed-queue index + receipt stream | G1 |
| new `sinkV3` | buffered indices + per-shard `Meta` + groups | G2, G3 |
| new `del` (Delegation) | nested action list + permission | G8 |
| new `vbw` (bandwidth) or public segments | requests + `allowed_shard` | G4, G5 |
| `rcptV3D1` → `rcptV3D2` | multi-action merge, refunds, gas-key | G9, G10 |

**Estimated net new tables: 5–7** (P-D2-2 keeps the queue *arithmetic* native, so only the
key/value binding tables are new).

### 2.3 Why the queue arithmetic can stay native

D0a's `schedStep` is the precedent and it is *proved*: the verifier runs `Scheduler.run` natively
on hint `s₀`, obtaining `out₀` and the grants; the AIR then proves only that the trie read at
`0x0f` returns `s₀` and the write stores `out₀`, both digest-bound. The queue operations are
structurally identical — a deterministic total function of (claim facts, current queue state,
receipt bytes) whose *inputs and outputs are trie values*. So:

* `prepD2` computes `groupsPushBack`, `groupsPopBack`, `metaPushed`, `metaPopped`, `tryFwd`,
  `bufferReceipt`, `forwardOrBuffer`, and the delayed-queue index deltas natively;
* the AIR proves the reads and writes at the queue keys, with `(len, sha256 v)` as public data;
* `canon0fD2` (the scheduler-canonicality amendment) and the new group-canonicality condition are
  the domain conditions that make the native computation single-valued.

**The risk this carries** is the same one D0a accepted: a bug in the native queue function is a
soundness bug, mitigated only by the difftest corpus. It is not zero-risk, and it is the main
technical argument against D2-N that a reviewer should weigh against the 60–120 k lines D2-S costs.

### 2.4 Why the receipt list needs a commitment

D1's receipts are bound by `mrk`/`rcpt` over a fixed arity. D2's receipt list is data-dependent
(delayed pops, forwarding, multi-action). Without a commitment the AIR cannot know which receipts
the native queue arithmetic saw. The proposal is a `rcpt`-emitted ledger over the processed
receipts, hashed to a public digest that `prepD2` also computes — the same shape as D0a's `B`
bound by `stream_eq_of_count`.

---

## 3. `D2a` tier (PROPOSAL)

`RelD2a := RelD2 ∧` the D0a amendments restated for the D2 decoder and run `∧ t2 NT2 ∧ tDel DR2`.

Restatement matters: `a2`/`a7`/`a9`/`a10` are written over the D0 witness walker; D1 needed
`a2D1`/`a7D1`/`a9D1`/`a10D1` analogues. D2 needs the same treatment over `decodeWitnessFile`'s D2
branch. `a1`, `a8`, `a12` are claim-only and are reused as-is.

`Tier.d2a` at rank 4 requires **shifting `.d2` to rank 5**, which changes `Tier.rank` for an
existing tier. That is a governance decision (PROPOSAL), not a technical one; the alternative is
rank 4 with a tie, which `Tier.rank` is not designed for.

Liveness cost of `NT2`/`DR2`: measured in §5.2.

---

## 4. Cost model

### 4.1 What the corpus already measures (**measured**, `spec/near-chunk-validation-d2.md` §15)

The D2 oracle corpus (seed 6262, 52 249 cases, every verdict from nearcore) reports the honest-case
coverage needed to size the tables:

| workload | cases | note for table sizing |
|---|---|---|
| multi-epoch segments | 1 009 | `mrkD2` instance count must reach the segment length |
| `ValidatorAccountsUpdate` | 501 (433 main) | new `stake_info` filtering pass |
| outgoing buffers | 1 932 (96 with bandwidth requests) | `sinkV3` |
| delayed queue | 1 221 (24 376 receipts popped) | `delqV3`; **mean 20, max unknown** |
| yield queue | 6 445 | `PromiseYieldIndices` writes |
| postponed receipts | 888 | — |
| instant receipts | 175 | G2 |
| contract-data removals | 71 | G15 squash |
| implicit transitions | 960 | G13 |

**The corpus does not currently report the maxima** this design needs (`max receipts in one chunk`,
`max delayed pops`, `max groups per shard`). That is P-D2-5, and it is the cheapest way to avoid
choosing `NT2` by guess.

### 4.2 Rows at the proposed bounds (**estimated**)

With `NT2 = DR2 = 8,192` and `B = B0 = 2,000,000` (no new SHA rows), the row counts are dominated by
the existing fixed 2²² tables exactly as D1's §5.2 shows. The delta is:
* `delqV3`: ≤ `NT2 + DR2` rows in the worst case (one per pop plus index update);
* `sinkV3`: ≤ 2·`NR` where `NR` = number of receipt groups touched;
* `del`: ≤ `NT2` rows;
* `nodeD2` squash: no extra rows, but the first-row offset changes (as `rcptV3D1` did).

---

## 5. Formal effort

### 5.1 What D1a's AIR gives for free

Per `V3-D1-DESIGN.md` §6.1 the framework is *per table*: `TableLocal → ∃ v, Wf v ∧
TableTraffic`; a trace-free link; `FactorSound`; render for completeness. Every table whose
definition is unchanged keeps its view and render theorems verbatim. For D2 that is every table in §2.2's unchanged row —
which is why the estimate below is not D2's full semantic surface.

### 5.2 New obligations (D2-N)

| module group | content | est. Lean lines | risk |
|---|---|---|---|
| spec (`ChunkValidationD2a`, `PrepD2`/`hintOfD2`, `Tier.d2a`, `t2`, `tDel`) | amendment restatements, executable checks, iff lemmas, `relD2a_relD2` | 3–6 k | low |
| `FactorSoundD2` (the big one) | `processReceipts` split into native queue steps and AIR receipt steps; delayed/local/incoming + instant interleaving; `applyReceiptsC` ordering; the D2 witness codec round trip; `MEM`/`AKMEM`/`DELQ`/`SINK` interleaving lemmas | 20–40 k | **high** — the D2 analogue of D0a's `V1 factor`, larger (more receipt kinds) |
| `delqV3` view + render | delayed-queue index codec, push/pop, two encodings | 6–12 k | medium |
| `sinkV3` view + render | `Meta` codec, groups push/pop, per-shard metadata | 8–14 k | medium |
| `del` view + render | nested action list, permission checks, gas-key nonce | 5–10 k | medium |
| `nodeD2` squash | re-prove only the first-row lemmas + affected traffic (as `rcptV3D1` did) | 4–8 k | medium |
| `rcptV3D2` | multi-action merge, refunds, gas-key credits | 6–12 k | medium |
| public segments D2 | receipt-ledger commitment `bindPreparedD2`, queue digests, `pubFit`, size | 3–6 k | low-medium |
| link + assembly | `GoodD2`, `LinkD2`, `ExtractD2Stmt`, `CompleteD2Stmt`, heights, `nearAirV3D2` wf/npOk/size, admission | 12–24 k | medium |
| **total D2-N** | | **≈ 65–130 k** | |

Calibration: D1-N was estimated at 45–90 k for a **two-table** delta; `NearV3/` is ≈ 450 k lines.
D2 changes or adds 5–7 tables, replaces the receipt factor, and adds squash. A 2–3× over-run is
already implicit in the range above; treat the upper end as the planning number.

### 5.3 Judge budget — **the binding constraint**

`runners/formal-checker/src/pipeline.rs` `Limits::default`: **4 h elaboration**, 1 h/module,
2 h/recheck-run, 4 h recheck total.

* D0a's packaged closure: 3 964 modules, 8 734 s = **2.43 h of 4 h**.
* D1a projection (`V3-D1-DESIGN.md` §6.3): **2.8–3.5 h**, "fits, but with little margin, and a
  judge VM slower than this host would erase it."
* D2 adds 65–130 k lines over D1a on the same per-table architecture. At D0a's mean of 2.2 s per
  module, ≈ 1 000–2 000 new modules is **+0.6–1.2 h**, landing at **3.4–4.7 h**.

**Therefore D2 does not fit the 4 h budget as a straight extension of the D1a certificate.**
This is a design-level finding, not a scheduling detail, and it must be answered before the
per-table work starts. Three options, in increasing order of ambition:

1. **Split the certificate.** Two admitted statements (`D2a` over non-queue chunks; a second over
   queue chunks) each under 4 h. Costs: two challenge statements, and `Tier` gains a rung pair.
2. **Coarsen the proof.** Merge the queue tables into one wider table, reducing module count at the
   cost of proof size. This is how D0a's `rcpt` absorbed nine receipt kinds.
3. **Native-extract more.** Move the receipt-list structural checks into `prepD2` and prove only
   digests in-AIR — the D1-N method taken further. Cheapest in judge time, most exposed to the
   native-bug risk of §2.3.

**Recommendation: option 3 first, measured; fall back to 1 if it does not close the gap.** Option 3
is the only one that does not increase the number of admitted statements, and it is a continuation
of a decision the user has already taken twice (P-D1-2, P-D1-6).

### 5.4 Separate tier proof vs one combined AIR

The D1 design (§6.4) already discusses this. D2 inherits the answer: one combined AIR
`nearAirV3D2` in which the D2 part is empty for D1/D0 chunks, because `D2 ⊇ D1 ⊇ D0` and the
tables are appended. This keeps one certificate and one admission statement.

---

## 6. Plan

Sequential, because each step gates the next.

| step | deliverable | gate |
|---|---|---|
| **L0** | corpus maxima: `max receipts/chunk`, `max delayed pops`, `max groups/shard`, `max multi-action receipts` (P-D2-5) | numbers exist to fix `NT2`/`DR2` |
| **L1** | `D2a` spec + `Tier.d2a` + `relD2a_relD2` (no AIR) | `lake build` green, kernel non-vacuity on the D2 corpus |
| **L2** | `prepD2` + `FactorSoundD2` skeleton: the native/AIR split stated as `Prop`s, each named | compiles, each `def … : Prop`, **no** claim of proof |
| **L3** | the three new tables (`delqV3`, `sinkV3`, `del`) view+render | per-table, independently reviewable |
| **L4** | `nodeD2` squash + `rcptV3D2` delta | first-row lemmas local |
| **L5** | link + assembly + admission | `nearV3D2_admission_final` |
| **L6** | budget measurement on a real judge-shaped run | fits 4 h, or option 1/2 |

L0 is cheap and should be done first: it is the only step whose output changes the design.

### Risks

* **Native queue bug** (§2.3) — the D2-N soundness exposure. Mitigation: corpus at scale, and
  keep the queue functions *identical* to the spec's, not reimplementations.
* **Squash in the node table** (G15) — genuinely new table work; if it forces a wide change to
  `node`, L4 could cost 2–3× the estimate.
* **Judge budget** (§5.3) — the most likely reason the plan changes shape mid-way.
* **`NT2` too small** — a liveness regression on real traffic, not a soundness bug. Fix by
  re-measuring, which is why L0 comes first.

---

## 7. What this document does not claim

* No D2 AIR exists; no line of `nearAirV3D2` is written.
* No `D2a` tier exists.
* All effort figures are **estimated** from the D1 calibration, not measured.
* The `w.size` argument that keeps `RecordedStorageExceeded` unreachable is inherited from
  `spec/near-chunk-validation-d3.md` §10 and is marked **[unverified]** there for the
  contract-storage-removal case; it applies to D2 too.
