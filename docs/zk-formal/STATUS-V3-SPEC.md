# STATUS — lane `v3-spec` (D0a statement, `prepD0`, witness encoder, native verify time)

Branch `lane/v3-spec`, 2026-10-06. Inputs: `V3-D0-DESIGN.md` §1, §2, §4, §6, §10, §11.
Labels: **proved** (closed Lean theorem, axioms ⊆ {propext, Classical.choice, Quot.sound},
no `sorry`/`native_decide`), **tested** (executable comparison, counts below), **measured**
(this host, CPUs 8–15/24–31, shared with other lanes; numbers vary ≈ ±30 % with load).

Governance: `near-chunk-validation-d0-1` (signed) pins the NearSpecV3 tree, the D0 spec doc,
`oracle/v3` and the public fixtures. Everything here is **additive**: no existing file under
`spec/lean`, `formal-core`, `oracle/v3`, `oracle/fixtures/v3/public`, `oracle/tools/spec_check_v3.py`,
`oracle/tools/difftest_v3.py` or the D0 drafts is changed (checked against main `e837025`).

## 1. Statement: `RelD0a` (amendments A1, A2, Canon0f)

* `NearSpecV3.ChunkValidationV0a` (new): `RelD0a cb w := RelD0 cb w ∧ a1 cb ∧ a2 cb w ∧ canon0f cb w`;
  executable `checkD0a`; `relD0a_iff : RelD0a cb w ↔ checkD0a cb w = .ok ()` (**proved**).
* `NearSpecV3.ChallengeD0a` (new): `challengeSpecD0a` (`Rel = RelD0a c.encode w`),
  `challengeParamsD0a` (`maxProofBytes = 8388608`), `relD0a_relD0` (**proved**).
* Doc: `spec/near-chunk-validation-v0a.md` (A1/A2/Canon0f with nearcore 2.13.4 source checks).
  Canon0f: the only runtime writer of `0x0f` is `run_bandwidth_scheduler` →
  `update_scheduler_state` (`scheduler.rs:548-562`, `iter_links` sender-major `:427-435`, every
  link present after `increase_allowances` `:323-336`; `mod.rs:118-135`), under
  `shard_layout(apply_state.epoch_id)` (`mod.rs:72`); in a single-epoch D0 segment every value
  read was written in `epoch_id` (or is absent), so every honest D0 witness satisfies it.
* Draft: `challenges/drafts/near-chunk-validation-d0-stark.draft.json`
  (builder `spec/tools/build_challenge_draft_v3_stark.py`): `#D0a`, relation
  `NearSpecV3.RelD0a`, restrictions + `c.gas_limit`, `w.proof_routing`, `e.sched_canonical`,
  `resource_limits.max_proof_bytes = formal_params.max_proof_bytes = 8388608`; workload
  generators and public fixtures as D0 (all 78 `arena-public` positives are `RelD0a`:
  `nearspec-v3-check-d0a` accepts 78/78, **tested**).

### 1.1 Differential test (tested)

`oracle/tools/difftest_v3_d0a.py`: nearcore oracle `near-arena-oracle-v3-d0a` (oracle/v3
modules shared unmodified via `#[path]`; `src/d0a.rs` classifies A1/A2/Canon0f on nearcore
objects) vs Lean `nearspec-v3-check-d0a` (compiled `checkD0a`) vs Python
`spec_check_v3_d0a.py` (D0 checker unmodified + independent amendment checks).

| set | cases | d0 (accept) | ood | mutants (accepted / A2) | disagreements |
|---|---|---|---|---|---|
| full, seed 4243, 9 chains × 120 blocks (`spec/difftest-report-v3-d0a.json`) | 10 771 | 907 | 2 131 (269 with `c.gas_limit`) | 7 733 (1 176 / 592) | **0** |
| public `oracle/fixtures/v3/public-d0a` (2 × 40) | 244 | 64 | 59 | 121 (16 / 43) | **0** |

* A2 holds on every honest witness: `w.proof_routing` violations **0 / 4 597** honest
  witnesses (nearcore `Receipt::receiver_shard_id`, every receipt of every source proof);
  Canon0f violations **0 / 4 597**; `c.gas_limit` 599 (exactly chain 8, 1500 Tgas); the 10 Tgas
  chain stays in D0a.
* A2 mutant `w.foreign_routed_receipt` (valid Merkle path, chain re-hashed; `Rel` by
  construction): 592/592 `out_of_domain` in Lean and Python.

## 2. `prepD0` (claim/hint side of the verifier) — `NearSpecV3.PrepD0` (new)

Per §11 (c): `Hint = {n, refunds}` (wire form `n`, `B = u32 0 ‖ encodeReceipts refunds`);
`prepClaim cb` (claim-only) and `prepBody pc h` (`{n, B}` part), `prepD0 = prepClaim >>= prepBody`;
`Prep` = header, applied-order source lists `(key, from_shard, root)`, own routing intervals,
per applied block `Scheduler.SchedPub` (ids, params, link-allowed matrix, converted
requests, seed, `sha256(all_shards)`), `B`, `fwd` = per-shard refund byte totals to check
against the AIR's grants; `Prep.encode`; `hintOf cb w`.

* **Scheduler split (proved):** `Scheduler.run_eq_core : run cfg cc ids prev cong req seed =
  (pubOf cfg cc ids cong req seed).bind (runCore · prev)` — the in-AIR scheduler is specified
  by `runCore` on public `SchedPub` and the decoded previous state.
* **Forwarding split (tested):** all refunds forward ⇔ native gas-only simulation ∧ every
  refund's shard has a status ∧ `Σ sizes to s ≤ grant(own, s)` (AIR).
* **Routing intervals (tested):** `inIntervals (ownIntervals L own) a ↔ L.shardOf a = own`.
* **Test** `nearspec-v3-test-prep` (zk-formal tools, with the fast paths) on the full D0a set
  + public-d0a (11 015 cases): every `RelD0a` case (2 163) has `prepD0 cb (hintOf cb w) = ok`
  and **all** prepared values equal the relation's execution (applied receipts rebuilt from
  the lists hash to `applied_receipts_hash`, paths, `n`, gas, roots, outcome root, burnt, body;
  `runCore(pub_τ, v_τ)` writes exactly the `0x0f` value in each post trie; `fwd ≤ grants`;
  intervals vs `shardOf` on every receipt): **2 163 / 2 163**. Claim/hint-class failures 3 470:
  `prepD0` fails in the same category on 3 462 (same message 3 425); the other 8 are honest
  `e.forwarded` cases whose size part is the AIR's (the hint's refunds stop at the buffered
  receipt, so a later native header check fails). Witness-class failures: 5 382 (no
  requirement). 0 problems.

## 3. Witness encoder — `ZkFormal.V3.EncodeWitness` (candidate side, zk-formal)

`encodeChunkInner`, `encodeEntry`, `encodeTransition (= encTr)`, `encodeSW`, `encodeWitnessFile`,
`D0Shape`; prefix lemmas `pReceipt_encode`, `pChunkInner_encode`, `pEntry_encode`,
`pTransition_encode`, `pChunkHeader_encode`, …; **proved**:
`encodeWitness_roundtrip : EncodeWitnessStmt` (decode ∘ encode), `encodeWitness_normal :
EncodeWitnessNormalStmt` (`D0Shape s → normW K R s = s → decodeStateWitness (encodeSW s) = .ok s ∧
normSW K R (encodeSW s) = .ok (encodeSW s)`, reusing the reference's `normSW`/`normW`/`sig0`/
`zeros8`/`encTr` and lemmas via `lean_lib ReexecV3D0`), `normalW_encodeWitnessFile`.
Tested (`nearspec-v3-test-encw`): round trip on every decodable case (public + full);
re-encoded `normW` of every `RelD0` witness is `normalW`, `checkD0`-accepted and byte-equal to
the reference normaliser's output (64 + 16 public, 907 + 1 768 full). Open: `checkD0` on the
normal form is tested, not proved (needs `D0Shape (normW …)` and the length bound).

## 4. Native verify time (measured)

Fast paths (candidate side, `zk-formal/ZkFormal/V3/Fast/*`, every redirection a kernel-checked
`@[csimp]` lemma; spec functions unchanged): `NearSpec.sha256` → `sha256Fast`, `merkleRoot`;
header chain (`blockHash`, `decodeBlockV6`, `chunkHash`, `slotLeaf`, `merklizeBorsh`,
`outgoingReceiptsRoot`, `decodeBlk`); GF(2⁸) multiplication by a table built from `gfMul`
(`gfMul_eq_T`) and the RS matrix functions; RS parity on arrays (`encodeParts_eq_fast`);
`partsMerkleRoot`, `encodedMerkleRoot`; `prepClaim`/`prepBody`/`prepD0`/`schedPub`. Axioms of all
lemmas ⊆ {propext, Classical.choice, Quot.sound} (`ZkFormal/V3/Tools/Axioms.lean`).
Scheduler runtime fast paths dropped (§11: the scheduler core is in-AIR).

Per component (ms; `nearspec-v3-bench`):

| component | public D0a fixtures (mean / max of 64) | full D0a d0 (mean of 907; max total) | synthetic 64 shards / 32 blocks (31 applied blocks, full requests, RS (33,100)) — before → after | RS 900 KB body |
|---|---|---|---|---|
| claim decode + header chain | 0.34 | 0.40 | 1 483 → **108** | — |
| shuffles | 0.04 | 0.04 | 0.2 → 0.2 | — |
| congestion (f64, statuses, outGas) | 0.06 | 0.07 | 15 → 15 | — |
| scheduler public data (`schedPub`) | 0.08 | 0.08 | (run: 2 991) → **430** for 31 pubs | — |
| Reed–Solomon (`RSCode.new` + encode + merkle) | 4.0 | 4.1 | 277 → **42** | (33,100): 2 548 → **380**; (85,256): 6 690 → **682** (matrix 2 461 → 165) |
| outgoing-receipts root | 0.03 | 0.03 | 0.5 | 4 481 refunds / 64 shards: 517 → **58** |
| **`prepD0` total** | **4.8 / 15.4** | **4.9; max 40** | 7 911 → **380** | — |

* "before" = the spec's List code with only the (reverted) A5 import; "after" = fast paths.
  `sha256` of 1 MiB: 1 358 → 17 ms.
* **Typical** native part ≈ 5 ms (≪ the STARK's ≈ 1 s). **Worst** native part (64 shards,
  32 blocks, A1-maximal 0.91 MB body at (85,256), 4 481 refunds) ≈ 0.38 + 0.68 + 0.06 ≈ **1.1 s**.
* **Open (size of the public statement):** `Prep.encode` of the synthetic worst case is
  **41 MB** (31 `SchedPub` × 4 032 converted requests × ≤ 40 increases as u64), and encoding it
  takes ≈ 3–4 s. Suggested for the `v3-sched` lane: publish each request as its raw 5-byte
  bitmap plus the per-block 40-entry `requestValues` table and convert in-AIR (≈ 36 KB per
  block), or u32 increases (½ size). Not changed here pending the lead's choice.

## 5. Open items

1. `Prep.encode` size in the scheduler-heavy worst case (§4).
2. The wire form of the hint: parsing `B` back into refunds needs a refund-receipt parser
   (`pReceipt` rejects implicit-account receivers, which refunds may have) — the verifier lane's.
3. Forwarding split and routing intervals: tested, not proved.
4. Two used source chunks with equal `chunk_hash` share one entry (AIR must enforce equal lists).
5. `checkD0` acceptance of the normal-form re-encoding: tested, not proved.

## 6. Commits

`c22b0ce` (superseded, reverted by `e525aac`: in-place A1/A2/A5), `152ccc2` (merge main),
merge `lane/v3-air` (§11), `3651e2f` (RelD0a, prepD0 per §11, fast paths, tools, encoder),
`6c46fe3` (oracle/v3-d0a, Python D0a checker, difftests, fixtures, v0a doc, ChallengeD0a,
draft builder), and the commit adding this file and the draft JSON.
