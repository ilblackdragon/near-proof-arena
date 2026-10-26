# Real shard-split fixtures (W11)

These are validator-generated state witnesses that cross a **real shard-layout boundary**, produced by
the pinned nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4, PV86). Each case is in the
usual corpus format (`claim.bin`, `witness.bin`, `meta.json`). `meta.json` records the cold
validator's verdict, the boundary shape and nearcore's own pre-validated implicit transitions. The
generator is `reshard` in `oracle/v3-successor/src/reshard.rs`. No signed source
(`oracle/v3-d3/src/**`, `challenges/**`) was changed.

## How the split is produced

At PV86, a layout change without a protocol-version change is **dynamic resharding**.
`ProtocolFeature::DynamicResharding` is stable at 85 (`core/primitives-core/src/version.rs:564,575`).
nearcore requires a static layout for the genesis epoch
(`chain/epoch-manager/src/genesis.rs:64-69`), so the chain is built the way the pinned
`resharding_v3` test builds it (`test-loop-tests/src/tests/resharding_v3.rs:516-545`):

* the genesis runs PV85 with a static 4-shard V2 layout (`ShardLayout::multi_shard_custom`, the D3
  generator's layout);
* every client votes PV86, which is the binary's `PROTOCOL_VERSION`. Voting is immediate for a local
  chain id;
* the PV86 epoch config is the same config with `ShardLayoutConfig::Dynamic`. Its settings are
  `force_split_shards = [shard of s{k}a00]`, thresholds `u64::MAX`,
  `max_number_of_shards = 5` and `min_epochs_between_resharding = 1`.

Everything after that is nearcore's own path. In the first PV86 epoch N, the parent's chunk producer
computes `proposed_split` (`find_trie_split` on the memtrie) for the chunks that may close the epoch.
The last block carries `shard_split`, and `finalize_epoch` derives the V3 layout of epoch N+2. At the
last block of N+1, `ReshardingManager::split_shard` builds both children from the parent memtrie.
The runtimes load memtries for tracked shards. The first chunks of the children are validated with
`ImplicitTransitionParams::Resharding`. The boundary account `find_trie_split` chose is `s0ctr-0`
for seed 11 and `s2ctr-0` for seed 23.

**Protocol versions.** Witnesses from the PV85 epochs are generated, but they are excluded from
every count below (`shape = pv85`). Every evaluated claim references only PV86 epochs: the split is
decided in epoch N and the layout changes at N+2, so a boundary claim spans N+1 and N+2. A *static*
split (a V2 layout change at a PV85→PV86 boundary) would make the first child chunk's main
transition run under PV85. Those witnesses were not produced and remain out of domain
(`c.pv86`, and `c.layout` for a V2 layout change).

## Generation

```
bash oracle/scripts/link-nearcore.sh
CARGO_TARGET_DIR=/tmp/lean-global-oracle-target cargo build --release \
  --manifest-path oracle/v3-successor/Cargo.toml          # rustc 1.96.0
for c in 0 1 2; do
  near-arena-oracle-v3-successor reshard --seed 11 --chains 1 --first-chain $c --blocks 80 --out fa$c
  near-arena-oracle-v3-successor reshard --seed 23 --split-k 2 --chains 1 --first-chain $c --blocks 80 --out fb$c
done
```

The defaults are 4 shards, epoch length 12, a 60 Tgas chunk gas limit, `--p-missing 0.05` and
`--p-burst-hot 0.5`. Chain `i` runs variant `i % 3`:

* 0 is plain;
* 1 drops the parent's chunk in the resharding block;
* 2 drops both children's chunks in the first block after it.

While the split is scheduled, every shard bursts transfers into a sink shard. The sink then bursts
into the parent. This produces delayed receipts, outgoing buffers and buffered gas at the boundary.
Runs are deterministic: two independent runs of seed 11 gave identical shapes, congestion values and
mutant sets.

| artifact | sha256 |
|---|---|
| generator binary `near-arena-oracle-v3-successor` | `23c373d76ef1ba618f827924b98db5a03784a9a67da12c6770f9b18c92edc621` |
| Lean checker `nearspec-v3-check-successor` (this branch) | `bfcaaf5216d57a652b85b1587520bc16087cf2334c7c5f5e9203c023b3027dc7` |

The raw runs contain 1,933 honest witnesses (6 chains). All of them were accepted by the cold
validator. 1,087 are PV86 and 846 are PV85. The raw runs also contain 86 independently judged
mutants. The PV86 witnesses fall into these shapes:

| shape | meaning | count |
|---|---|---|
| `split.left` / `split.right` | child's first chunk(s); the witness contains a `Resharding` transition | 6 / 6 |
| `cross_layout.no_split` | segment spans both layouts, no split transition (non-split shards, children's later chunks) | 48 |
| `gate.proposed_split` | split-gate fact present; header carries `proposed_split = Some(..)` | 13 |
| `gate.no_split` | split-gate fact present; no split proposed | 92 |
| `pre_split` | epoch whose next layout differs | 247 |
| `plain` | all other PV86 chunks (including post-split V3 epochs) | 675 |

## Committed cases

`cases/` holds 38 small cases: 20 honest and 18 mutants. `cases/index.json` gives each case's
origin, shape, nearcore verdict, implicit transitions, congestion, outgoing-receipt count and file
hashes. `cases.txt` lists them.

**Boundary chunks.** Every split boundary of the six chains is listed below. `(c)` means the case is
committed.

| seed/chain | resharding block → first child block | left child | right child | implicit transitions |
|---|---|---|---|---|
| 11/0 | 10072 → 10073 | s4 `00-h10073-s4` (c) | s5 `00-h10073-s5` (c) | split |
| 11/1 | 10060 → 10061 | s4 `01-h10061-s4` | s5 `01-h10062-s5` (c) | old(parent), split[, old(child)] |
| 11/2 | 10060 → 10061 (child chunks missing) | s4 `02-h10062-s4` | s5 `02-h10062-s5` | split, old(child) |
| 23/0 | 10060 → 10061 | s4 `00-h10061-s4` (c) | s5 `00-h10061-s5` | split |
| 23/1 | 10060 → 10061 | s4 `01-h10061-s4` (c) | s5 `01-h10061-s5` (c) | old(parent), split |
| 23/2 | 10060 → 10061 (child chunks missing) | s4 `02-h10062-s4` (c) | s5 `02-h10062-s5` (c) | split, old(child) |

The committed boundary cases cover the following:

* **Both retention directions with nonempty state and receipts.**
  * Seed 11/0 left inherits 400 Tgas of buffered gas and 231 Tgas of delayed gas.
  * Seed 11/0 right has the buffered gas subtracted (0) and keeps the delayed gas.
  * Seed 23/2 left has 57 Tgas buffered.
  * Seed 23/0 left's main transition produced 253 outgoing receipts. They are reassigned to the
    lowest-id child.
  * 23/1 and 11/1 have the parent's chunk missing at the resharding block.
* **Non-split shards' first chunks after the boundary**: `seed11-00-h10073-s0` and
  `seed11-01-h10062-s2`.
* **The left child's second chunk**, whose segment still reaches the resharding block:
  `seed11-01-h10062-s4`.
* **A non-split shard forwarding its outgoing buffer to the split parent**: `seed23-01-h10062-s3`.
* **Forced-split gate chunks with the recomputed `proposed_split`**, gate chunks without a split
  (also after the split, at `max_number_of_shards`), post-split V3 epochs, and an epoch before the
  split.

**Mutants.** All of these are rejected by the cold validator or, for claim facts, by claim
discipline:

* `w.split_child_post_root`: the split transition's post-state root is flipped (left and right).
* `c.child_layout_is_parent`: the child epoch's claimed layout is replaced by the parent layout.
* `c.child_layout_boundary_s2a00`: the child layout is derived with another boundary account.
* `h.proposed_split_none` and `h.proposed_split_left_memory`: the forced split is removed or its
  memory is changed.
* `h.proposed_split_forged`: a split is forged on a non-forced shard.

Each header mutant is re-signed, following nearcore's
`shard_split_validation.rs:96-121` construction. The raw runs also contain a dropped-parent-node
mutant per child; it is not committed.

## Lean results

Results for the committed cases, from `replay/verdicts-*.jsonl` and `replay/verdicts-summary.json`.
Each row compares the Lean verdict with nearcore's verdict:

| tier | agree |
|---|---|
| `resharding` | 38/38 |
| `allFeatures` | 38/38 |

The full raw corpus (1,087 honest PV86 witnesses and 86 mutants) gives these results:

| tier | honest accept | honest out of domain | mutants rejected |
|---|---|---|---|
| `allFeatures` | 1,087 | 0 | 86/86 |
| `resharding` | 1,080 | 7 (5 ML-DSA keys, 2 `promise_batch_action_*` hosts: features this tier does not set) | 86/86 |

**Blind replay** uses `tools/mainnet-replay/blind_corpus.py --tier allFeatures`. Every produced
value is removed from the inputs (state roots including every implicit transition's post root,
outcome root, gas, balance burnt, receipts root, congestion, bandwidth and encoding), and Lean
recomputes them.

* On the committed cases, 19/20 honest cases match. One case is a harness `blind_error`:
  `seed11-01-h10062-s5` carries the sibling child's chunk header, which repeats the same main
  transition's outcome root, in its own segment. So a "secret" output is legitimately in the
  claim. Non-blind, the case is accepted.
* On the full raw corpus of 1,087 PV86 cases (`replay/raw-corpus-summary.json`), 1,084 match and
  no output field differs. The three exceptions are harness `blind_error`s: the sibling-header case
  above, and two `w.shape` ML-DSA key cases that the blind harness cannot blind. This covers all 12
  split children, 48 cross-layout chunks, 105 gate chunks and 54 cases with implicit transitions.

Before this change, the same raw corpus on the base checker (`fb435a61d`) gave these results. Every
split and cross-layout case was out of domain (`c.same_layout`). All 105 gate cases were out of
domain (`c.no_split_gate`). Five valid post-split chunks were rejected: three with
`implicit transition post state root` and two with `InvalidBandwidthRequests`.

**No regression on prior corpora.** `replay/regression.json` covers 4,625 earlier case
directories: the `combined-1788` list, 2,000 sampled `d3c7` mutants and the 837 `d3c7`
out-of-domain cases. Each was run on `allFeatures` and `resharding`, with the base checker and with
this branch. The 9,250 verdict-and-reason pairs are identical.

## Lean changes

All changes are in `spec/lean/v3`. Each one is root-caused against these fixtures.

1. **`checkD2CoreGWith` prefix.** It excluded `c.same_layout` and `c.no_split_gate` before
   delegating, so the `resharding` and `allFeatures` tiers could never decide a split.
   `checkSuccessor` and `checkSuccessorObs` now send non-genesis resharding-tier claims to the new
   `Successor/ReshardCore`. Genesis segments keep the old path and its exclusion.
2. **Segment walk across layouts** (`ReshardCore.walkSegment`, `get_state_witness_block_range`):
   * each block is read in its own epoch's layout;
   * the shard is carried child→parent at a layout boundary;
   * a split transition is placed only at a boundary block before the first new chunk, ahead of
     that block's old-chunk transition;
   * the main and implicit transitions run in their block's layout and walk shard;
   * receipt proofs use the per-block target shard.

   The old driver decided a split from the witness layout's split map and the block **index**, so
   every post-split child with an old-chunk transition was mistaken for a split. That is the three
   false rejects.
3. **Split trie** (`Resharding.retainSplit`, `splitRootE`). `retainRanges` kept stale
   `memory_usage` and never squashed, so a split root could not match nearcore's. The new function
   follows `retain_multi_range_recursive` and `squash_node`, and treats a missing node as a missing
   trie value.
4. **Child congestion.** The left child keeps the parent's congestion. The right child subtracts
   the parent's receipt-group totals read from the parent trie. Both are finalized to their own
   shard.
5. **Outgoing receipts** of a main transition in the parent layout go to the lowest-id child
   (`reassign_outgoing_receipts_for_resharding`) before the receipts root and the encoding are
   computed.
6. **V3 split event** (`splitEventV3`) uses `last_split` only. The V3 split map keeps history.
7. **Split gate decided** (`Successor/TrieSplit`). This is a transcription of
   `check_dynamic_resharding` and `find_trie_split`. All 13 forced-split headers match exactly
   (boundary, left and right memory), and all gate mutants are rejected.
8. **V3 bandwidth requests** (`StorageExecution.bandwidthRequestsV3L`). nearcore chains
   `get_parent_shard_id(to_shard)`'s buffer before the shard's own. For V3 that call returns the
   shard itself for every non-split shard, so the shard's buffer is counted twice. This is the
   pinned behaviour, and it causes the two `InvalidBandwidthRequests` false rejects.
9. **V3 buffer forwarding** (`forwardFromBufferV3L`). Buffers to the split parent are forwarded
   first, each receipt to its child (`forward_from_buffer`). This replaces an exclusion that hit 3
   cross-layout chunks.

## Not covered

* Static (V2) resharding across a protocol-version change, and any witness whose epochs include a
  PV85 epoch. These stay excluded.
* Two consecutive splits in one chain. The V3 split-history rule is covered only by a Lean unit
  example.
* Threshold-driven splits (`memory_usage_threshold` and `min_child_memory_usage` below
  `u64::MAX`). Only forced splits occur. The threshold branch of the gate is implemented but has no
  fixture.
* A validator-update (epoch-start) block inside the boundary walk.
* Global-contract distribution routed to an obsolete layout (W07).
* Genesis segments with a layout change.
