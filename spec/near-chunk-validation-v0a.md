# `near/pv86/chunk-validation/v0`, domain **D0a** — D0 with amendments A1, A2, Canon0f

Status: **unsigned draft**, 2026-10-06 (lane `v3-spec`). Additive successor of domain D0
(`spec/near-chunk-validation-v0.md` §6, `NearSpecV3.RelD0`), which is pinned by the signed
challenge `near-chunk-validation-d0-1` and is **not modified**. Draft challenge:
`challenges/drafts/near-chunk-validation-d0-stark.draft.json`. Design and decisions:
`docs/zk-formal/V3-D0-DESIGN.md` §4, §10, §11.

## 1. The relation

```
RelD0a(cb, w) := RelD0(cb, w) ∧ A1(cb) ∧ A2(cb, w) ∧ Canon0f(cb, w)
```

Lean: `NearSpecV3.ChunkValidationV0a` (`RelD0a`, `a1`, `a2`, `canon0f`; executable verdict
`checkD0a`, `relD0a_iff : RelD0a cb w ↔ checkD0a cb w = .ok ()` **proved**). A pure
restriction: `RelD0a → RelD0`, so every D0a proof is a D0 proof of the same claim. The claim
and witness formats are unchanged (`spec/claim-v3.md`).

## 2. Amendments (out-of-domain conditions added to D0's table)

| id | condition | reason |
|---|---|---|
| `c.gas_limit` (A1) | the `gas_limit` of B2's own-shard slot (the block of the shard's last new chunk) is `≤ 10^15` (1000 Tgas) | bounds the applied receipts (`n ≤ 4481`) and the refund body (`≤ 0.91 MB`) for a succinct proof |
| `w.proof_routing` (A2) | every receipt of every *used* source receipt proof (the entry the last-wins lookup selects for a new source chunk) routes, under `L(epoch_id)`, to the validated shard | no receipt is Merkle-hashed but filtered out (proof-size bound) |
| `e.sched_canonical` (Canon0f) | every `0x0f` (`BandwidthSchedulerState`) value the run reads — main pre-state and each implicit transition's pre-state — is absent or `V1` whose links are exactly the layout's `n²` links `(sender, receiver)` in sender-major order (any allowances, any sanity hash) | the in-AIR scheduler decodes the previous state as exactly `n²` ordered links |

### 2.1 A1 source check (nearcore 2.13.4, `44f7ae6c`)
The genesis chunk extra takes `genesis_config.gas_limit` (`chain/chain/src/types.rs:288`,
`chain/chain/src/chain.rs:430,614`); a chunk producer copies `chunk_extra.gas_limit()` into the
new header (`chain/client/src/chunk_producer.rs:393`); validation requires
`prev_chunk_extra.gas_limit() == chunk_header.gas_limit()` (`chain/chain/src/validate.rs:154`);
applying stores `to_chunk_extra(chunk_header.gas_limit())` (`chain/chain/src/chain_update.rs:472,519`,
`types.rs:166-172`), a missing chunk reuses `prev_chunk_extra.gas_limit()` (`update_shard.rs:224`).
So a chain's chunk gas limit is its genesis value forever: a real chain is wholly in or wholly
out of A1 (mainnet: 1000 Tgas, in).

### 2.2 A2 source check
`Chain::create_receipts_proofs_from_outgoing_receipts` (`chain/chain/src/chain.rs:4132-4150`)
builds the proof for `to_shard_id = shard_layout.get_shard_id(i)` from
`group_receipts_by_shard(outgoing, shard_layout)`; routing is `receipt.receiver_shard_id(layout)`
= `account_id_to_shard_id(receiver_id)` for Action receipts (`core/primitives/src/receipt.rs:438-447`);
the layout is that of the chunk's epoch, in D0 (single epoch) `L(c.epoch_id)`; the witness
producer passes the stored proofs through (`stateless_validation/state_witness.rs:264-320`).
Hence every honest D0 witness satisfies A2. A foreign receipt with a valid Merkle path is
accepted by nearcore (`filter_incoming_receipts_for_shard` drops it) but is outside D0a.

### 2.3 Canon0f source check
* The only writer of `TrieKey::BandwidthSchedulerState` in the runtime is
  `run_bandwidth_scheduler` → `set_bandwidth_scheduler_state`
  (`runtime/runtime/src/bandwidth_scheduler/mod.rs:118-135`, `core/store/src/utils/mod.rs:330-335`;
  the other writer in the tree is the offline `tools/fork-network` mutator).
* It writes `BandwidthSchedulerState::V1` after `update_scheduler_state`
  (`runtime/runtime/src/bandwidth_scheduler/scheduler.rs:548-562`): one `LinkAllowance` per link
  of `iter_links()` (`scheduler.rs:427-435`: sender index major, receiver minor, over
  `0..num_shards`), with `sender/receiver = shard_layout.get_shard_id(index)`, for every link
  present in `link_allowances` — and every link is present after `increase_allowances`
  (`scheduler.rs:323-336`, `increase_allowance` inserts each link of `iter_links()`).
* Absent before the first run after genesis (`mod.rs:61-70`): allowed.
* Hence every value read is canonical **for the layout of the application that wrote it**
  (`shard_layout(&apply_state.epoch_id)`, `mod.rs:72`). In D0 every value the run reads was
  written by an application in the segment's own epoch: the main pre-state is the post-state of
  the stop block's chunk application followed by the missing-chunk applications of the blocks
  up to B2's parent, and the implicit pre-states are post-states of the previous transitions —
  all applications of blocks in `epoch_id` (`c.single_epoch`: every header in `epoch_id`, no
  epoch start in the segment), hence under `L(epoch_id)`; or the key is absent (genesis
  state). So **every honest D0 witness satisfies Canon0f**; a non-canonical value needs a state
  the chain never wrote (the reason the condition exists: an adversarial witness may present,
  in an implicit transition, a different value with a colliding digest, which the semantic
  theorems cannot exclude).
* Tested: the oracle's classifier (`oracle/v3-d0a/src/d0a.rs`, nearcore's own trie reads)
  checks Canon0f on every honest witness of the generated chains (§3).

## 3. Reference oracle and tests

* `oracle/v3-d0a` (binary `near-arena-oracle-v3-d0a`): the D0 oracle's modules shared unmodified
  from `oracle/v3/src` (`#[path]`), plus `src/d0a.rs` (amendment classifier on nearcore objects:
  B2 slot `gas_limit()`, `Receipt::receiver_shard_id`, `get_bandwidth_scheduler_state` on the
  tracking node's full pre-state and on `Trie::from_recorded_storage` over each implicit
  transition), `src/a2mut.rs` (A2 mutant) and a copy of `chaingen.rs` that classifies with
  D0 ∧ amendments, adds chain 8 (genesis gas limit 1500 Tgas, every chunk outside A1), and on
  every accepted D0a case whose segment starts at B2 writes the **A2 mutant**
  `w.foreign_routed_receipt`: a D0-shaped receipt routed to another shard is appended to a
  source proof of B2; the chunk's `prev_outgoing_receipts_root`, its chunk hash (the map key),
  B2's `chunk_headers_root` and hash, and the endorsed chunk's `prev_block_hash` are recomputed;
  every value nearcore's validator reads is then consistent and the foreign receipt is filtered,
  so `Rel` holds by construction (nearcore cannot judge it directly: the mutated block is not in
  its store); expected verdict `out_of_domain`.
* Checkers: Lean `nearspec-v3-check-d0a` (`zk-formal` package, compiled `checkD0a`), Python
  `oracle/tools/spec_check_v3_d0a.py` (D0 checker unmodified + independent amendment checks).
* 3-way difftest: `oracle/tools/difftest_v3_d0a.py`; public fixtures
  `oracle/fixtures/v3/public-d0a/` (seed 4243, 2 chains × 40 blocks); full set seed 4243,
  9 chains × 120 blocks. Results: `docs/zk-formal/STATUS-V3-SPEC.md`.
