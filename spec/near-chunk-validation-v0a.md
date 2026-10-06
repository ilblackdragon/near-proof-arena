# `near/pv86/chunk-validation/v0`, domain **D0a** — D0 with amendments A1, A2, Canon0f

Status: **unsigned draft**, 2026-10-06 (lane `v3-spec`). Additive successor of domain D0
(`spec/near-chunk-validation-v0.md` §6, `NearSpecV3.RelD0`), which is pinned by the signed
challenge `near-chunk-validation-d0-1` and is **not modified**. Draft challenge:
`challenges/drafts/near-chunk-validation-d0-stark.draft.json`. Design and decisions:
`docs/zk-formal/V3-D0-DESIGN.md` §4, §10, §11.

## 1. The relation

```
RelD0a(B)(cb, w) := RelD0(cb, w) ∧ A1(cb) ∧ A2(cb, w) ∧ Canon0f(cb, w) ∧ unfoldBytes(cb, w) ≤ B ∧ A8(cb)
```

The challenge instance is `B = B0 = 3,000,000` (§2.4).

Lean: `NearSpecV3.ChunkValidationV0a` (`RelD0a B`, `a1`, `a2`, `canon0f`, `a7`, `unfoldBytes`, `a8`;
executable verdict `checkD0a B`; **proved**: `relD0a_iff : RelD0a B cb w ↔ checkD0a B cb w = .ok ()`,
`relD0a_relD0 : RelD0a B cb w → RelD0 cb w` (for every `B`), `relD0a_mono`). A pure
restriction: every D0a proof is a D0 proof of the same claim; no soundness statement
mentions `B`. The claim
and witness formats are unchanged (`spec/claim-v3.md`).

## 2. Amendments (out-of-domain conditions added to D0's table)

| id | condition | reason |
|---|---|---|
| `c.gas_limit` (A1) | the `gas_limit` of B2's own-shard slot (the block of the shard's last new chunk) is `≤ 10^15` (1000 Tgas) | bounds the applied receipts (`n ≤ 4481`) and the refund body (`≤ 0.91 MB`) for a succinct proof |
| `w.proof_routing` (A2) | every receipt of every *used* source receipt proof (the entry the last-wins lookup selects for a new source chunk) routes, under `L(epoch_id)`, to the validated shard | no receipt is Merkle-hashed but filtered out (proof-size bound) |
| `w.unfolded` (A7) | `unfoldBytes(cb, w) ≤ B0 = 3,000,000` (§2.4) | the AIR hashes every revealed node *occurrence* (tree-shaped records); a witness can share one subtree under many slots, so the unfolded size — not `|base_state|` — bounds the SHA and node tables |
| `c.bw_requests` (A8) | in every block of the claim's segment, every chunk slot's `BandwidthRequests` has at most one request per `to_shard` (claim-only; `prepD0` checks it natively) | bounds the requests the in-AIR scheduler converts and processes (`≤ n²` per applied block), hence the scan / process table heights |
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

### 2.3a A8 source check (nearcore 2.13.4, `44f7ae6c`)

* `runtime/runtime/src/congestion_control.rs:503-523` (`generate_bandwidth_requests`): one
  `generate_bandwidth_request(shard_id, …)` per `shard_layout.shard_ids()`, at most one request
  each, `to_shard = shard_id` (`core/primitives/src/bandwidth_scheduler.rs:84-126`).
* `chain/chain/src/validate.rs:280-298` (`validate_bandwidth_requests`): a chunk header whose
  requests differ from the ones its previous chunk's application stored in the chunk extra is
  rejected (`InvalidBandwidthRequests`).
* So every chunk header of a valid chain satisfies A8. The validated shard's own header carries no
  requests in D0 (`H.bwRequests = []`).

### 2.4 A7 `w.unfolded`: definition, `B0`, liveness

**Definition** (`NearSpecV3.unfoldBytes`, coordinated with STATUS-V3-TRIE §1.3–1.4,
`UnfoldBound`): for each applied transition τ (main, then each implicit one) with pre-trie
`pre_τ = partialTrie ws_τ root_τ keys_τ` (exactly the trie `checkD0` builds) and post-trie
`post_τ` (the post-state as a store presents it, rebuilt along the same keys):
`unfoldBytes = Σ_τ unfoldedBytesT pre_τ + diffT pre_τ post_τ`, where `unfoldedBytesT` sums
`|nodeEnc o|` over the revealed node occurrences (per path copy) and the revealed values
(identical to lane v3-trie's `unfoldedBytes`, so `UnfoldBound e ws root keys` is
`unfoldedBytesT (partialTrie ws root keys) ≤ e`), and `diffT` sums the post node occurrences
whose encoding differs from the pre-trie's at the same position plus the changed revealed
values (the post-write path copies the AIR hashes). Decidable; computed independently in the
oracle (`oracle/v3-d0a/src/d0a.rs`: nearcore `RawTrieNodeWithSize`, witness values and the
tracking node's State column, keys from `TrieKey::to_vec`) and the Python checker (the keys the
D0 checker reads, raw node bytes); the difftest compares the three values exactly.

**`B0 = 3,000,000`.** The SHA table hashes every unfolded byte (pre occurrences once; changed
post occurrences once) at ≤ 1.25 rows/byte (sha_t, lane v3-trie); 1.25 · 3,000,000 = 3.75 M of
its 2²² = 4.19 M rows, leaving ≈ 0.44 M rows (≈ 350 KB of input) for the non-trie hashing
(receipt lists, outcome leaves, Merkle paths), the budget V3-D0-DESIGN §5.1 assumes. The node
table (1 row per pre byte, post bytes in lockstep) stays below 2²². Table heights — hence the
8 MiB proof-size analysis (§5.3) — are unchanged by A7. *Assumption to confirm with the trie
and receipt lanes: the non-trie SHA input at A1-maximal load fits in the remaining 0.44 M rows.*

**Measured** (STATUS-V3-SPEC §1.2): over the 2,993 nearcore-accepted honest witnesses of the
full corpus `unfoldBytes` ≤ 50,579 (p50 4,286, p99 12,650; on the 2,695 RelD0 cases ≤ 7,917):
headroom ≥ 59× against `B0`. Honest tries share only identical leaves/values (full unfold /
recorded bytes ≤ 2.31 on D0, ≤ 1.32 on the public D1 corpus).

**Liveness limit (known, for later domains).** A7 never makes a false statement provable; it
can make a *valid* chunk unprovable. An adversary who controls state can make the read paths
of one chunk long and their unfolded bytes large while `|base_state|` stays small (identical
subtrees are recorded once): every revealed occurrence is a node of the logical trie, so a
path through `D` branch levels needs ≈ `D` sibling accounts, and ≈ `U / 75` accounts are needed
for `U` unfolded bytes with 2-child branches (≈ 75 B each; with 16-child branches ≈ 559 B per
occurrence but 15 siblings). Exceeding `B0` thus takes ≈ 40,000 named accounts with identical
sub-structure (e.g. sub-accounts of one attacker account), plus receipts to ≤ 4,481 of them in one
chunk. Cost at PV 86: storage stake ≈ 182 B per account (account record + full-access key) ×
10¹⁹ yocto/B ≈ 0.0018 NEAR → **≈ 75 NEAR locked** (refundable on deletion) + creation gas
(CreateAccount + AddKey + Transfer ≈ 0.4–0.5 Tgas each → ≈ 20 Pgas ≈ 2 NEAR at the 10⁸ yocto/gas
minimum price) + the transfers that target the chunk. Cheap: the domain's liveness against an
adversarial state owner is weak; later domains need a larger `B` (multi-instance tables /
recursion) or a cost-based argument. The attacker cannot make a wrong chunk provable.

### 2.5 Duplicate chunk hashes among used source chunks
`RelD0` does not forbid two used source slots with the same chunk inner (the claim's blocks
are authenticated only up to its own `prev_block_hash`); both are looked up under one key
(last-wins), so their receipt lists are equal, and `distinctKeys(entries) = #used` then needs
**one extra, unused entry per duplicate**. So `RelD0` (and `RelD0a`) is satisfiable in that
case, and only with such extra entries. Tested (`oracle/tools/dupkey_v3.py`, 30 constructed
claims from accepted D0 cases: the witness with the extra entry is accepted by Lean and
Python, the same witness without it is rejected). Consequences: the constructed witness must
contain one entry per distinct used key **plus** `#used − #distinct` filler entries with fresh
keys (any D0-shaped content); the AIR's `srcp` must bind equal lists to equal keys (one entry
per key), count the filler entries, and never route a filler entry's receipts. The reference
normal form (`normalW`: dedup + sort) keeps filler entries (distinct keys).

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
