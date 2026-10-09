# `near/pv86/chunk-validation/v0`, domain **D0a** — D0 with amendments A1, A2, Canon0f, A7–A10

Status: **unsigned draft**, 2026-10-06 (lane `v3-spec`). Additive successor of domain D0
(`spec/near-chunk-validation-v0.md` §6, `NearSpecV3.RelD0`), which is pinned by the signed
challenge `near-chunk-validation-d0-1` and is **not modified**. Draft challenge:
`challenges/drafts/near-chunk-validation-d0-stark.draft.json`. Design and decisions:
`docs/zk-formal/V3-D0-DESIGN.md` §4, §10, §11.

## 1. The relation

```
RelD0a(B, W, Dp)(cb, w) := RelD0(cb, w) ∧ A1(cb) ∧ A2(cb, w) ∧ Canon0f(cb, w) ∧ unfoldBytes(cb, w) ≤ B
                           ∧ A8(cb) ∧ chachaWords(cb, w) ≤ W ∧ (∀ used source proof e, |e.path| ≤ Dp)
```

The challenge instance is `B = B0 = 2,000,000` (§2.4), `W = W0 = 770,000` (§2.6) and
`Dp = Dp0 = 32` (§2.7). `W0` and `Dp0` are user decisions of 2026-10-09.

Lean: `NearSpecV3.ChunkValidationV0a` (`RelD0a B cb w (W := W0) (Dp := Dp0)`, `a1`, `a2`, `canon0f`,
`a7`, `unfoldBytes`, `a8`, `a9`, `chachaWords`, `a10`, `maxPathDepth`; executable verdict
`checkD0a B cb w (W := W0) (Dp := Dp0)`; **proved**: `relD0a_iff : RelD0a B cb w W Dp ↔
checkD0a B cb w W Dp = .ok ()`, `relD0a_relD0 : RelD0a B cb w W Dp → RelD0 cb w` (for all
bounds), `relD0a_mono` (in `B`), `relD0a_mono_all` (in `B`, `W`, `Dp`),
`Scheduler.run_eq_mid` (the counted RNG is the run's own)). A pure restriction: every D0a proof
is a D0 proof of the same claim; no soundness statement mentions the bounds. The claim
and witness formats are unchanged (`spec/claim-v3.md`).

## 2. Amendments (out-of-domain conditions added to D0's table)

| id | condition | reason |
|---|---|---|
| `c.gas_limit` (A1) | the `gas_limit` of B2's own-shard slot (the block of the shard's last new chunk) is `≤ 10^15` (1000 Tgas) | bounds the applied receipts (`n ≤ 4481`) and the refund body (`≤ 0.91 MB`) for a succinct proof |
| `w.proof_routing` (A2) | every receipt of every *used* source receipt proof (the entry the last-wins lookup selects for a new source chunk) routes, under `L(epoch_id)`, to the validated shard | no receipt is Merkle-hashed but filtered out (proof-size bound) |
| `w.unfolded` (A7) | `unfoldBytes(cb, w) ≤ B0 = 3,000,000` (§2.4) | the AIR hashes every revealed node *occurrence* (tree-shaped records); a witness can share one subtree under many slots, so the unfolded size — not `|base_state|` — bounds the SHA and node tables |
| `c.bw_requests` (A8) | in every block of the claim's segment, every chunk slot's `BandwidthRequests` has at most one request per `to_shard` (claim-only; `prepD0` checks it natively) | bounds the requests the in-AIR scheduler converts and processes (`≤ n²` per applied block), hence the scan / process table heights |
| `e.chacha_words` (A9) | the bandwidth-scheduler runs of all applied transitions (main at B2, each implicit block) draw `≤ W0 = 770,000` ChaCha20 words in total (§2.6) | bounds the in-AIR ChaCha lane: `chachaV3 ≤ 86·⌈K/16⌉ ≤ 4,141,410 < 2²²` rows; the rejection-sampling fuel alone allows ≈ 9.9 M words |
| `w.path_depth` (A10) | every *used* source receipt proof's Merkle path has `≤ Dp0 = 32` items (§2.7) | bounds the in-AIR source-proof table: `srcpV3 ≤ 1984·(33 + 64·32) = 4,128,704 ≤ 2²²` rows; `rootFromPath` alone accepts any length |
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

**`B0 = 2,000,000`** (lead decision, user-approved). The SHA table hashes every unfolded byte
(pre occurrences once; changed post occurrences once) at ≤ 1.25 rows/byte (sha_t, lane
v3-trie); 1.25 · 2,000,000 = 2.5 M of its 2²² = 4.19 M rows, leaving ≈ 1.69 M rows for the
non-trie hashing (receipt lists, outcome leaves, Merkle paths). The node table (1 row per pre
byte, post bytes in lockstep) stays below 2²². Table heights — hence the 8 MiB proof-size
analysis (§5.3) — are unchanged by A7. Note `B0` is below the `base_state ≤ 3,000,000` bound
of `w.size`: **chunks whose unfolded read set is between 2 and 3 MB move out of D0a** — they
become unprovable in this domain, never wrongly accepted.

**Measured** (STATUS-V3-SPEC §1.2): over the 2,993 nearcore-accepted honest witnesses of the
full corpus `unfoldBytes` ≤ 50,579 (p50 4,286, p99 12,650; on the 2,695 RelD0 cases ≤ 7,917):
headroom ≈ 40× against `B0`. Honest tries share only identical leaves/values (full unfold /
recorded bytes ≤ 2.31 on D0, ≤ 1.32 on the public D1 corpus).

**Liveness limit (known, for later domains).** A7 never makes a false statement provable; it
can make a *valid* chunk unprovable. An adversary who controls state can make the read paths
of one chunk long and their unfolded bytes large while `|base_state|` stays small (identical
subtrees are recorded once): every revealed occurrence is a node of the logical trie, so a
path through `D` branch levels needs ≈ `D` sibling accounts, and ≈ `U / 75` accounts are needed
for `U` unfolded bytes with 2-child branches (≈ 75 B each; with 16-child branches ≈ 559 B per
occurrence but 15 siblings). Exceeding `B0` thus takes ≈ 27,000 named accounts with identical
sub-structure (e.g. sub-accounts of one attacker account), plus receipts to ≤ 4,481 of them in one
chunk. Cost at PV 86: storage stake ≈ 182 B per account (account record + full-access key) ×
10¹⁹ yocto/B ≈ 0.0018 NEAR → **≈ 50 NEAR locked** (refundable on deletion) + creation gas
(CreateAccount + AddKey + Transfer ≈ 0.4–0.5 Tgas each → ≈ 13 Pgas ≈ 1.3 NEAR at the 10⁸ yocto/gas
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

### 2.6 A9 `e.chacha_words`: definition, `W0`, liveness

**Definition** (`NearSpecV3.chachaWords`, `a9`). Every applied transition τ (main at B2, then
each implicit block, oldest first) runs `Scheduler.run` once with a fresh
`ChaCha20Rng::from_seed(prev_block_hash)`; its only RNG use is the shuffle of each equal-allowance
bucket in `process_bandwidth_requests` (`scheduler.rs:362`, `gen_index` rejection sampling). The
words a run draws are its RNG's stream position afterwards (`Scheduler.rngWords = 16·ctr −
|buf|`; nearcore `ChaCha20Rng::get_word_pos`). `chachaWords cb w = Σ_τ` words drawn by τ's run,
with the run's inputs exactly `prims.sched`'s (`schedInsD0`: the walk's block contexts and the
`0x0f` value of τ's pre-trie). `Scheduler.runMid` repeats `run` up to its last RNG use, and
`Scheduler.run_eq_mid` (**proved**) shows `run = (runMid …).map finish`, so the counted RNG is
the run's own. Decidable; computed independently by the Python checker (every `ChaCha20Rng`
the D0 checker's scheduler creates counts its `next_u32` calls) and the oracle (a copy of
nearcore's scheduler core on nearcore's inputs with `rand_chacha`'s `get_word_pos`, its
resulting state checked against nearcore's own post-state on every honest witness).

**`W0 = 770,000`** (user decision 2026-10-09). With `≤ 33` scheduler instances, the in-AIR
lane has `genV3 = K ≤ 770,000 < 2²⁰`, `chachaV3 = 86·⌈K/16⌉ ≤ 86·(W0 + 15·33)/16 = 4,141,410`
`< 2²²` rows and `shufV3 ≤ 174,149` (`ZkFormal…Sched.Complete.lane_770k_22`, `lane_W0`); the
largest bound that fits `2²²` is 779,840 (`chachaMax_tight`). The alternative 360,000 (≈ 16 %
over twice the worst-case expectation) is superseded. Without A9 the bound is only the fuel
bound `K + 64·Rd ≤ 64·S`, ≈ 9.9 M words at the worst A7/A8 claim (`worstK_exceeds`).
Not a nearcore invariant: the count depends on hash outputs (rejections in `gen_index`) and on
how many equal-allowance requests the claim's chunk headers carry.

**Liveness.** A9 never makes a false statement provable; a chunk whose scheduler runs draw
more than `W0` words is **out of D0a: unprovable in this domain, never wrongly accepted**. An
honest run draws about one word per request in a shuffled bucket of size ≥ 2 (rejections
are rare), so exceeding `W0` takes ≈ 770 k bucket entries over ≤ 33 runs — far above any
real block (a run has at most `n²` requests with ≤ 40 increases each, so `n ≤ 9` shards give
≤ 3,240 entries per run). **Measured** (Lean = Python = oracle on every case): full corpus max
3 words per D0a case (5 per run on honest witnesses), heavy-request corpus max 8 per D0a case
(165 cases non-zero; 16 on any honest witness), nearcore's 600 scheduler vectors max 102 per
run; 0 honest witnesses out of A9.

### 2.7 A10 `w.path_depth`: definition, `Dp0`, liveness

**Definition** (`NearSpecV3.a10`, `maxPathDepth`): every used source receipt proof (the entry
`checkD0`'s last-wins lookup selects for a new source chunk, `usedProofs`) has
`|e.proof.path| ≤ Dp`. `verifyReceiptProof` (`rootFromPath`, nearcore `verify_path`) accepts a
path of any length.

**`Dp0 = 32`** (user decision 2026-10-09: the largest depth that keeps the source-proof table
within `2²²` rows and the 8 MiB bound). `srcpV3` spends per used proof one root row, a 32-row
leaf segment and one 64-row segment per path item, exactly (`SrcpGen.R_eq`); there are at most
`31·64 = 1984` used proofs (`usedProofs_count`, `prepD0_source_count`). Hence
`rows ≤ 1984·(33 + 64·Dp)`: `Dp = 32` gives 4,128,704 ≤ 2²² = 4,194,304, `Dp = 33` gives
4,255,680 > 2²² (`ZkFormal.NearV3.Rcpt.SrcpDepth.dp0_largest`, attained: `dp0_tight`). The
design's rounder estimate `1984·(2 + Dp)·64` would allow 31. At `Dp0` the receipt-side SHA
rows (A1 worst case) are 3,501,199 `< 2²²` and the source-proof SHA rows alone 2,257,792
(one SHA table). The 8 MiB proof-size model already counts `srcpV3` at its aligned cap `2²²`,
so the bound is unchanged (V3-D0-DESIGN §3.5). `Dp0 ≥ 16`; nearcore emits `⌈log₂ #shards⌉ ≤ 6`
items at ≤ 64 shards.

**Liveness.** A10 never makes a false statement provable; a witness with a longer used path
is **out of D0a: unprovable in this domain, never wrongly accepted**. Honest producers never
emit one (the path is the outgoing-receipts Merkle tree over the layout's shards).
**Measured**: honest max depth 3 on every corpus (headroom 29 levels), 0 honest witnesses out
of A10; the oracle's path-depth mutants (nearcore accepts both) are in D0a at 32 items and
`w.path_depth` at 33 in Lean and Python (845/845 full, 59/59 public, 559/559 heavy-request).

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
* **A9 / A10 (2026-10-09).** Oracle: `src/sched.rs` is an independent copy of nearcore's
  scheduler core (request conversion, link permissions, allowances, base grants,
  `process_bandwidth_requests` with `rand_chacha`); `d0a.rs` replays every scheduler run of the
  witness (main at B2 and each implicit block) on nearcore's own block contexts and pre-state,
  reads `get_word_pos()` after the last shuffle, and checks the replica's new `0x0f` state against
  nearcore's actual post-state (generation aborts on any mismatch); `w.path_depth` uses the
  witness's `MerklePath` lengths. Meta fields `chacha_words`, `chacha_words_runs`,
  `max_path_depth`. **Path-depth mutants** (`src/pathmut.rs`, every accepted D0a case whose
  segment starts at B2): a used source proof of B2 is extended with deterministic synthetic
  siblings to exactly 32 items (`w.path_depth_at_bound`, in D0a) and to 33 items
  (`w.path_depth_over`, expected `out_of_domain` / `w.path_depth`); the chunk's
  `prev_outgoing_receipts_root` and the hash chain are recomputed, the mutated B2 is injected
  into the judging client's store, and **nearcore's own validator judges each mutant** (all
  accepted: `Rel` holds); a negative control (last sibling flipped) is rejected by nearcore.
  `sched-words` runs the replica on nearcore's 600 scheduler vectors
  (`oracle/fixtures/v3/vectors-d0a/scheduler_words.json`); `oracle/tools/sched_words_v3.py`
  compares it with Python and Lean (`nearspec-v3-test-words`). `--heavy-requests` (default
  off) makes two non-own shards burst 300–500 transfers to a third so that nearcore emits
  bandwidth requests and the scheduler draws words. Boundary: `oracle/tools/d0a_boundary_v3.py`
  (each in-domain case at its own value `V` accepts, at `V − 1` is out of domain for that
  family). Results: `docs/e2e-results/v3-domain-bounds/report.json`, STATUS-V3-AIR §5.
