# `near/pv86/receipt-transfer-batch/v1` — Transfer-receipt batch with the real post-state root

Challenge name `near-transfer-receipt-v2`; claim format `near-arena-claim-v2`
(`spec/claim-v2.md`). Pinned nearcore `2.13.4` =
`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, protocol version **86**, mainnet
runtime parameters (`RuntimeConfigStore::new(None).get_config(86)`).

This is a **new, separately named** statement. v1 (`near/pv86/receipt-transfer-batch/v0`,
challenge `near-transfer-receipt-v1`, `spec/near-transfer-receipt-v1.md`,
`spec/claim-v1.md`, `NearSpec.TransferV1`) is unchanged: no v1 file of the
trusted base was modified, the v1 oracle path (`--scope v1`, the default)
regenerates the committed v1 fixtures byte-identically (modulo the wall-clock
`apply_ns` field of `diagnostics.json`), and the v1 differential test
reproduces `spec/difftest-report.json` exactly.

**What changes w.r.t. v1.** v1 proves `slice_post_root`, a *projection*: every
`Runtime::apply` also writes `TrieKey::BandwidthSchedulerState` (key `0x0f`)
(`docs/research/first-slice.md` §1.1; v1 §5). v2 formalizes that write for a
**shard layout with exactly one shard** and claims `post_state_root` =
`ApplyResult.state_root` — the root nearcore stores as `ChunkExtra.state_root`
and the next chunk header carries as `prev_state_root`. The receipt semantics
are v1's, reused verbatim (`TransferV1.applyReceipt`).

**Scope warning.** NEAR mainnet is multi-shard. With `n > 1` shards the
scheduler state holds `n²` link allowances that depend on the previous
allowances, on every shard's congestion info and bandwidth requests, and (via
a ChaCha20 shuffle seeded by `prev_block_hash`) on tie-breaking; none of that is
formalized here. **No current mainnet chunk is in this domain.** The statement
is the exact transition of a single-shard chain running PV 86 with mainnet
runtime parameters (e.g. a single-shard localnet/forknet), and the stepping
stone for the multi-shard version (§11).

## 1. The relation

Lean: `NearSpec.TransferV2.NearRelation (c : Claim) (w : Witness) : Prop`
(`spec/lean/NearSpec/TransferV2.lean`).

```lean
structure Witness where
  receipts : List Receipt   -- the ordered batch (v1 receipt shape)
  trie     : PTrie          -- partial pre-state trie: receivers' Account paths + path to 0x0f

def bandwidthStep (ctx : Ctx) (t : PTrie) : Option PTrie :=      -- §2.1
  match t.find bwKeyPath with                                      -- bwKeyPath = nibbles [0x0f] = [0, 15]
  | none => none                                                   -- witness does not determine 0x0f
  | some prev =>
    match (match prev with | none => some State.initial | some b => State.decode b) with
    | none => none                                                 -- undecodable: nearcore aborts
    | some st => t.upsert bwKeyPath (Bandwidth.step ctx.shardId (linkAllowed ctx.missedChunksCount) st).encode

def runChunk (ctx : Ctx) (w : Witness) : Option TransferV1.Acc :=  -- scheduler, then the v1 batch
  match bandwidthStep ctx w.trie with
  | none => none
  | some t => match TransferV1.runBatch ⟨ctx.blockHeight, ctx.blockGasPrice⟩ t w.receipts with
    | none => none
    | some acc => if !acc.refunds.isEmpty && !linkAllowed ctx.missedChunksCount then none else some acc

def NearRelation (c : Claim) (w : Witness) : Prop :=
  DomainStatic c w ∧                                                -- §3
  receiptsCommitment c.shardId w.receipts = c.receiptsCommitment ∧
  w.trie.hashOf = c.preStateRoot ∧
  (runChunk c.ctx w).map Outputs.ofAcc = some (Outputs.ofClaim c)   -- post root = hashOf of the final trie
```

`Outputs = (postStateRoot, outcomeRoot, refundCount, refundsCommitment,
gasBurntTotal, tokensBurntTotal)`; `Ctx = (shardId, missedChunksCount,
blockHeight, blockGasPrice)`. Proved: `NearRelation.domain`,
`NearRelation.outputs_unique`, `decodeClaim_encode`, `Claim.encode_injective`,
`NearRelation.claimDomain`. `ArenaCore.ChallengeSpec`:
`NearSpec.TransferV2.challengeSpec` (`NearSpec/ChallengeV2.lean`) with
`Claim := WfClaim`, `Rel := WfClaim.Rel`, `Domain := WfClaim.ClaimDomain`,
`encodeClaim/decodeClaim := WfClaim.encode/decode`, `decode_encode :=
WfClaim.decode_encode`.

Informally: *applying the ordered batch of incoming Transfer receipts to the
shard state with root `pre_state_root`, as nearcore 2.13.4 `Runtime::apply`
does for a chunk with no transactions, no local/delayed/yield/buffered receipts
and no validator updates, in an epoch whose shard layout has the single shard
`shard_id`, with the bound congestion info and no bandwidth requests, yields the
post-state root `post_state_root`, the outcomes with root `outcome_root`, exactly
the committed gas refunds, `gas_burnt_total` gas and `tokens_burnt_total` yoctoNEAR burnt.*

## 2. Semantics

Order inside `Runtime::apply` (`runtime/runtime/src/lib.rs:1740-1810`):
validator accounts (none) → load delayed queue (empty) → **`run_bandwidth_scheduler`**
(lib.rs:1767; writes `0x0f`) → receipt sink (forwards buffered receipts: none) →
transactions (none) → the incoming receipts. `0x0f` is disjoint from every
`Account` key (`0x00 ‖ id`), so the two writes commute; the relation follows
nearcore's order anyway.

### 2.1 Bandwidth-scheduler state for one shard (`NearSpec/Bandwidth.lean`)

**Layout** (`core/primitives/src/bandwidth_scheduler.rs:251-286`, `#[borsh(use_discriminant = true)]`):

```
BandwidthSchedulerState  = u8 0 (V1) ‖ BandwidthSchedulerStateV1
BandwidthSchedulerStateV1 = Vec<LinkAllowance> (u32 n ‖ n × 24 B) ‖ sanity_check_hash [u8;32]
LinkAllowance             = sender u64 ‖ receiver u64 ‖ allowance u64
```

Decoding is `BorshDeserialize::try_from_slice`: unknown tag, truncation or
trailing bytes ⇒ `StorageInconsistentState` and `apply` aborts
(`core/store/src/utils/mod.rs:26-39`) — out of domain (`scheduler_state_decodes`).

**Parameters** (PV 86 mainnet, `core/parameters/res/runtime_configs/74.yaml:2-5`,
unchanged through 86; asserted on the live config by `near-arena-oracle params --scope v2`):
`max_shard_bandwidth = 4 500 000`, `max_single_grant = 4 194 304`,
`max_allowance = 4 500 000`, `max_base_bandwidth = 100 000`. For `num_shards = 1`
(`BandwidthSchedulerParams::calculate`, bandwidth_scheduler.rs:317-347):
`base_bandwidth = min((4 500 000 − 4 194 304) / max(1, 0), 100 000) = 100 000`,
fair link share `max_shard_bandwidth / 1 = 4 500 000`.

**Update rule** (`run_bandwidth_scheduler`, `runtime/runtime/src/bandwidth_scheduler/mod.rs:44-141`;
`BandwidthScheduler::run`, `scheduler.rs:200-560`), layout `[S]`, no requests:

1. `prev := state[0x0f]`, or `V1 { link_allowances: [], sanity_check_hash: 0^32 }` if absent (mod.rs:59-71).
2. Allowance of link (S,S) carried over: the last entry of `prev.link_allowances`
   with `sender = receiver = S`, else 0 (entries for shards not in the layout are
   dropped; scheduler.rs:214-229, `default_link_allowance` = 0).
3. `increase_allowances`: `a := min(a ⊕ 4 500 000, max_allowance)` (`⊕` = u64 `saturating_add`; scheduler.rs:323-338, 442-450).
4. `grant_base_bandwidth`: `try_grant_bandwidth(link, 100 000)` succeeds iff the
   link is allowed and both budgets (`max_shard_bandwidth`) cover it; then
   `a := a ⊖ 100 000` (`saturating_sub`; scheduler.rs:340-345, 452-458, 467-497).
5. Requests: none (domain `no_bandwidth_requests`); `distribute_remaining_bandwidth`
   only adds grants, never touches allowances (scheduler.rs:393-405).
6. `update_scheduler_state`: `link_allowances := [(S, S, a)]` (one entry per link of the layout; scheduler.rs:548-560).
7. `sanity_check_hash := sha256(prev.sanity_check_hash ‖ sha256(borsh(all_shards)))`
   with `borsh(all_shards) = u32 1 ‖ u64 S` (mod.rs:120-131); write the state (mod.rs:134).

**Link status** (`calculate_is_link_allowed`, scheduler.rs:506-546): the
receiver's status is present (the block's congestion info contains S); the link
is refused iff `missed_chunks_count > 0` (`last_chunk_missing`), or S is fully
congested and S is not the allowed shard. Fully congested means congestion
level exactly 1.0 (`congestion_info.rs:44-100`); with `delayed_receipts_gas =
buffered_receipts_gas = receipt_bytes = 0` (domain `zero_congestion`) the
incoming/outgoing/memory terms are 0 and the missed-chunk term is 0 for
`missed ≤ 1` and irrelevant otherwise (the missing-chunk test comes first). So
under the domain **`linkAllowed missed := (missed = 0)`** exactly, and
`allowed_shard` has no effect.

Closed form (proved: `Bandwidth.newAllowance_eq`, `TransferV2.bandwidthStep_value`):

```
state'[0x0f] = 00 ‖ 01000000 ‖ S_le64 ‖ S_le64 ‖ A_le64 ‖ sha256(prev_hash ‖ sha256(01000000 ‖ S_le64))
A = 4 400 000 if missed_chunks_count = 0 else 4 500 000              (61 bytes, Bandwidth.step_encode_length)
```

The previous allowance never matters for one shard (the increase always
saturates at `max_allowance`), but the previous **state** matters through the
sanity hash chain and through its presence/length (§4).

### 2.2 Receipts (unchanged from v1)

Per receipt: v1 §2 (`TransferV1.applyReceipt`: receiver credit, outcome, gas
refund when `gas_price > block_gas_price`, burn at `min(gas_price, block_gas_price)`).

### 2.3 Refund forwarding needs a grant

Gas refunds go to the shard itself. With bandwidth scheduling, the receipt sink
forwards a receipt to shard S only within the granted bandwidth of link (S,S)
(`runtime/runtime/src/congestion_control.rs:96-120, 403-468`; gas limit is
`Gas::MAX` for the own shard). Allowed link ⇒ grant ≥ `base_bandwidth` =
100 000 bytes ≥ 256 refunds × ≤ 289 bytes, so every refund is forwarded (as in
v1). Refused link (`missed_chunks_count > 0`) ⇒ grant 0 ⇒ refunds would be
**buffered** (new trie keys) ⇒ out of domain (`refund_needs_grant`; the oracle
observes exactly this on the `missed_chunk_refund` rejection family).

## 3. Domain (restrictions)

`S` = checked by `DomainStatic`; `D` = checked by `runChunk` returning `some`;
`A` = stated assumption about the apply context (not checkable from the claim).

| id | restriction | why (nearcore behaviour otherwise) | Lean |
|---|---|---|---|
| `pv86`, `mainnet_params`, `claim_wf`, `batch_size`, `compute_limit`, `receipt_shape`, `valid_account_ids`, `signer_key_type`, `not_system_predecessor`, `named_receiver`, `distinct_receipt_ids` | as v1 §3 | as v1 | S (claim_wf now also bounds the congestion fields) |
| `witness_size` | revealed partial-trie bytes ≤ 3 000 000 (now incl. the `0x0f` path) | as v1 | S |
| `receiver_exists_v1`, `no_balance_overflow`, `storage_stake`, `burn_fits_u128` | as v1 | as v1 | D |
| `single_shard_layout` | the epoch's shard layout has exactly one shard, `shard_id`, and `shard_id < 2^32` | multi-shard scheduler (§11); `ShardUId` stores a u32 shard id (`shard_layout/mod.rs:485-487`) | A (+ S for the bound) |
| `zero_congestion` | `delayed_receipts_gas = buffered_receipts_gas = receipt_bytes = 0` | non-zero congestion changes the link status and the receipt sink's limits; a non-zero buffered gas with empty buffers makes `apply` **panic** (`congestion_control.rs:281-284`) | S |
| `no_bandwidth_requests` | the block carries no bandwidth requests | requests are granted from allowances and change them | A (implied on a real chain: requests come from outgoing buffers, empty when `receipt_bytes = 0`) |
| `scheduler_state_decodes` | an existing `0x0f` value is a valid borsh `BandwidthSchedulerState` | `apply` aborts (`StorageInconsistentState`) | D |
| `refund_needs_grant` | `missed_chunks_count > 0` ⇒ no receipt generates a gas refund | the refund is buffered, not forwarded (§2.3) | D |
| `apply_context` | the chunk applies only these incoming receipts: no transactions, no local/delayed/yield/buffered receipts, no validator-account update, new chunk | those run before/around incoming receipts and touch other keys | A |

The judge only issues jobs in the domain (the oracle checks it with an
independent Rust predicate, `oracle/src/v2.rs::check`, which reuses v1's
receipt-level predicate unchanged, and additionally requires nearcore to behave
cleanly: all outcomes `SuccessValue([])`, no delayed receipts, only Account keys
plus `0x0f` changed, `0x0f` written, outgoing receipts = generated refunds, the
key-value decomposition and the witness-only re-execution reproduce the root).
Out-of-domain fixtures: `oracle/fixtures/v2/rejection/` (18 families: v1's 14 +
`bw_state_undecodable`, `nonzero_congestion`, `missed_chunk_refund`,
`shard_id_too_large`).

## 4. Trie: insertion and value-length change (`NearSpec/TrieUpsert.lean`)

The `0x0f` write is not a v1-style in-place replacement:

* **insert** — the key is absent before the first scheduler run (and in every
  synthetic pre-state without it). Depending on the pre-state shape this splits
  a leaf, splits an extension, adds a branch child or adds a branch value;
* **length change** — the previous state may hold any number of link
  allowances (`37 + 24·n` bytes); the new one is always 61 bytes, so the
  `memory_usage` of every node on the path changes.

`PTrie.find : PTrie → List Nat → Option (Option Bytes)` distinguishes *present*
(`some (some v)`), *proven absent* (`some none`: the path leaves the trie at a
revealed node) and *undetermined* (`none`). `PTrie.upsert` implements nearcore's
insert (`core/store/src/trie/ops/insert_delete.rs`) on a partial trie, keeping
the trie canonical and recomputing `memory_usage` exactly
(`interface.rs:78-105`: leaf `50 + 2·|hp| + (|v| + 50)`, extension
`50 + 2·|hp| + child`, branch `50 + [|v| + 50] + Σ children`); an unrevealed
child's usage is never needed (an extension split recovers it as
`mem − (50 + 2·|hp|)`, exactly like nearcore's `children_memory_usage =
memory_usage − memory_usage_direct`, insert_delete.rs:53-54).

**Proved** (`NearSpec/TrieUpsertProofs.lean`, `NearSpec/TransferV2Props.lean`;
axioms ⊆ {propext, Classical.choice, Quot.sound}):

| theorem | statement |
|---|---|
| `PTrie.find_upsert_self` | `nibblesOk k → t.upsert k v = some t' → t'.find k = some (some v)` |
| `PTrie.find_upsert_other` | `t.wf → nibblesOk k → k' ≠ k → t.upsert k v = some t' → t'.find k' = t.find k'` (presence, proven absence and "undetermined" all preserved) |
| `PTrie.hashOf_refinedBy`, `PTrie.find_refinedBy` | a hash-pruning `t₁` of `t₂` (subtrees → hash, values → ValueRef) has the same root, and whatever `t₁.find` determines, `t₂.find` determines identically |
| `PTrie.upsert_refinedBy`, `PTrie.upsert_hashOf_congr` | `upsert` commutes with pruning: the post-root computed on any partial witness equals the post-root computed on the fully revealed trie |
| `bandwidthStep_spec` | the step writes exactly `0x0f` (with the state computed from the previous value read from the same trie) and every other key — in particular every Account key the receipts touch next — looks up as before |
| `bandwidthStep_refinedBy` | same independence for the whole scheduler step |
| `Bandwidth.newAllowance_eq`, `bandwidthStep_value`, `Bandwidth.step_encode_length` | closed form of §2.1 |

**Not proved** (argued here, and tested by differential testing on every
case): that on the *full canonical* pre-state trie `upsert` produces exactly
nearcore's canonical trie of the updated key→value map — i.e. that the shape
rules (extension over the longest common prefix, a branch at the first
differing nibble, leaf values moving into a branch value when a key ends there)
and the `memory_usage` deltas coincide with nearcore's `insert`. The argument:
nearcore's trie is the unique compressed Patricia trie of its key set (the root
is a function of the final map, `update.rs:242-262`), every `upsert` branch
builds that unique form for the new key set from the old one, and `memory_usage`
is the structural sum above. Combined with the proved theorems, this gives:
*if* `w.trie.hashOf = pre_state_root` and SHA-256 is collision resistant (so the
revealed nodes are a pruning of the real pre-state trie), *then*
`post_state_root` is the real post-state root.

The receivers' Account updates still use v1's `PTrie.set` (same-length value
replacement, `memory_usage` unchanged), which remains exact because AccountV1
values are always 72 bytes (v1 §4).

Coverage of the `0x0f` write in the reported difftest run (seed 4243; case
classification by `oracle/tools/difftest.py::bw_write_case` on the full
pre-state): update, same length 886; update, length change 68; insert as a new
branch child 461; insert as a branch value 6; extension split — new key
continues & rest of the extension kept 15, continues & rest empty 10, new key
ends at the new branch & rest kept 11, ends & rest empty 9; leaf split — both
keys continue, under a new extension 19 / without 11; new key ends at the new
branch (old leaf moves below it) 9. The `upsert` paths never exercised are
unreachable in the domain: a leaf split where the existing key is a proper
prefix of `0x0f` (needs the empty key), or one where the path to `0x0f` ends
inside a lone leaf below a non-empty extension (the subtree under nibble 0 would
have to hold a single key extending `0x0f`, but the receivers' accounts live
there).

## 5. The post-state root is the real one

For every in-domain case the oracle checks (`diagnostics.json`):
`post_state_root = ApplyResult.state_root` (that is what it emits),
`decomposition_ok` (pre ⊕ nearcore's own state changes = that root) and
`witness_only_post_root_ok` (nearcore's `Trie::from_recorded_storage` over
`witness.bin` alone reproduces it — the witness suffices for the insert). The
v1 worked example (alice/bob/carol, `docs/research/first-slice.md` §6) has
`post_state_root = 1420be412762e74b9ffa60aead6a770a6a220dab5415ad6243551a930198953d`,
exactly the "FULL Runtime::apply root" reported there, versus v1's projection
`28ff3f4a…`; the kernel proves the v2 relation rejects the projection
(`NearSpec.Examples.V2Negative.projection_root_rejected`).

## 6. What is formalized vs. only tested

| part | status |
|---|---|
| claim v2 encoding, strict decoding, round trip, injectivity | Lean definitions + **proved** |
| relation ⇒ domain; outputs determined by the witness and context | **proved** |
| `upsert` map semantics (incl. absence), independence from revealment, scheduler step writes exactly `0x0f` | **proved** (§4 table) |
| scheduler closed form (allowance 4.4M/4.5M, 61-byte state) | **proved** from the Lean transcription of the algorithm |
| Lean transcription of the scheduler algorithm, borsh layout, parameters, link status under zero congestion | written from the cited nearcore source; **faithfulness tested, not proved** (§7) |
| `upsert` = nearcore's canonical insert (shape + `memory_usage`) | argued (§4) + tested on every case, incl. every reachable insert case |
| receipt semantics, outcome hashing, refunds | as v1: tested, not proved |
| non-vacuity | **kernel-checked** (`decide +kernel`): `Examples.V2TierA` (scheduler key inserted), `V2TierBbw` (previous state updated, refunds), `V2Missed` (link refused, allowance 4.5M); negatives in `V2Negative` (projection root rejected, `missed_chunks_count` and the refund grant matter, non-zero congestion rejected, cross-scope decoding fails) |
| `single_shard_layout`, `no_bandwidth_requests`, `apply_context` | stated assumptions about the chunk context |
| memtrie / flat-storage paths | not exercised (disk-trie path, as v1) |

## 7. Differential testing

Three implementations agree byte-for-byte on `claim.bin` and on in-domain-ness:
(1) `near-arena-oracle gen --scope v2` — the real pinned `Runtime::apply` with
a one-shard layout `ShardLayout::v2([], [S])`, the request's congestion info
and an empty bandwidth-request set; (2) `nearspec-check --scope v2` — the
compiled Lean semantics, also evaluating `decide (TransferV2.NearRelation c w)`
on the decoded claim; (3) `oracle/tools/spec_check_v2.py` — independent Python
that implements the scheduler as the *algorithm* (not the closed form) and
rebuilds the whole trie from `state.bin` before and after (no partial-trie
update at all), plus a separate witness walk proving presence/absence of `0x0f`.

Results (`spec/difftest-report-v2.json`): seed 4243, **1775 cases** (1500 valid
+ 5 worked examples + 270 out-of-domain = 18 families × 15), **0
disagreements**; 1505 in-domain cases byte-identical across all three (1152
with refunds, 353 without; batch sizes 1..256, mean 25.1; shard ids 0 (1017),
1..2^16−1 (441), 2^16..2^32−1 (47); `allowed_shard ≠ shard_id` 433;
`missed_chunks_count > 0` 204; previous scheduler state absent / 0 / 1 / 2 /
≥3 links: see report) and `decide (NearRelation c w)` true on each; all 270
out-of-domain cases classified out-of-domain by all three. Wall time: oracle
5.7 s, Lean checker 68 s, Python 3.3 s.

```
oracle/scripts/link-nearcore.sh /path/to/nearcore@44f7ae6c && (cd oracle && cargo build -j 8)
(cd spec/lean && lake build)
python3 oracle/tools/difftest.py --scope v2 --seed 4243 --valid 1500 --invalid 270
```

Generator (`oracle/src/v2.rs`): every v1 profile (receipt and state shapes,
reused) plus `bw_state` (absent / realistic one-link / empty / stale multi-link
previous states with arbitrary allowances and hashes), `trie_shapes` (states
forcing each insert case: accounts only, a single account, one-nibble and long
extensions, keys in high columns, and raw keys extending `0x0f` that no nearcore
code writes), `missed` (1, 2, 3, 10, 124–126, 1000, random), `shards` (0, 1, …,
65535, 65536, 2^31, 2^32−1, random u32). Note: the `trie_shapes` raw keys make
some synthetic states unreachable on a real chain; they test the trie, which is
generic in its keys.

## 8. `runtime_config_digest` (v2)

`runtime_config_digest = sha256(JCS(D2))` with `D2` = the JSON emitted by
`near-arena-oracle params --scope v2` (`spec/challenge-inputs/runtime-config-pv86-v2.json`):
v1's description (§8 of the v1 doc: parameter files and their hashes, the
`RuntimeConfigView` hash, every slice constant) with `schema =
"near-arena-runtime-config-v2"` and `slice_parameters.bandwidth_scheduler =
{max_shard_bandwidth, max_single_grant, max_allowance, max_base_bandwidth,
max_receipt_size, num_shards: 1, derived_base_bandwidth: 100000,
derived_fair_link_bandwidth: 4500000}`, read from the live config and asserted
equal to `NearSpec.Bandwidth`.

## 9. Honest gaps

* Single-shard only (scope warning above); `prev_block_hash` is not bound
  because without requests the scheduler draws no randomness.
* Faithfulness of the Lean transcription to nearcore is established by source
  reading + differential testing, not proof; the `upsert` = canonical-insert
  step is argued (§4).
* Synthetic states only (§10); memtrie/flat storage not exercised; congestion
  is restricted to zero, so the f64 congestion-level arithmetic is never needed.

## 10. Historical replay

Unavailable for the same reasons as v1 (§10 of the v1 doc), and additionally
because mainnet is multi-shard: a replay would need a single-shard PV-86 chain
with mainnet parameters (e.g. a forknet), its chunk's `prev_state_root`, the
state witness for the receivers and `0x0f`, the incoming receipts, the block
header (height, gas price), the chunk header (gas limit, congestion info) and
the missed-chunk count. No network or archival access was used; all fixtures
are synthetic and labelled so in `provenance.json`.

## 11. Explicit exclusions (`excludes`) and next steps

`block_finality`, `data_availability`, `receipt_inclusion`,
`pre_state_root_on_chain`, `epoch_and_protocol_version_selection`,
`multi_shard_layouts`, `bandwidth_requests`, `nonzero_congestion`,
`transactions`, `signature_verification`, `function_calls_and_wasm`,
`non_transfer_actions`, `implicit_account_creation`,
`failure_paths_and_rollback`, `refund_receipt_inputs`,
`data_postponed_yield_receipts`, `delayed_receipt_queue`,
`buffered_receipts_and_forwarding_limits`, `outgoing_receipts_root_and_routing`,
`validator_updates_and_rewards`, `account_v2_global_contracts`,
`receipt_enum_action_v2`, `other_protocol_versions`, `testnet_parameters`.

(v1's `onchain_post_state_root` and `bandwidth_scheduler` exclusions are lifted
for the single-shard case.) Multi-shard next step: `n²` allowances with
carry-over (`min(a + max_shard_bandwidth/n, max_allowance)` no longer
saturates), requests from every shard ordered by allowance with the ChaCha20
tie-break seeded by `prev_block_hash`, per-shard congestion status (the f64
congestion level must then be formalized or bounded away from 1.0).

## 12. ArenaCore instance and parameters

`spec/lean/NearSpec/ChallengeV2.lean`: `NearSpec.TransferV2.challengeSpec`,
`challengeParamsWith profile verifyFuel maxProofBytes maxReductionFuel` (judge
templates `spec/lean/judge/ExpectedV2.lean.template` and
`ExpectedV2.native-lean.lean.template`, formal-checker config
`runners/formal-checker/challenges/near-transfer-receipt-v2.json`), and the
canonical `challengeParams` with v1's values (profile `validity-classical-128`,
`maxProofBytes` 8 MiB, `verifyFuel` = `maxReductionFuel` = 2^30): the v2 witness
adds one root→`0x0f` path (a few hundred bytes) to v1's.

## 13. Workload suite (v2)

Three classes by receipts per request, as v1 (`batch-1` 200 000 ppm, `batch-16`
300 000 ppm, `batch-256` 500 000 ppm; 8 requests per measured batch), generated
with `near-arena-oracle gen --scope v2 --receipts N` over all v2 profiles
(`spec/workloads/near-transfer-receipt-v2/batch-{1,16,256}.json`). Public dev fixtures:
`oracle/fixtures/v2/public` (byte-reproducible: `oracle/scripts/regen-fixtures-v2.sh`).
Held-out set: 24 cases per class from a secret seed kept off-repo
(`oracle/scripts/gen-heldout-v2.sh`); only its TreeDigest is committed
(`spec/challenge-inputs/heldout-commitment-v2.json`). Baselines are null.

### 13.1 Candidate class `max-witness` (not governed)

Purpose: an adversarial worst-case prover input, the maximal in-domain witness
of this statement, so that a later challenge revision can include it as a
class. It is **not** part of any governed challenge: the v2 draft's
`workload_suite` does not reference it (no weight, no held-out set); adding it
is a governance decision. Generator spec:
`spec/workloads/near-transfer-receipt-v2/max-witness.json`, i.e.
`near-arena-oracle gen --scope v2 --receipts 256 --profiles max_witness
--fixtures-layout` (the profile also works under `--scope v1`; it is never in
the default profile list). Source: `oracle/src/maxwit.rs`, a port of the
candidate-side `npudr gen-max --eps 0` onto real state: the oracle, not the
candidate, is the source of truth.

Shape, deterministic from `(seed, index)`: 256 receipts to distinct
64-character named receivers (130-nibble keys) with pairwise distinct
2-character prefixes. For every private nibble depth `d ≥ 4` of a receiver's
key there is one untouched sibling account that leaves the path exactly at `d`,
so each of the ~124 private nodes per path is a 2-child branch (75 bytes, 2
SHA-256 blocks) and the account leaf has an empty key; no extension compresses
a path, and siblings are never revealed (hash stubs). The remaining budget goes
to further siblings, pairs on odd-depth branches first (a 4-child branch is 139
bytes, 3 SHA blocks), calibrated against nearcore's own `TrieRecorder` so that
the slice witness (incl. the `0x0f` path) is `3 000 000 − r` bytes,
`0 ≤ r < 32`. Every receipt refunds (receipt gas price > block gas price
`10^8`); predecessors and signers are 64-character ids with SECP256K1 keys.
Empty-key extensions (the default `npudr gen-max` fill) cannot occur in a
nearcore trie and are not used.

Sizes (seed 42, v2): slice witness 2 999 973 revealed bytes in 32 402 values
(`witness.bin` 3 129 643 B), `request.bin` 89 037 B (limit 131 072), pre-state
49 921 entries (`state.bin` 5.5 MB); the full `Runtime::apply` recorded storage
is the same 2 999 973 B (< `main_storage_proof_size_soft_limit` 4 000 000:
nothing delayed). Generation takes ~1 s per case. Every case goes through
`Runtime::apply` and the domain check, like any other class.
