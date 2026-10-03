# Historical replay from authentic NEAR mainnet data

Status as of 2026-10-03, statement `near/pv86/receipt-transfer-batch/v0`
(nearcore 2.13.4 `44f7ae6c`, PV 86, mainnet parameters).

**Result in one paragraph.** Public JSON-RPC cannot provide the trie nodes a
witness needs. The NEAR peer-to-peer state-sync protocol can: any mainnet node
will serve a *state part* to any peer. A state part holds the raw trie nodes for
a key range of a shard trie. With it we built **4 authentic mainnet fixtures**
in `oracle/fixtures/historical/`. Each one has three properties:

* the witness is made of real mainnet trie nodes, hash-linked to an on-chain
  `prev_state_root`;
* the receipts are real mainnet receipts that originated from transactions;
* the claims were produced by the pinned `Runtime::apply` running on those nodes
  and were confirmed by the Lean checker.

All 4 are class **`historical-rebased-prestate`**. Their pre-state is the
shard's *state-sync root*, an on-chain root committed 9–59 blocks before the
block that actually executed the receipt. Each claim is therefore authentic
data run through nearcore, but it is **not the chain's own transition**.

In two cases the claim's `outcome_root`, `gas_burnt_total`, `tokens_burnt_total`
and refunds equal the on-chain values of the executing chunk. The chain executed
exactly that one receipt in that chunk, and the receiver's Account record is
byte-identical. Only `pre_state_root` and `slice_post_root` differ from the
chain's transition.

An **exact** replay was not achievable in the current epoch. Public trie nodes
exist for exactly one root per shard per epoch, and the chunks applied to those
roots in this epoch contain no in-domain receipt (§4). Section 7 lists what
would be needed.

## 1. Data sources tried

Probed 2026-10-03 06:10–07:35 UTC with small volumes. Full request log is in
the harvester output.

| source | result |
|---|---|
| `https://rpc.mainnet.near.org` `status` | chain `mainnet`, `protocol_version` 86, node 2.13.4 commit `44f7ae6c` (= our pin). `network_info` lists ~74 active peers with addresses. Non-archival: earliest block ≈ 218 191 586 (≈ 2.5 days). |
| `https://archival-rpc.mainnet.near.org` | Worked for about an hour (blocks down to height 200 000 000). Then every call returned `-429 "WARNING! THIS ENDPOINT IS DEPRECATED! STOP USING IT NOW! Switch to https://fastnear.com…"`. |
| `https://archival-rpc.mainnet.fastnear.com` | Works, node 2.13.4 `44f7ae6c`. Returns `-429 Rate limits exceeded` under bursts, so the harvester throttles to ≥ 0.25 s per call with back-off. Default endpoint of `harvest.py`. |
| `https://rpc.mainnet.fastnear.com`, `https://free.rpc.fastnear.com` | `status` works (non-archival). |
| testnet (`rpc.testnet.near.org`, archival testnet near.org / fastnear) | Reachable, but testnet runs **PV 87**, so it is outside the PV 86 statement. Not used. |
| `https://mainnet.neardata.xyz/v0/block/H` | Block and per-shard JSON with `receipt_execution_outcomes` (incl. outcome merkle proofs) and `state_changes`. Rate limited (HTTP 429). Used only to *find* candidate receipts (`harvest.py candidates`). |
| `query view_account` with `block_id` | Account **values** at a block. No trie nodes. |
| `query view_state` with `include_proof` | Returns trie nodes, but only those visited while iterating `0x09 ‖ account ‖ ','` (contract data). See `runtime/runtime/src/state_viewer/mod.rs:230-325`, which calls `get_raw_prefix_for_contract_data`. The `TrieKey::Account` path (`0x00 ‖ id`) is never revealed. Below the root branch the two paths diverge. |
| other 2.13.4 RPC methods (`chain/jsonrpc/src/lib.rs`) | None of the 51 methods (`EXPERIMENTAL_*` included) returns trie nodes, state parts or chunk state witnesses. |
| `/debug/api/entity` (entity debug API, which can query `TrieNode`s) and `/debug/*` | HTTP 404 on all five public mainnet endpoints (`enable_debug_rpc` is off). |
| Chunk state witnesses (`ChunkStateWitness.main_state_transition.base_state`) | Producers push them to the chunk validators of that height as `PartialEncodedStateWitness`. There is no request message for an arbitrary peer, no RPC, and nodes keep them only with the debug option `save_latest_witnesses`. **Not publicly available.** |
| GCS bucket `state-parts` (legacy external state-sync dumps) | Exists and is publicly listable, but **empty** (`storage/v1/b/state-parts/o` → no objects). Mainnet moved to peer-based state sync. |
| NEAR Lake (S3, requester-pays) | Not tried. It needs AWS credentials and none were created. It also holds state *changes* (values), not trie nodes. |
| **P2P state sync** (`StateRequestHeader` / `StateRequestPart` direct messages) | **Works.** Handled by `chain/network/src/peer_manager/network_state/mod.rs:1235-1248` and `chain/client/src/state_request_actor.rs:260-293`, served from the node's state snapshot. Peers come from `network_info`. Of the first 11 peers asked for a shard-13 part, 1 served it; the others replied with no part (not tracking that shard's snapshot) or timed out. `StateRequestHeader` is answered more widely. |

## 2. What state sync gives, and its limits

nearcore 2.13.4 (`chain/chain/src/state_sync/utils.rs`) defines two blocks for
each epoch:

* `sync_prev`: the first block, not counting the epoch's first block, after
  which every shard has received at least 2 new chunks;
* `sync`: the block after `sync_prev`.

Parts are for the root `sync_prev.chunks[s].prev_state_root`
(`state_sync/adapter.rs:310-316`). That root is the shard state after the
previous new chunk, and it is the pre-state of **one** on-chain chunk: the
shard's chunk in `sync_prev`.

* The header (`ShardStateSyncResponseHeaderV2`) carries `state_root_node`. We
  check `sha256(state_root_node) == prev_state_root`, the RPC chunk-header
  field. The header also carries the full chunk and its incoming-receipt proofs.
* A part is zstd-compressed `PartialState`: every node and value of a contiguous
  slice of the trie (DFS order by `memory_usage`, 30 MiB per part) plus the
  boundary paths. Parts are 7–17 MB on the wire. The four shards used have
  420 (s13), 666 (s12), 1216 (s7), 1235 (s4) and 1127 (s10) parts.
* There is no index from key to part. `harvest.py` bisects on the key range a
  part reveals (`near-arena-historical range`) and fetches neighbouring parts
  when a subtree starts across a boundary. About 8–10 parts are needed per new
  key region.
* A node serves parts only for the **current** epoch's sync hash, and only while
  its snapshot exists. When the next epoch starts (≈ 7 h, `epoch_length` 43 200
  at ~1.71 blocks/s), the root becomes unobtainable.

`Runtime::apply` reads more than the receivers' accounts:

* the value at `0x07` (DelayedReceiptIndices);
* the promise-yield queue (`0x0a`, `0x0b…`);
* buffered-receipt and bandwidth-scheduler keys (`0x0d`, `0x0f`, `0x10`).

The harvester runs nearcore and maps each `MissingTrieValue` hash back to its
trie path (`near-arena-historical whereis`). It then fetches the part holding
that path and retries until the apply succeeds. Each case needed 3 parts: the
receiver's account part, the part holding the `0x07` value, and the tail part
holding `0x0a…0x10`.

Total downloaded in this session: **92 parts ≈ 1.1 GB** over P2P, spread over
shards 4, 7, 12 and 13, plus a few hundred RPC calls. The parts are not
committed. `apply_witness.bin` keeps every node `Runtime::apply` read, about
8 KB per case.

## 3. Receipts: which ones are in the v1 domain

* Receipts that contracts create (promises) are `ReceiptEnum::ActionV2`
  (`runtime/runtime/src/function_call.rs:187`). That variant is excluded from
  v1 (`receipt_enum_action_v2`). RPC `ReceiptView` erases the difference:
  `views.rs:2518-2521` notes that ActionV2 without `refund_to` becomes V1 after
  a round trip through views. A contract-generated transfer therefore cannot be
  reconstructed byte-exactly from RPC.
  * Example: `zcash-client.bridge.near → zcash-relayer.near`. Its trie witness
    was fetched, but the case was dropped.
* Receipts converted from a **Transfer transaction** are `ReceiptEnum::Action`
  (`Receipt::from_tx`, `core/primitives/src/receipt.rs:344-365`). The harvester
  accepts a receipt only if `EXPERIMENTAL_receipt_to_tx` +
  `EXPERIMENTAL_tx_status` show all of the following, so `TryFrom<ReceiptView>`
  reproduces the exact borsh:
  * the transaction's outcome `receipt_ids == [id]`;
  * the same signer, receiver, public key and `[Transfer]` actions;
  * no `refund_to`;
  * `SuccessValue("")` on chain.

## 4. Finding chunks: survey

**Sampled blocks.** Over 100 sampled blocks (heights 218 300 000 + 37·k) we saw
1 621 executed receipts and 20 single-Transfer receipts to named accounts. Most
of those were contract-generated (ActionV2). No chunk consisted only of
in-domain receipts.

**Pure chunks.** In consecutive blocks after the current sync point there are
pure chunks: no transactions and exactly one tx-originated named transfer. An
example is `tx-bench.near → tx-bench-buddy.near` on shard 12, which repeats
every ~20–40 blocks. None of them sits on a sync root.

**Sync-prev chunks.** The only chunks whose pre-state trie is publicly
obtainable are the sync-prev chunks. The last 7 epochs:

| epoch start | sync_prev | receipts executed (all shards) | named single-Transfer | tx-originated (exact-subbatch candidates) | pure |
|---|---|---|---|---|---|
| 218 303 534 (current) | 218 303 536 | 35 | 0 | 0 | 0 |
| 218 260 334 | 218 260 336 | 34 | 1 | 1 (s8 → `bridge-mng.near`, chunk of 7 receipts) | 0 |
| 218 217 134 | 218 217 137 | 52 | 0 | 0 | 0 |
| 218 173 934 | 218 173 936 | 25 | 2 | 0 (contract-generated) | 0 |
| 218 130 734 | 218 130 737 | 45 | 0 | 0 | 0 |
| 218 087 534 | 218 087 536 | 57 | 1 | 1 (s8 → `bridge-mng.near`, chunk of 13 receipts) | 0 |
| 218 044 334 | 218 044 337 | 26 | 0 | 0 | 0 |

An `historical-exact-subbatch` case becomes possible about 2 epochs in 7 (≈ 1
per day). It must be harvested *during* that epoch. No candidate existed in the
current epoch, so **no exact case was produced**. A "pure" exact chunk (the
whole chunk is the batch, so every claim field is on-chain-checkable) was not
seen in any surveyed sync-prev chunk.

PV 86 on mainnet: bisection with `EXPERIMENTAL_protocol_config` gives PV 84 at
height 207 762 733 and PV 86 from 207 762 734. The harvester re-checks PV 86 at
every execution block.

## 5. Fixture classes

| class | pre_state_root | receipts / context | what is on-chain-anchored |
|---|---|---|---|
| `historical-exact-chunk` | = prev_state_root of the chunk that executed the batch | the chunk's own receipts; that block's height and gas price, that chunk's gas limit; the chunk executed nothing else | everything except `slice_post_root` (spec §5). Not produced yet. |
| `historical-exact-subbatch` | as above | an in-domain subset of that chunk's receipts | pre_state_root, receipts, per-receipt outcome leaves (merkle proofs). `outcome_root`, gas and tokens totals do not cover the chunk's other receipts. Receiver records are correct only if no earlier receipt of the chunk touched them, which `receiver_records_identical_to_execution_prestate` checks. Not produced yet (no candidate this epoch). |
| `historical-rebased-prestate` | an on-chain root of the **same shard and epoch** (the sync root), committed *before* the executing chunk | authentic tx-originated receipts with their real execution context | the witness hashes to an on-chain root; receipts, context and PV are authentic. Per-receipt outcome leaves equal the on-chain leaves, which are verified against the chunk outcome root. Totals and refunds equal on-chain values when the chunk was pure. Receiver records are compared with `view_account` at the execution pre-state. **Not anchored:** that the chain applied these receipts to this root (it did not), and `slice_post_root`. |

Every case has a `provenance.json` containing:

* block, chunk and epoch hashes and heights;
* the sync hash and state header;
* every part used: id, sha256, size, peer and retrieval time where recorded;
* the RPC endpoint and retrieval time;
* the receipts with their transaction hashes;
* the claim;
* `anchors`: each check with `ok`, its meaning and the observed values;
* `not_anchored`.

Each case also has a `context.json` (the exact build input: RPC `ReceiptView`s
plus block fields) and a `diagnostics.json` (nearcore observations, file
digests, receiver pre-values).

Part peers for the shard 4 and 7 cases are recorded as "not recorded". They
were downloaded before per-part logging was added. Their sha256 and download
time are recorded.

## 6. The fixtures (`oracle/fixtures/historical/cases/`)

All 4 cases share the same structure:

* PV 86, `mainnet`, batch of 1, block gas price 10^8;
* receipt gas price 10^9, so one gas refund of 200 864 306 250 000 000 000 yN;
* `gas_burnt_total` 223 182 562 500;
* `tokens_burnt_total` 22 318 256 250 000 000 000.

Pre-state root = `sync_prev(218 303 536).chunks[s].prev_state_root` of epoch
`8gCvn4roxttM9mEgH7VpD15wR9BYoiTQEfXDjLbG6LNq`, sync hash
`4UUB8Yb5sv84w5AqQNdPSKSgnxdxypBTr6M8GwGwkPL2`.

| case | shard / root | receipt (tx) | executed at | anchors not ok |
|---|---|---|---|---|
| `mainnet-s12-h218303553` | 12 / `8HP5FZi1…MXA6` | `tx-bench.near → tx-bench-buddy.near` 1 yN, `Hjxdqr…koVj` (tx `59EznD…Su7i`) | 218 303 553, a pure chunk (0 tx, 1 receipt) | only `claim_pre_state_root_is_execution_chunk_prev_state_root`. The claim's `outcome_root` = next chunk's `prev_outcome_root` `BKAAJcwZ…aWe`, gas/tokens = `prev_gas_used`/`prev_balance_burnt`, the refund = the on-chain outgoing receipt `9o7VTy…pW6`, and the receiver record equals the chain's. |
| `mainnet-s12-h218303595` | 12 / same root | same pair, `8YkKjj…xNx` (tx `66tvdY…jafA`) | 218 303 595, pure chunk | as above, plus `receiver_records_identical_to_execution_prestate`. The chain saw amount 245 525, our root has 245 523, because one transfer at 218 303 571 lies between the two roots. This shows a rebased case whose post-value is not the chain's. |
| `mainnet-s7-h218303557` | 7 / `DBwM61Cn…c5as` | `kkaabbiirr81.tg → kkaabbiirr82.tg`, `7tAeeT…pDNr` (tx `FcBGr9…KBYA`) | 218 303 557, chunk of 5 receipts and 2 txs | `…prev_state_root`, `execution_chunk_contains_exactly_the_batch`, `claim_outcome_root_equals_onchain_prev_outcome_root`. The outcome *leaf* still equals the on-chain leaf, which is merkle-verified against the chunk outcome root. |
| `mainnet-s4-h218303545` | 4 / `Hci1hMJL…zRmP` | `crypto10081.tg → swanmaw.tg`, `7Stptk…yW3z` (tx `4PXJoy…JKMa`) | 218 303 545, chunk of 7 receipts and 1 tx | same three as the s7 case. |

**Verification.** Run offline with `oracle/historical/verify.sh`. It ran
2026-10-03 with these results:

* **REPLAY_OK ×4.** nearcore `Runtime::apply` re-runs from
  `apply_witness.bin` alone and reproduces `witness.bin` and
  `expected_claim.bin` byte for byte. The independent Rust domain check
  (`oracle/src/domain.rs`) accepts each case and agrees on burnt tokens and
  refunds.
* **`nearspec-check`: 4 cases, 4 ok.** The compiled Lean semantics derive the
  same claim bytes and `decide (NearRelation c w)` holds on each authentic
  witness. The binary was built from `spec/lean` sources identical to this
  branch's (`diff -r` clean).
* **File digests and anchors consistent.**
* The third differential implementation, `oracle/tools/spec_check.py`, needs
  the full `state.bin`, so it cannot run on partial mainnet state.

**Deviation from the synthetic oracle.** The two shard-12 cases apply a
sync-root state at a later height. There nearcore also removed promise-yield
timeouts that had fallen due: it wrote `0x0a` and `0x0bde36590000000000` (and
`0x0bdf36590000000000` in the 218 303 595 case). The shard 4 and 7 cases had no
such writes. These
writes happen after all incoming receipts, produce no outcome and no receipt,
and lie outside the slice. The historical builder tolerates writes to columns
`0x0a`/`0x0b` and lists them in `diagnostics.json`
(`nearcore.non_slice_writes_tolerated`). Everything else is required "clean",
exactly as in the oracle:

* one `SuccessValue([])` outcome per receipt;
* no delayed receipts;
* outgoing receipts = refunds;
* `decomposition_ok`;
* the witness-only slice root equals the full update.

A v1 claim is still valid, because the relation covers only the slice. It does
mean the `apply_context` assumption (§3 of the spec: no yield receipts) does not
literally hold for the full nearcore apply of these cases.

## 7. What exact historical replay would require

1. **Exact sub-batches (cheap, recurring).** Run
   `harvest.py candidates` shortly after each epoch's sync point (≈ 7 h
   cadence). Then run `harvest.py build` on any tx-originated named Transfer
   executed in a sync-prev chunk, within that epoch. The survey suggests ≈ 1
   candidate per day. Pure exact chunks are much rarer; none appeared in 7
   epochs.
2. **Arbitrary chunks.** The trie nodes at an arbitrary chunk's
   `prev_state_root` require one of:
   * an archival or tracking node with that state: a node tracking the shard
     plus `view_state`-style access to Account paths, or a state snapshot at
     that root;
   * a node configured to keep chunk state witnesses (`save_latest_witnesses`,
     or a chunk validator of that shard and height). The witness's
     `main_state_transition.base_state` is exactly what `Runtime::apply` reads,
     so it is the ideal source;
   * a public service publishing state witnesses (none found).

   Running a node was out of scope here.
3. **Rolling a sync root forward.** This means rebasing to a later root by
   replaying the intermediate chunks of the shard. It is possible in principle
   with the same tooling: apply each intermediate chunk on the partial trie and
   check the root against the next chunk header. But it needs every node those
   chunks read, including contract code and data for every function call
   (on shard 12, 15 of the 17 chunks at heights 218 303 536–552, between the
   sync root and the pure chunk at 218 303 553, executed receipts, mostly
   function calls). Account and state *values* from RPC
   or neardata `state_changes` are not enough: internal keys (delayed and
   buffered queues, bandwidth-scheduler state, yield queue) are not exposed by
   any API.

## 8. Reproducing

```
oracle/scripts/link-nearcore.sh /path/to/nearcore@44f7ae6c
(cd oracle/historical && cargo build -j 8)        # tool: fetch, range, whereis, build, replay
python3 oracle/historical/harvest.py sync-point   # current epoch's sync point and target chunks
python3 oracle/historical/harvest.py candidates   # exact candidates (or --from/--to for rebased)
PARTS_DIR=/scratch/parts python3 oracle/historical/harvest.py build \
    --shard 12 --receipt HjxdqrEkSA3YXkzJAs17X3vdUPAetBfywTAtR3j2koVj --name mainnet-s12-h218303553
NEARSPEC_CHECK=spec/lean/.lake/build/bin/nearspec-check oracle/historical/verify.sh
```

Rebuilding these four cases from scratch is not possible after epoch
`8gCvn4ro…` ends: peers stop serving that root. Verification needs no network.

**Code placement.** The judge's oracle sources (`oracle/src`, `Cargo.toml`,
`Cargo.lock`) are pinned by `generator_digest`, and the spec documents by
`spec_doc_digest`/`spec_digest`. They are deliberately **unchanged**. The
historical builder lives in `oracle/historical/` and has two parts:

* `src/replay.rs` mirrors `oracle/src/exec.rs` for partial tries;
* `oracle/src/enc.rs` and `domain.rs` are compiled in unchanged via
  `#[path]`.

`spec/near-transfer-receipt-v1.md` §10 and `oracle/fixtures/public/provenance.json`
still say historical replay is unavailable. Both are digest-pinned, so they stay
unchanged; this document supersedes them until the next spec version.
