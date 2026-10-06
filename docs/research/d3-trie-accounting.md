# D3: trie-node accounting of contract storage (the trie-backed `External`)

Status: spec module `spec/lean/v3/NearSpecV3/Wasm/TrieAccounting.lean` (compiles; no sorry/axiom;
**not yet difftested op-by-op**: RuntimeD3 will wire it into `Host.lean` in place of the mock
External). The node-independence claim below is backed by a source argument plus an experiment on a
real multi-shard TestEnv (`oracle/d3-ttn`). nearcore 2.13.4 (44f7ae6), PV86.

## 1. The question

Contract storage ops charge `wasm_touching_trie_node` (TTN) and `wasm_read_cached_trie_node` per
trie node touched. A chunk producer applies a chunk against local state (flat storage, optionally
memtries). A stateless validator applies the same chunk against the witness's recorded partial trie
(no flat storage, no memtries). If those two paths counted trie nodes differently, they would
compute different gas for the same receipt. Since `gas_burnt` is part of the outcome root
(`PartialExecutionOutcome`, `transaction.rs:746-752`) and compute decides how many receipts fit in
a chunk, that would be a consensus hazard.

## 2. Answer: both paths count the same, by construction

| Path | Trie constructed by | `use_access_tracker` | Reads / has_key (`MemOrFlatOrTrie`) | Writes / removes (`MemOrTrie`) |
|---|---|---|---|---|
| Producer, flat storage (no memtrie) | `get_trie_for_shard(.., use_flat_storage=true)` → `get_trie_with_block_hash_for_shard` (`chain/chain/src/runtime/mod.rs:682-697`) → `Trie::new_with_memtries` | `false` (`core/store/src/trie/mod.rs:625-640`) | flat-storage lookup, no node tracked (`mod.rs:1527-1545`) | state-column walk, every node tracked |
| Producer, memtries | same, `memtries = Some` | `false` | `lookup_from_memory(.., false)`, no node tracked (`mod.rs:1342-1380`) | `lookup_from_memory(.., true)`, every node tracked |
| Producer, no flat storage for the shard | `Trie::new` | `false` | state-column walk, untracked | tracked |
| Stateless validator | `apply_new_chunk` hard-codes `use_flat_storage: true` (`chain/chain/src/update_shard.rs:159-161`); `StorageDataSource::Recorded` → `Trie::from_recorded_storage(.., true)` (`runtime/mod.rs:1243-1247`) | `!flat_storage_used = false` (`mod.rs:715-735`) | state-column walk over the partial storage, untracked | tracked |
| `DbTrieOnly` (replay tool, not consensus) | `set_use_trie_accounting_cache(false)` (`runtime/mod.rs:1230-1241`) | `false` | untracked | tracked |

Further pieces, all identical on every path:

* `StorageGetMode` is a protocol parameter (`flat_storage_reads`, `core/parameters/src/parameter_table.rs:461`), not node configuration. It selects `MemOrFlatOrTrie` for `storage_read`/`storage_has_key` and `MemOrTrie` for `storage_write`/`storage_remove` (`runtime/runtime/src/ext.rs:147-313`).
* `get_optimized_ref` tracks the nodes of a lookup iff `mode == MemOrTrie || use_access_tracker` (`mod.rs:1527-1545`; `contains_key_mode` is the same, `mod.rs:1486-1515`).
* A value dereference is always tracked: `retrieve_value` calls `internal_retrieve_trie_node(.., true)` (`mod.rs:1461-1468`), and `deref_optimized` tracks `hash(value)` for inlined values (`mod.rs:1551-1575`).
* The memtrie walk and the state-column walk visit the same node hashes. The memtrie serializes each node with `to_raw_trie_node_with_size`, which has the same hash. This is the one claim the source argument does not settle and the experiment does.
* `AccountingState` is created once per chunk application (`chain/chain/src/runtime/mod.rs:340`) and shared by all receipts of the chunk (`function_call.rs:73`).
* Recording happens on both paths: `apply_chunk` wraps every trie in `recording_reads_with_proof_size_limit` (`runtime/mod.rs:1252-1258`), so the per-receipt `storage_proof_size_receipt_limit` checks after each storage op (`wasmtime_runner/logic.rs:4510,4605,4670,4730`) see a recorder on both sides.

The validator's `use_flat_storage = true` is what makes this work. The validator has no flat storage, but it simulates its cost model ("used to simulate the same costs as if flat storage were present", `mod.rs:707-713`), so reads are free of node charges on both sides.

## 3. Experiment (`oracle/d3-ttn`, new crate; `oracle/v3` is frozen)

The experiment runs a real `TestEnv`: 4 shards, 8 validators, mainnet `RuntimeConfigStore::new(None)`, PV86, and real witness production. Each shard has a storage-heavy contract (`ttn.wat`). Its `run` method executes 1–40 random write/read/has_key/remove ops over 2- and 3-byte keys, with value sizes 1, 100 or 4500. Keys overlap with pre-populated genesis data and with each other, so cache hits within and across receipts do occur. 30% of transactions use tight prepaid gas (3–40 Tgas), so out-of-gas lands at varied points. 60 blocks per run.

For every witness a chunk producer emits, the same chunk is compared three ways:

* **P (producer):** the outcomes the producer stored while processing the block. Its storage was flat storage, with memtries iff `--memtries` (checked with `get_memtries(shard_uid).is_some()` per chunk).
* **V (validator):** `pre_validate_chunk_state_witness`, then `update_shard::apply_new_chunk(ValidateChunkStateWitness, ..)`, which is exactly what `validate_chunk_state_witness_impl` runs.
* **A (ablation):** the same recorded storage applied with `use_flat_storage = false`, so reads are also tracked.

On top of the three-way comparison, nearcore's full witness judge runs on every witness. Comparisons are made on the borsh bytes of each `ExecutionOutcome`: gas, tokens, status, logs, receipt ids, and the metadata including the full gas profile. Chunk `gas_used` is compared too.

| seed | producer memtries | chunks | outcomes | outcomes with TTN charges | P≠V outcomes | chunk gas P≠V | judge ok/fail | A≠V outcomes (chunks) |
|---|---|---|---|---|---|---|---|---|
| 1 | off | 236 | 1891 | 612 | 0 | 0 | 240/0 | 619 (212) |
| 1 | on (236/236 chunks) | 236 | 1891 | 612 | 0 | 0 | 240/0 | 619 (212) |
| 2 | off | 236 | 2037 | 657 | 0 | 0 | 240/0 | 663 (218) |
| 2 | on | 236 | 2037 | 657 | 0 | 0 | 240/0 | 663 (218) |
| 3 | off | 236 | 2023 | 656 | 0 | 0 | 240/0 | 662 (217) |
| 3 | on | 236 | 2023 | 656 | 0 | 0 | 240/0 | 662 (217) |

* The memtries-off and memtries-on runs of the same seed produce identical per-chunk digests: 236/236 chunks, covering new root, chunk gas, and every outcome's hash, gas, compute and TTN/cached split (`compare_memtries.py`, `runs/memtrie-compare.txt`). So the memtrie walk and the state-column walk charge identically.
* The ablation shows the comparison is sensitive. Counting read nodes changes 619–663 outcomes per run and roughly 2.3x the cached-node gas. Reproduce with: `near-d3-ttn --seed S --blocks 60 [--memtries] --out runs/sS.json` (build under `heavy` + `taskset`).

**Conclusion:** no consensus hazard found. Producer (flat storage, memtries on or off) and stateless validator compute identical outcomes, including the full profile, for the same chunk.

**What this does not cover:**

* Resharding transitions. The validator's `from_recorded_storage(.., true)` at `chunk_validation.rs:709` was checked by source only.
* The storage-proof size limit actually triggering (4 MB per receipt).
* Producers with flat storage absent at a non-genesis height.

## 4. The spec (prose; Lean: `TrieStore.lean`, `TrieAccounting.lean`, `ChunkStorage.lean`)

This section is the normative prose: the clean-room implementation is written from it, not from the
Lean modules.

### 4.1 State

* **Pre-state.** `prev_state_root` (32 bytes) and the witness's recorded storage: a set of byte
  strings, each addressed by its SHA-256. Every receipt of the chunk reads the trie at this one root;
  writes never change the root during the chunk.
* **Overlay.** A map from full trie key to `value | removed`, holding the chunk's writes so far
  (the committed changes of earlier receipts plus the current receipt's own). The full trie key of a
  contract storage key `k` of account `a` is `0x09 ‖ utf8(a) ‖ 0x2c (',') ‖ k`.
* **Accounting cache.** A set of 32-byte hashes, with counters `db` and `mem`. It is created empty
  once per chunk and shared by every receipt of the chunk, across accounts. It is never rolled back.
  *Touching* a hash `h` means: if `h` is in the set then `mem += 1`; otherwise `db += 1` and `h` is
  added to the set.

### 4.2 Trie nodes and lookup

A node is `borsh(RawTrieNodeWithSize)`: the node body, then an 8-byte little-endian
`memory_usage` (ignored here). The body is a 1-byte tag:

* `0` Leaf: `u32 LE len` + hex-prefix-encoded key (`len` bytes) + value ref = `u32 LE value
  length` + 32-byte value hash.
* `1` BranchNoValue: `u16 LE` child bitmap (bit `i` set means child `i` is present), then one 32-byte
  hash per present child in index order.
* `2` BranchWithValue: value ref (`u32` length + hash), then bitmap and children as in tag `1`.
* `3` Extension: `u32 LE len` + hex-prefix key + 32-byte child hash.

Hex-prefix: in the first byte, the high nibble `f` has bit 0 set for an odd nibble count (and then
the low nibble is the first key nibble; otherwise it must be 0), and bit 1 set for a leaf key; the
remaining bytes give two nibbles each, high nibble first.

**Lookup** of key `K` (as nibbles, high nibble first) from the root:

* An all-zero root means the empty trie: no node is retrieved and the key is absent.
* Otherwise retrieve node `h`: a hash missing from the recorded storage is a storage error
  (`MissingTrieValue`). Record `h` in the visited list.
  * Leaf: the key is present iff its key equals the remaining nibbles. Stop.
  * Extension: if its key is a prefix of the remaining nibbles, consume it and continue at the
    child. Otherwise absent; stop.
  * Branch: if no nibbles remain, the result is the branch's value (if any). Stop. Otherwise take
    the child at the next nibble and continue, or report absent if there is no such child.

The lookup returns the visited node hashes, root first, plus the value ref `(length, hash)` when
the key is present. Absence is also decided by the last node visited.

### 4.3 The four operations

Gas: `TTN` = `wasm_touching_trie_node`, `CACHED` = `wasm_read_cached_trie_node`. *Commit since
snapshot `(db₀, mem₀)`* means: charge `TTN × (db − db₀)`, then `CACHED × (mem − mem₀)`. Each is a
`pay_per`, recorded under its own profile key. The base, key and value charges that precede these
steps, and the register writes that follow them, are those of Appendix A; listed here is only what
happens inside the `External` call.

**storage_write(k, v)** and **storage_remove(k)** (B = `storage_write_evicted_byte` /
`storage_remove_ret_value_byte`): take a snapshot.
1. If the overlay has the key: if it holds a value `old`, charge `B × len(old)` and return `old`.
   If it holds `removed`, return nothing. No trie access, no touches.
2. Otherwise look the key up in the trie. Touch every visited node. If a value is present:
   charge `B × length` (on failure, stop here; the touches stay in the cache uncharged), then touch
   the value hash and fetch the value (missing means a storage error). Then commit since the
   snapshot. Return the value, if any.
3. Then the overlay gets `k ↦ v` (write) or `k ↦ removed` (remove). A remove records `removed`
   even when the key was absent.

**storage_read(k)**:
1. If the overlay has the key with a value: charge `storage_read_value_byte × len`, and if
   `len > 4000` also `storage_large_read_overhead_base` and `storage_large_read_overhead_byte ×
   len`. Return the value. No touches. If it holds `removed`: absent.
2. Otherwise look the key up. **No node is touched.** The commit happens but charges 0. If present:
   apply the same value charges as in step 1, then touch the value hash **without charging**
   (it enters the cache and increments `db`/`mem`, but no gas), then fetch the value.

**storage_has_key(k)**: overlay first, otherwise a trie lookup. Nothing is touched and nothing is
charged by the `External`. A missing node is still a storage error.

### 4.4 Across the chunk

Contract calls run in the chunk's execution order (the order of its outcomes). The cache persists
through every call, failed or not. A call's overlay changes are kept iff its receipt succeeds; a
failed receipt (any error, including out of gas) rolls back to the overlay before the call.

Subtleties the spec keeps:

1. A failed evicted/removed-bytes charge leaves the path touches in the cache, uncharged.
2. A read's value dereference warms the cache (uncharged) for a later write or remove of the same
   key.
3. Keys written or removed earlier in the chunk touch nothing, even across receipts.

**At PV86 the cache does not affect gas.** Since PV82, `wasm_touching_trie_node` =
`wasm_read_cached_trie_node` = 2,280,000,000 gas and 4,000,000,000 compute (`runtime_configs/82.yaml`;
`theorem ttn_costs_equal`, proved by `rfl`). So gas and compute depend only on the number of tracked
accesses. The cache only decides the profile split, which is not consensus data (the outcome root
hashes `PartialExecutionOutcome`, which has no metadata). The split is still modelled exactly and
difftested.

### 4.5 Storage-proof recording and the per-receipt limit

* **Recorder.** One per chunk application, never rolled back (`TrieRecorder`,
  `trie_recording.rs`; `recording_reads_with_proof_size_limit`, `runtime/mod.rs:1258`). It holds a set
  of recorded hashes and a counter `upper_bound`. Recording a hash that is not yet in the set adds
  it and adds its byte length (the stored node or value bytes) to `upper_bound`. Recording an
  already-recorded hash does nothing.
* **What is recorded.** On a trie lookup (overlay miss), every visited node, in any mode,
  including `storage_read` and `storage_has_key`, which charge no trie nodes. On a dereference, the
  value: for `storage_read` after the value charges succeed, for write/remove after the
  evicted/removed-bytes charge. An overlay hit records nothing.
* **Removals.** Every `storage_remove` adds 2000 to `upper_bound`, whether or not the key exists,
  even when the overlay already has it removed (`TrieUpdate::remove` → `record_key_removal`,
  `update.rs:169-181`). This happens after the value dereference and before the trie-node commit.
* **Receipt start.** Before the receipt's snapshot `before = upper_bound`
  (`storage_proof_size_before_receipt`, `runtime/runtime/src/lib.rs:838-845`), the runtime reads the
  receiver's account (`TrieKey::Account` = `0x00 ‖ utf8(account)`). This records the nodes on that
  path and the account value. The model records exactly that path and value at each call start;
  it happens before the snapshot, so it never counts toward the receipt's growth, but it pre-records
  the top nodes that contract-data paths share with it (clean-room T10). Nothing else between the
  snapshot and the VM records anything: `record_contract_call` uses `NO_SIDE_EFFECTS`
  (`function_call.rs:355-390`).
* **Deduplication is by hash, chunk-wide.** Byte-identical subtrees under different accounts (in
  the v2 experiment every contract has the same genesis `f` subtree) have identical node hashes, so
  a receipt's growth depends on what *earlier receipts of other accounts* recorded in the same chunk
  (clean-room T11). The spec is exact here because its recorder is a hash set shared by the chunk.
* **Check.** After every storage operation (`observe_size`, `logic.rs:4510, 4605, 4670, 4730`; for
  `storage_read`, after the value charges and before the register write): if
  `upper_bound − before > 4,000,000` (`per_receipt_storage_proof_size_limit`, `69.yaml`), the call
  fails with `HostError::RecordedStorageExceeded`. Exactly 4,000,000 passes.

## 5. Op-level difftest

`near-d3-ttn --trace FILE` writes one line per chunk:

```
C <prev_root> <n> <node>… <k> (<account> <prepaid> <args|-> <ok|fail:KIND> <wasm> <ext_total> <s0>…<s10>)…
```

`KIND` is the `HostError` variant name (`GasExceeded`, `GasLimitExceeded`,
`RecordedStorageExceeded`, …); otherwise it is the variant inside `FunctionCallError(…)`. The
runtime stores a host error only as its display text, which the generator maps back to the
variant. The calls are every outcome executed by a contract account (`*ctr*`, `*big`), in outcome
order. Promise-created calls are included, with their contents taken from the outgoing receipts of
the chunk that created them. `--v2` uses `ttn2.wat`: 8 storage contracts (2 per shard) plus
`s0big`/`s1big`, which hold 8 values of 0.45–0.71 MB each, and promise DAGs
(`promise_create`/`promise_then` to other contracts, args nested in the input). Their contents come
from the transactions the generator submitted (receipt id taken from the transaction's conversion
outcome). The expected columns are nearcore's outcome profile. The slot order is
`storage_write_base, storage_read_base, storage_read_key_byte, storage_read_value_byte,
storage_large_read_overhead_base, storage_large_read_overhead_byte, storage_remove_base,
storage_has_key_base, storage_has_key_byte, touching_trie_node, read_cached_trie_node`.

`difftest_ttn.py TRACE` replays every chunk with the Lean spec (`nearspec-v3-wasm --chunk`:
`ChunkStorage.replayChunk` → `Exec.runCall` with a `RealStore` → `Host` storage → `TrieAccounting`)
and compares each call's status, wasm gas, ext total and the 11 slots. The ext total includes the
evicted/removed-byte charges, every other host cost, and the contract-loading fee
(`contract_loading_base` + `contract_loading_bytes × code size`), which is profiled as ext gas, not
wasm gas (clean-room finding T1). Results: §5.1.

### 5.1 Results (op-level, Lean spec vs nearcore)

There were 15 trace runs: seeds 1–3 with `--ops 40` and `--ops 300` over 60 blocks; seed 4 with `--ops 300 --memtries` over 60 blocks; seeds 5–12 with `--ops 200` over 100 blocks, memtries on for the even seeds.

| | chunks | contract calls | failed calls (mostly out of gas mid-run) | calls with trie-node charges | disagreements |
|---|---|---|---|---|---|
| total | 4,820 | 14,036 | 764 | 13,536 | **0** |

* Every profile slot is exercised. In the 300-op runs, more than 90% of calls have a nonzero value in each of the 11 slots (`runs/*.difftest`).
* The difftest is sensitive. On seed 1 with 300 ops, the deliberately wrong replays disagree on 414 of 667 calls (fresh cache per call, `--ablate-cache`) and on 423 of 667 (no committed overlay between calls, `--ablate-overlay`).
* Producer vs validator stayed at 0 outcome differences on every run, with all witnesses endorsed by nearcore.
* On seed 8, the use_flat_storage=false ablation hit a `MissingTrieValue` once. Counting read nodes changed gas enough that execution took a different path and needed a node the witness does not record. It is counted as a differing chunk (`ablation_storage_errors`). This is expected behaviour of the ablation, not a finding about nearcore.

### 5.2 Multiple contracts, promise DAGs, and the per-receipt storage-proof limit (checkpoint 3c)

**Multiple contracts and cross-contract chains (`--v2`, `ttn2.wat`).** Each shard has two storage
contracts. `run` creates `promise_create` / `promise_then` chains to any of the 8 contracts, and
nests each child's ops in its args. Each child therefore runs in a later chunk, possibly on another
shard, and can spawn further children. Every chunk interleaves calls of several contracts that share
the chunk's cache and recorder. In 6 runs (seeds 21–26, 80 blocks, `--ops 200`, memtries on for the
even seeds) there were 1,896 chunks and 46,574 calls, of which 16,891 failed (all `GasExceeded`:
children carry 5–20 Tgas) and 19,293 had trie-node charges. Lean vs nearcore had **0
disagreements**. Producer vs validator had 0 outcome differences on every run, and every witness
was endorsed. Most calls are promise-created: a run submits on the order of a thousand transactions
(an estimate from the generator's rates, not counted). Two v1 regression runs (seeds 31–32, 1,309
calls) also had 0 disagreements.

**Per-receipt storage-proof limit (§4.5).** The `s0big`/`s1big` contracts hold 8 values of
0.45–0.71 MB each, and no random traffic reaches them. Planned receipts (`--limit-plan`) read 7 of
the values, then remove one key repeatedly (+2000 each), then read small values of length
1–256 bytes. The clean-room implementation calibrated the plans with its own model, and the runs
were then made with nearcore. `runs/limit/` holds the plans, `run.sh`, the difftests, and each
planned receipt's growth as computed by the spec (`--deltas`):

| growth (bytes) | receipts | nearcore | spec |
|---|---|---|---|
| 4,000,000 (exactly the limit) | 3 | ok | ok |
| 4,000,001 (one over) | 2 | `RecordedStorageExceeded` | `RecordedStorageExceeded` |
| 3,997,449 – 3,999,878 | 15 | ok | ok |
| 4,000,021 – 4,001,743 | 4 | `RecordedStorageExceeded` | `RecordedStorageExceeded` |
| 3,255,933 – 3,256,056 (clearly under) / 4,645,178 (clearly over) | 3 / 3 | ok / fail | ok / fail |
| 605 – 728 (one-op control receipts) | 8 | ok | ok |

The three limit traces (2,639 calls, of which 9 hit `RecordedStorageExceeded`) also had 0
disagreements on every column. The clean-room agrees with nearcore on the same cases and on its own
traces (findings T10–T16 in its README). Its ablations show that each rule of §4.5 is needed: the
strict `>`, the +2000 per remove, read recording, has_key recording, and the account read before the
snapshot.
