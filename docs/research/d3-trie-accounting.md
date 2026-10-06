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

## 4. The spec (`TrieAccounting.lean`)

Inputs for one op are:

* the chunk's pre-state trie (`PTrie` at `prev_state_root`; every receipt of the chunk reads through it);
* the chunk's write overlay (`TrieUpdate` prospective and committed changes, `update.rs:118-145`);
* the chunk-scoped cache `Acct`.

`lookupPath` mirrors `lookup_from_state_column`. It lists the node hashes retrieved, root first, including the last node when the key is absent. Reaching an unrevealed node yields `MissingTrieValue`.

| op | overlay hit | overlay miss |
|---|---|---|
| `storage_write` / `storage_remove` | no touches. `evicted`/`removed_byte × len` charged if a value was present | track every path node, then charge `evicted/removed_byte × len` if a value is present, then track `hash(value)`, then `TTN × Δdb` and `cached × Δmem` |
| `storage_read` | value charges only | no node tracked (TTN/cached charged ×0). Value bytes and large-read overhead are charged, then `hash(value)` enters the cache **uncharged** (`deref` with `FreeGasCounter`, `logic.rs:4600`; `ext.rs:70-86`) |
| `storage_has_key` | none | none |

Subtleties the spec keeps:

1. The cache lives for the whole chunk, crosses receipts and accounts, and is not rolled back when a receipt fails.
2. A failed evicted-bytes charge leaves the path touches in the cache, uncharged.
3. A read's value dereference warms the cache for a later write or remove of the same key.
4. Keys written or removed earlier in the chunk (overlay) touch nothing. This holds even across receipts, because the root is fixed per chunk.

**At PV86 the cache does not affect gas.** Since PV82, `wasm_touching_trie_node` = `wasm_read_cached_trie_node` = 2,280,000,000 gas and 4,000,000,000 compute (`runtime_configs/82.yaml`; `theorem ttn_costs_equal`, proved by `rfl`). So gas and compute depend only on the number of tracked accesses. The cache only decides the profile split, which is not consensus data (outcome root hashes `PartialExecutionOutcome`, which has no metadata). The split is still modelled exactly.

**Remaining work (RuntimeD3):** replace the mock storage in `Host.lean` with `TTN.storage*` over the D2 trie/overlay state and thread `Acct` through the chunk. Then difftest per outcome against `oracle/d3-ttn`'s digests, which already record per-outcome `ttn`/`cached` gas for 5,951 outcomes (1,925 of them with trie-node charges).
