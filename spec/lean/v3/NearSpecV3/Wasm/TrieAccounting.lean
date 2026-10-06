import NearSpecV3.Wasm.Machine

/-!
# Trie-node accounting of contract storage (the trie-backed `External`)

The trie-node (TTN) and value-dereference part of contract storage gas at PV86. `Host.lean` uses
these functions when the call runs against a `RealStore` (chunk replay, `nearspec-v3-wasm --chunk`);
without one it keeps the mock `External` of the harness. Full argument and citations:
`docs/research/d3-trie-accounting.md`; experiment and op-level difftest: `oracle/d3-ttn`.

**Node-independence.** The charges are a function of the chunk's *pre-state trie*
(`prev_state_root`, through which every receipt of the chunk reads), the chunk's *write overlay*
(`TrieUpdate` prospective + committed changes) and a chunk-scoped *accounting cache*; they do not
depend on how a node stores state:
* `StorageGetMode` is a protocol parameter (`flat_storage_reads`, `parameter_table.rs:461`), so
  `storage_read`/`storage_has_key` use `KeyLookupMode::MemOrFlatOrTrie` and
  `storage_write`/`storage_remove` use `MemOrTrie` (`runtime/runtime/src/ext.rs:147-313`);
* `Trie::get_optimized_ref` tracks the nodes of a lookup iff `mode = MemOrTrie ∨ use_access_tracker`
  (`core/store/src/trie/mod.rs:1527-1545`), and `use_access_tracker` is `false` on every
  consensus path (producer `Trie::new_with_memtries`, `mod.rs:625-640`; validator
  `from_recorded_storage(.., true)`, `update_shard.rs:159-161`, `mod.rs:715-735`);
* memtrie and state-column lookups visit the same node hashes; a value dereference is tracked on
  every backend (`deref_optimized`, `retrieve_value`, `mod.rs:1461-1575`).

**The cache does not change gas at PV86.** Since PV82 `wasm_touching_trie_node` and
`wasm_read_cached_trie_node` have equal gas (2,280,000,000) and compute (4,000,000,000)
(`runtime_configs/82.yaml`); the cache only decides the profile split between the two keys.
-/

namespace NearSpecV3.Wasm.TTN

open NearSpecV3.Wasm

/-- `commit_counts_since(snapshot)`: `trie_node_touched(Δdb)` then `cached_trie_node_access(Δmem)`
(`ext.rs:700-718`, `gas_counter.rs:399-406`). -/
def commit (gs : Gas) (start a : Acct) : Gas × Option String :=
  match payPer gs C.touchingTrieNode (a.db - start.db) with
  | (gs, some e) => (gs, some e)
  | (gs, none) => payPer gs C.readCachedTrieNode (a.mem - start.mem)

/-- Result of the External side of one storage op. `old` = the current value (to return in a
register); `err` = a gas error (`payPer` text) or a storage error. -/
structure Out where
  gs : Gas
  acct : Acct
  /-- the recorder after the op: lookups record every retrieved node, dereferences the value
  (also when a later charge fails: recording is not rolled back) -/
  recd : Recorder
  old : Option ByteArray := none
  err : Option String := none

/-- The value behind a reference, from the recorded storage. -/
def deref (r : RealStore) (vh : ByteArray) : Except String ByteArray :=
  match r.store vh with
  | some v => .ok v
  | none => .error errMissing

/-- `storage_set` / `storage_remove` (`ext.rs:147-182, 232-268`): `get_ref(MemOrTrie)`. An overlay
hit touches nothing; otherwise every node of the path is tracked. If a value is present,
`{evicted|removed}_byte × len` is charged *before* the value is dereferenced (tracked); then the
deltas are committed. A failed byte charge returns before the commit: the path touches stay in
the cache uncharged. -/
def writeLike (byteCost : Cost) (r : RealStore) (key : ByteArray) (gs : Gas) : Out :=
  let a := r.acct
  let rc := r.recd
  match r.overlay.get? key with
  | some none => { gs, acct := a, recd := rc }
  | some (some v) =>
    match payPer gs byteCost v.size with
    | (gs, some err) => { gs, acct := a, recd := rc, err := some err }
    | (gs, none) => { gs, acct := a, recd := rc, old := some v }
  | none =>
    match lookup r.store r.root key with
    | .error err => { gs, acct := a, recd := rc, err := some err }
    | .ok l =>
      let a1 := a.touchAll l.nodes
      let rc := rc.recordNodes r.store l.nodes
      match l.value with
      | none =>
        let (gs, e) := commit gs a a1
        { gs, acct := a1, recd := rc, err := e }
      | some (len, vh) =>
        match payPer gs byteCost len with
        | (gs, some err) => { gs, acct := a1, recd := rc, err := some err }
        | (gs, none) =>
          let a2 := a1.touch vh
          match deref r vh with
          | .error err => { gs, acct := a2, recd := rc, err := some err }
          | .ok v =>
            let rc := rc.record vh v.size
            let (gs, e) := commit gs a a2
            { gs, acct := a2, recd := rc, old := some v, err := e }

def storageWrite := writeLike C.storageWriteEvictedByte
def storageRemove := writeLike C.storageRemoveRetValueByte

/-- `TrieUpdate::remove` of a contract-data key: +2000 to the recorder's upper bound, also when the
key is absent (`update.rs:169-181`). -/
def removeRecord (r : RealStore) : RealStore := { r with recd := { r.recd with size := r.recd.size + 2000 } }

/-- `storage_get` (`ext.rs:189-230`) + `storage_read` (`logic.rs:4571-4605`): `MemOrFlatOrTrie`
tracks no node (both commits charge 0) but records them; the logic then charges value bytes (and
the large-read overhead for `len > 4000`) and dereferences with a `FreeGasCounter`: the value hash
enters the cache *uncharged* and the value is recorded, only after every value charge succeeded. -/
def storageRead (r : RealStore) (key : ByteArray) (gs : Gas) : Out :=
  let a := r.acct
  let rc := r.recd
  let valueCharges (gs : Gas) (len : Nat) : Gas × Option String :=
    match payPer gs C.storageReadValueByte len with
    | (gs, some err) => (gs, some err)
    | (gs, none) =>
      if len > 4000 then
        match payBase gs C.storageLargeReadOverheadBase with
        | (gs, some err) => (gs, some err)
        | (gs, none) => payPer gs C.storageLargeReadOverheadByte len
      else (gs, none)
  match r.overlay.get? key with
  | some none => { gs, acct := a, recd := rc }
  | some (some v) =>
    let (gs, e) := valueCharges gs v.size
    { gs, acct := a, recd := rc, old := some v, err := e }
  | none =>
    match lookup r.store r.root key with
    | .error err => { gs, acct := a, recd := rc, err := some err }
    | .ok l =>
      let rc := rc.recordNodes r.store l.nodes
      match l.value with
      | none => { gs, acct := a, recd := rc }
      | some (len, vh) =>
        match valueCharges gs len with
        | (gs, some err) => { gs, acct := a, recd := rc, err := some err }
        | (gs, none) =>
          match deref r vh with
          | .error err => { gs, acct := a.touch vh, recd := rc, err := some err }
          | .ok v => { gs, acct := a.touch vh, recd := rc.record vh v.size, old := some v }

/-- `storage_has_key` (`ext.rs:270-297`): `MemOrFlatOrTrie`, nothing tracked or dereferenced; the
path is recorded. -/
def storageHasKey (r : RealStore) (key : ByteArray) (gs : Gas) : Out :=
  let a := r.acct
  match r.overlay.get? key with
  | some old => { gs, acct := a, recd := r.recd, old := old }
  | none =>
    match lookup r.store r.root key with
    | .error err => { gs, acct := a, recd := r.recd, err := some err }
    | .ok l => { gs, acct := a, recd := r.recd.recordNodes r.store l.nodes,
                 old := l.value.map fun _ => ByteArray.empty }

/-- `RecordedStorageCounter::observe_size` (`logic/recorded_storage_counter.rs:19-33`), called after
every storage op (`logic.rs:4510, 4605, 4670, 4730`): the receipt's recorded growth must not
exceed the per-receipt limit. -/
def overLimit (r : RealStore) : Bool := r.recd.size - r.recBefore > perReceiptProofLimit

/-- At PV86 both trie-node keys cost the same, so the cache is gas- and compute-irrelevant. -/
theorem ttn_costs_equal : C.touchingTrieNode.gas = C.readCachedTrieNode.gas ∧
    C.touchingTrieNode.compute = C.readCachedTrieNode.compute := ⟨rfl, rfl⟩

end NearSpecV3.Wasm.TTN
