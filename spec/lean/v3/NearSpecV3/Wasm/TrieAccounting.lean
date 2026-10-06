import NearSpec.TrieUpsert
import NearSpecV3.Wasm.Machine

/-!
# Trie-node accounting of contract storage (the trie-backed `External`)

The spec of the trie-node (TTN) part of contract storage gas at PV86, used by RuntimeD3 in place of
the mock `External` (which charges no trie nodes). Full argument and citations:
`docs/research/d3-trie-accounting.md`; experiment: `oracle/d3-ttn`.

**Node-independence.** The charges are a function of the chunk's *pre-state trie* (the
`prev_state_root` every receipt of the chunk reads through), the chunk's *write overlay*
(`TrieUpdate` prospective + committed changes) and a chunk-scoped *accounting cache*; they do not
depend on how a node stores state:
* `StorageGetMode` is a protocol parameter (`flat_storage_reads`, `parameter_table.rs:461`), so
  `storage_read`/`storage_has_key` use `KeyLookupMode::MemOrFlatOrTrie` and
  `storage_write`/`storage_remove` use `MemOrTrie` (`runtime/runtime/src/ext.rs:147-313`);
* `Trie::get_optimized_ref` tracks the nodes of a lookup iff `mode = MemOrTrie ∨ use_access_tracker`
  (`core/store/src/trie/mod.rs:1527-1545`), and `use_access_tracker` is `false` on every
  consensus path: `Trie::new_with_memtries` (producer, memtrie / flat / state column,
  `mod.rs:625-640`) and `Trie::from_recorded_storage(.., flat_storage_used = true)` (validator:
  `apply_new_chunk` hard-codes `use_flat_storage: true`, `update_shard.rs:159-161`;
  `from_recorded_storage` sets `use_access_tracker = !flat_storage_used`, `mod.rs:715-735`);
* the memtrie lookup (`lookup_from_memory`, `mod.rs:1342-1380`) and the state-column lookup
  (`lookup_from_state_column`, `mod.rs:1270-1330`) visit the same node hashes; a value dereference
  is tracked on every backend (`deref_optimized`, `retrieve_value`, `mod.rs:1461-1575`).

**The cache does not change gas at PV86.** Since PV82 `wasm_touching_trie_node` and
`wasm_read_cached_trie_node` have equal gas (2,280,000,000) and compute (4,000,000,000)
(`runtime_configs/82.yaml`), so only the *number* of tracked accesses enters gas/compute; the
cache only decides the profile split between the two keys. It is modelled exactly anyway.
-/

namespace NearSpecV3.Wasm.TTN

open NearSpec NearSpecV3.Wasm

/-- What one lookup of a key visits in the pre-state trie, in order: the node hashes retrieved by
`lookup_from_state_column` (root first, the last one included even when the key is absent), and the
value reference `(length, hash)` when the key is present. -/
structure Lookup where
  nodes : List Bytes
  value : Option (Nat × Bytes)
  deriving Repr, Inhabited

def Slot.ref' : Slot → Nat × Bytes
  | .val v => (v.length, sha256 v)
  | .ref len h => (len, h)

mutual
/-- `lookup_from_state_column` on a partial trie (`mod.rs:1270-1330`). An unrevealed node on the path
is `MissingTrieValue` (the validator's storage error; the producer's witness records every node
it visits, so an honest witness never hits it). -/
def lookupPath : PTrie → List Nat → Except String Lookup
  | .hash _, _ => .error "StorageInconsistentState(MissingTrieValue)"
  | t@(.leaf k v _), key =>
    .ok { nodes := [t.hashOf], value := if k == key then some (Slot.ref' v) else none }
  | t@(.ext k c _), key =>
    if isPrefix k key then
      (lookupPath c (key.drop k.length)).map fun l => { l with nodes := t.hashOf :: l.nodes }
    else .ok { nodes := [t.hashOf], value := none }
  | t@(.branch v _ _), [] => .ok { nodes := [t.hashOf], value := v.map Slot.ref' }
  | t@(.branch _ cs _), n :: rest =>
    (lookupKids cs n rest).map fun l => { l with nodes := t.hashOf :: l.nodes }
def lookupKids : Kids → Nat → List Nat → Except String Lookup
  | .nil, _, _ => .ok { nodes := [], value := none }
  | .none _, 0, _ => .ok { nodes := [], value := none }
  | .some c _, 0, key => lookupPath c key
  | .none r, i + 1, key => lookupKids r i key
  | .some _ r, i + 1, key => lookupKids r i key
end

/-- Lookup from the root; the empty trie retrieves nothing (`retrieve_raw_node` on `EMPTY_ROOT`). -/
def lookupRoot (root : Option PTrie) (key : List Nat) : Except String Lookup :=
  match root with
  | none => .ok { nodes := [], value := none }
  | some t => lookupPath t key

/-- `AccountingState` (`ext.rs:645-748`): created once per chunk application
(`chain/chain/src/runtime/mod.rs:340`) and shared by every receipt of the chunk; never rolled back
(a failed receipt's touches stay cached). -/
structure Acct where
  cache : List Bytes := []
  db : Nat := 0
  mem : Nat := 0
  deriving Repr, Inhabited

/-- `track_mem_lookup` / `track_disk_lookup`. -/
def Acct.touch (a : Acct) (h : Bytes) : Acct :=
  if a.cache.contains h then { a with mem := a.mem + 1 } else { a with db := a.db + 1, cache := h :: a.cache }

def Acct.touchAll (a : Acct) (hs : List Bytes) : Acct := hs.foldl Acct.touch a

/-- `commit_counts_since(snapshot)`: `trie_node_touched(Δdb)` then `cached_trie_node_access(Δmem)`
(`gas_counter.rs:399-406`). -/
def commit (gs : Gas) (start a : Acct) : Gas × Option String :=
  match payPer gs C.touchingTrieNode (a.db - start.db) with
  | (gs, some e) => (gs, some e)
  | (gs, none) => payPer gs C.readCachedTrieNode (a.mem - start.mem)

/-- The chunk's write overlay (`TrieUpdate::get_ref_from_updates`, `update.rs:118-145`): the latest
prospective-or-committed change of a trie key; `some none` = deleted earlier in the chunk. -/
abbrev Overlay := List (Bytes × Option Bytes)

def overlayGet (o : Overlay) (k : Bytes) : Option (Option Bytes) := (o.find? (·.1 == k)).map (·.2)

/-- Inputs of one storage operation: the full trie key (`TrieKey::ContractData`), the pre-state trie,
the chunk's overlay. -/
structure Env where
  root : Option PTrie
  overlay : Overlay

/-- Result: gas after the trie-side charges, the cache after, the old value length if present, or an
error (`GasExceeded`/`GasLimitExceeded` text from `payPer`, or a storage error). -/
structure Out where
  gs : Gas
  acct : Acct
  old : Option Nat
  err : Option String := none

/-- `storage_set` / `storage_remove` trie side (`ext.rs:147-182, 232-268`): `get_ref(MemOrTrie)` —
the overlay if it has the key (no touches), else every node of the path is tracked; if a value is
present, `{evicted|removed}_byte × len` is charged *before* the value hash is tracked (a failed
charge leaves the path touches in the cache, uncharged); then the deltas are committed. -/
def writeLike (byteCost : Cost) (e : Env) (key : Bytes) (gs : Gas) (a : Acct) : Out :=
  match overlayGet e.overlay key with
  | some old =>
    let n := old.map (·.length)
    match n with
    | some len => match payPer gs byteCost len with
      | (gs, some err) => { gs, acct := a, old := n, err := some err }
      | (gs, none) => { gs, acct := a, old := n }
    | none => { gs, acct := a, old := none }
  | none =>
    match lookupRoot e.root (nibbles key) with
    | .error err => { gs, acct := a, old := none, err := some err }
    | .ok l =>
      let a1 := a.touchAll l.nodes
      match l.value with
      | none =>
        let (gs, r) := commit gs a a1
        { gs, acct := a1, old := none, err := r }
      | some (len, vh) =>
        match payPer gs byteCost len with
        | (gs, some err) => { gs, acct := a1, old := some len, err := some err }
        | (gs, none) =>
          let a2 := a1.touch vh
          let (gs, r) := commit gs a a2
          { gs, acct := a2, old := some len, err := r }

def storageWrite := writeLike C.storageWriteEvictedByte
def storageRemove := writeLike C.storageRemoveRetValueByte

/-- `storage_get` (`ext.rs:189-230`) + `storage_read` (`logic.rs:4571-4605`): `MemOrFlatOrTrie`
tracks no node, so the committed deltas are 0 (both `pay_per` calls charge 0); the logic then
charges value bytes (and the large-read overhead for `len > 4000`), and dereferences the value
with a `FreeGasCounter`: the value hash enters the cache *uncharged* (only when every value charge
succeeded). The overlay serves a key written earlier in the chunk. -/
def storageRead (e : Env) (key : Bytes) (gs : Gas) (a : Acct) : Out :=
  let valueCharges (gs : Gas) (len : Nat) : Gas × Option String :=
    match payPer gs C.storageReadValueByte len with
    | (gs, some err) => (gs, some err)
    | (gs, none) =>
      if len > 4000 then
        match payBase gs C.storageLargeReadOverheadBase with
        | (gs, some err) => (gs, some err)
        | (gs, none) => payPer gs C.storageLargeReadOverheadByte len
      else (gs, none)
  match overlayGet e.overlay key with
  | some old =>
    match old with
    | none => { gs, acct := a, old := none }
    | some v => let (gs, r) := valueCharges gs v.length; { gs, acct := a, old := some v.length, err := r }
  | none =>
    match lookupRoot e.root (nibbles key) with
    | .error err => { gs, acct := a, old := none, err := some err }
    | .ok l =>
      let (gs, r) := commit gs a a
      match r, l.value with
      | some err, _ => { gs, acct := a, old := none, err := some err }
      | none, none => { gs, acct := a, old := none }
      | none, some (len, vh) =>
        match valueCharges gs len with
        | (gs, some err) => { gs, acct := a, old := some len, err := some err }
        | (gs, none) => { gs, acct := a.touch vh, old := some len }

/-- `storage_has_key` (`ext.rs:270-297`): `MemOrFlatOrTrie`, nothing tracked, nothing dereferenced. -/
def storageHasKey (e : Env) (key : Bytes) (gs : Gas) (a : Acct) : Out :=
  match overlayGet e.overlay key with
  | some old => { gs, acct := a, old := old.map (·.length) }
  | none =>
    match lookupRoot e.root (nibbles key) with
    | .error err => { gs, acct := a, old := none, err := some err }
    | .ok l => let (gs, r) := commit gs a a; { gs, acct := a, old := l.value.map (·.1), err := r }

/-- Gas of the tracked accesses: at PV86 both keys cost the same, so the cache is gas-irrelevant —
`(db + mem) × 2,280,000,000` (compute `× 4,000,000,000`). -/
theorem ttn_costs_equal : C.touchingTrieNode.gas = C.readCachedTrieNode.gas ∧
    C.touchingTrieNode.compute = C.readCachedTrieNode.compute := ⟨rfl, rfl⟩

end NearSpecV3.Wasm.TTN
