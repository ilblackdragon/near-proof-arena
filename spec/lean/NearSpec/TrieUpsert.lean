import NearSpec.Trie

/-!
# Partial-trie lookup with proven absence, and upsert with structural changes

Used by `near/pv86/receipt-transfer-batch/v1` (`NearSpec.TransferV2`), which must
write `TrieKey::BandwidthSchedulerState` (key `0x0f`). That write can

* **insert** a key (the state is absent before the first chunk that runs the
  scheduler, and in synthetic states), which changes the trie *shape*: a leaf or
  an extension is split, a branch gains a child or a value; and
* **change a value's length** (the previous scheduler state can hold any number
  of link allowances; the new one holds exactly one), which changes the stored
  `memory_usage` of every node on the path.

v1's `PTrie.set` (in-place replacement, shape and `memory_usage` kept) cannot
express either, so this module adds `PTrie.upsert`. `NearSpec.Trie` (trusted by
the v1 challenge) is not modified.

Source (nearcore 2.13.4):
* `core/store/src/trie/ops/insert_delete.rs` (`GenericTrieUpdateInsertDelete::insert`)
  — leaf split, extension split, new branch child / branch value;
* `core/store/src/trie/ops/interface.rs:78-105` — per-node `memory_usage`:
  leaf `50 + 2·|hp(key)| + (|value| + 50)`, extension `50 + 2·|hp(key)| + child`,
  branch `50 + [|value| + 50] + Σ children` (`TRIE_COSTS = {node_cost 50,
  byte_of_key 2, byte_of_value 1}`, `trie/mod.rs:158`);
* the resulting trie is the canonical compressed Patricia trie of the new key set
  (a function of the key→value map: `update.rs:242-262` feeds only final values).

`memory_usage` of an unrevealed (`.hash`) child is never needed: an extension
split recovers its child's usage from the extension's own stored usage
(`mem − (50 + 2·|hp|)`), and every other case either recurses into a revealed
child (using the child's stored usage) or builds fresh leaves.

Proved in `NearSpec.TrieUpsertProofs` (no `sorry`; axioms ⊆ {propext,
Classical.choice, Quot.sound}), for well-formed tries and nibble keys `< 16`:
* `PTrie.find_upsert_self` — after `upsert t k v = some t'`, `t'.find k = some (some v)`;
* `PTrie.find_upsert_other` — for every other key `k' ≠ k`, `t'.find k' = t.find k'`
  (presence with value, proven absence and "unknown" are all preserved);
* `PTrie.hashOf_refinedBy`, `PTrie.find_refinedBy`, `PTrie.upsert_refinedBy`,
  `PTrie.upsert_hashOf_congr` — the result does not depend on how much of the
  trie is revealed: on a partial trie that refines (is a hash-pruning of) a more
  revealed trie — e.g. the full pre-state trie — `find`, the pre-root and the
  post-root all agree with the computation on the more revealed trie.
Not proved (argued + differentially tested, see `spec/near-transfer-receipt-v2.md` §4):
that on the full canonical trie `upsert` yields exactly nearcore's canonical
trie (shape and `memory_usage`) of the updated key→value map.
-/

namespace NearSpec

def Slot.len : Slot → Nat
  | .val v => v.length
  | .ref len _ => len

/-- `memory_usage` stored in a revealed node. -/
def PTrie.mem? : PTrie → Option Nat
  | .hash _ => none
  | .leaf _ _ m => some m
  | .ext _ _ m => some m
  | .branch _ _ m => some m

def PTrie.memD (t : PTrie) : Nat := t.mem?.getD 0

/-- Leaf `memory_usage`: `node_cost + byte_of_key·|hp(key, leaf)| + (|value|·byte_of_value + node_cost)`. -/
def leafMem (k : List Nat) (vlen : Nat) : Nat := 50 + 2 * (hexPrefix k true).length + (vlen + 50)
/-- Extension `memory_usage` without its child: `node_cost + byte_of_key·|hp(key, ext)|`. -/
def extOwnMem (k : List Nat) : Nat := 50 + 2 * (hexPrefix k false).length
/-- Contribution of a branch value: `|value| + node_cost`. -/
def valueMem (vlen : Nat) : Nat := vlen + 50

/-- Longest common prefix of two nibble paths. -/
def commonPrefix : List Nat → List Nat → List Nat
  | a :: as, b :: bs => if a = b then a :: commonPrefix as bs else []
  | _, _ => []

/-- `n` child slots starting at index `i`; slot `j` holds `f j`. -/
def kidsFrom : Nat → Nat → (Nat → Option PTrie) → Kids
  | 0, _, _ => .nil
  | n + 1, i, f =>
    match f i with
    | some c => .some c (kidsFrom n (i + 1) f)
    | none => .none (kidsFrom n (i + 1) f)

/-- 16 slots with one child at `x`. -/
def kids1 (x : Nat) (c : PTrie) : Kids :=
  kidsFrom 16 0 fun i => if i = x then some c else none

/-- 16 slots with children at `x` and `y` (`x ≠ y`). -/
def kids2 (x : Nat) (c : PTrie) (y : Nat) (d : PTrie) : Kids :=
  kidsFrom 16 0 fun i => if i = x then some c else if i = y then some d else none

def newLeaf (k : List Nat) (v : Bytes) : PTrie := .leaf k (.val v) (leafMem k v.length)

/-- Prefix `b` with an extension over `p` (none if `p = []`). -/
def wrapExt (p : List Nat) (b : PTrie) : PTrie :=
  match p with
  | [] => b
  | _ :: _ => .ext p b (extOwnMem p + b.memD)

/-- Insert `key ↦ v` next to an existing leaf `k ↦ s` (`k ≠ key`): a branch at the
first differing nibble (holding a value if one key ends there), under an
extension over the common prefix. -/
def splitLeaf (k : List Nat) (s : Slot) (key : List Nat) (v : Bytes) : PTrie :=
  let p := commonPrefix k key
  match k.drop p.length, key.drop p.length with
  | [], y :: ys =>
    wrapExt p (.branch (some s) (kids1 y (newLeaf ys v)) (50 + valueMem s.len + leafMem ys v.length))
  | x :: xs, [] =>
    wrapExt p (.branch (some (.val v)) (kids1 x (.leaf xs s (leafMem xs s.len)))
      (50 + valueMem v.length + leafMem xs s.len))
  | x :: xs, y :: ys =>
    wrapExt p (.branch none (kids2 x (.leaf xs s (leafMem xs s.len)) y (newLeaf ys v))
      (50 + leafMem xs s.len + leafMem ys v.length))
  | [], [] => newLeaf key v

/-- Insert `key ↦ v` where the extension `k` (child `c`, usage `m`) is not a
prefix of `key`. The child's usage is `m − extOwnMem k`. -/
def splitExt (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) : PTrie :=
  let p := commonPrefix k key
  let cm := m - extOwnMem k
  match k.drop p.length with
  | [] => .ext k c m   -- unreachable: `k` would be a prefix of `key`
  | x :: xs =>
    let sub : PTrie := match xs with
      | [] => c
      | _ :: _ => .ext xs c (extOwnMem xs + cm)
    let subMem := match xs with
      | [] => cm
      | _ :: _ => extOwnMem xs + cm
    match key.drop p.length with
    | [] => wrapExt p (.branch (some (.val v)) (kids1 x sub) (50 + valueMem v.length + subMem))
    | y :: ys => wrapExt p (.branch none (kids2 x sub y (newLeaf ys v)) (50 + subMem + leafMem ys v.length))

mutual
/-- Insert or overwrite `key ↦ v` (nibble path) in a partial trie, keeping the
trie canonical and every `memory_usage` exact. `none` iff the path to `key`
runs into an unrevealed subtree (the witness is insufficient). -/
def PTrie.upsert : PTrie → List Nat → Bytes → Option PTrie
  | .hash _, _, _ => none
  | .leaf k s _, key, v => if k = key then some (newLeaf k v) else some (splitLeaf k s key v)
  | .ext k c m, key, v =>
    if isPrefix k key then
      match c.mem?, c.upsert (key.drop k.length) v with
      | some cm, some c' => some (.ext k c' (m + c'.memD - cm))
      | _, _ => none
    else some (splitExt k c m key v)
  | .branch bv cs m, [], v =>
    some (.branch (some (.val v)) cs
      (m + valueMem v.length - (match bv with | some s => valueMem s.len | none => 0)))
  | .branch bv cs m, n :: rest, v =>
    (Kids.upsert cs n rest v).map fun r => .branch bv r.1 (m + r.2.2 - r.2.1)
/-- Upsert into child slot `n`; returns the new slots and (old, new) usage of that child. -/
def Kids.upsert : Kids → Nat → List Nat → Bytes → Option (Kids × Nat × Nat)
  | .nil, _, _, _ => none
  | .none r, 0, key, v => some (.some (newLeaf key v) r, 0, leafMem key v.length)
  | .some c r, 0, key, v =>
    match c.mem?, c.upsert key v with
    | some cm, some c' => some (.some c' r, cm, c'.memD)
    | _, _ => none
  | .none r, i + 1, key, v => (Kids.upsert r i key v).map fun x => (.none x.1, x.2)
  | .some c r, i + 1, key, v => (Kids.upsert r i key v).map fun x => (.some c x.1, x.2)
end

mutual
/-- Lookup with proven absence: `some (some v)` — present with revealed value;
`some none` — proven absent (the path leaves the trie at a revealed node);
`none` — undetermined (the path enters an unrevealed subtree or value). -/
def PTrie.find : PTrie → List Nat → Option (Option Bytes)
  | .hash _, _ => none
  | .leaf k v _, key => if k = key then v.get.map some else some none
  | .ext k c _, key => if isPrefix k key then c.find (key.drop k.length) else some none
  | .branch v _ _, [] =>
    match v with
    | none => some none
    | some s => s.get.map some
  | .branch _ cs _, n :: rest => Kids.find cs n rest
def Kids.find : Kids → Nat → List Nat → Option (Option Bytes)
  | .nil, _, _ => some none
  | .none _, 0, _ => some none
  | .some c _, 0, key => c.find key
  | .none r, i + 1, key => Kids.find r i key
  | .some _ r, i + 1, key => Kids.find r i key
end

end NearSpec
