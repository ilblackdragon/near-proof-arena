import NearSpecV3.TrieBuild
import NearSpec.TrieUpsert

/-!
# D2 trie operations: full reveal, delete with squash, path-only refs, prefix iteration

spec/near-chunk-validation-d2.md §3. All operations act on `NearSpec.PTrie` (v1/v2's partial
trie; node hashing and `upsert` with its proofs are reused unchanged).

* **Full reveal** (`revealAll`): the recorded storage is a set of values keyed by their
  SHA-256 (`Trie::from_recorded_storage`, `core/store/src/trie/mod.rs:715-735`). Revealing
  every node reachable from the root that is present in the set, and every value present,
  yields a partial trie on which an operation succeeds iff every node/value nearcore touches
  is present: an unrevealed subtree (`PTrie.hash`) or value (`Slot.ref`) is exactly a
  missing recorded value (`MissingTrieValue`). Revealing more than D0/D1's per-key builder
  does not change any lookup (`NearSpec.PTrie.find_refinedBy`).
* `PTrie.del`: `generic_delete` + `squash_node` (`core/store/src/trie/ops/insert_delete.rs:262-438`,
  `ops/squash.rs:29-178`): descending reads every child entered; a branch left with one
  child and no value is merged with that child, **which must be revealed** (it is read).
* `PTrie.findRef`: `get_optimized_ref` / `contains_key` — the path only, not the value.
* `iterPrefix`: `TrieIteratorImpl::seek_prefix` + `next` (`ops/iter.rs:125-250, 337-372`):
  the path to the prefix, then every node and value of the prefix subtree.

`none` results mean "a node or value nearcore reads is missing".
-/

namespace NearSpecV3.D2

open NearSpec NearSpecV3

/-! ## Full reveal of the recorded storage -/

/-- Binary search tree of the recorded values keyed by their SHA-256 (byte-lexicographic),
built by insertion in witness order. Pure inductive data with structural recursion, so the
relation stays kernel-reducible (no `HashMap`: its hash function is `opaque`). -/
inductive HStore where
  | tip
  | node (k v : Bytes) (l r : HStore)

/-- Three-way byte-lexicographic comparison (`0` lt, `1` eq, `2` gt). -/
def cmpBytes : Bytes → Bytes → Nat
  | [], [] => 1
  | [], _ :: _ => 0
  | _ :: _, [] => 2
  | a :: as, b :: bs => if a.toNat < b.toNat then 0 else if b.toNat < a.toNat then 2 else cmpBytes as bs

def HStore.insert : HStore → Bytes → Bytes → HStore
  | .tip, k, v => .node k v .tip .tip
  | .node k' v' l r, k, v =>
    match cmpBytes k k' with
    | 0 => .node k' v' (l.insert k v) r
    | 2 => .node k' v' l (r.insert k v)
    | _ => .node k' v l r

def HStore.get? : HStore → Bytes → Option Bytes
  | .tip, _ => none
  | .node k' v' l r, k =>
    match cmpBytes k k' with
    | 0 => l.get? k
    | 2 => r.get? k
    | _ => some v'

def mkHStore (values : List Bytes) : HStore :=
  values.foldl (fun m v => m.insert (sha256 v) v) .tip

def hGet (s : HStore) (h : Bytes) : Option Bytes := s.get? h

def hSlot (s : HStore) (len : Nat) (vh : Bytes) : Slot :=
  match hGet s vh with
  | some v => if v.length == len then .val v else .ref len vh
  | none => .ref len vh

def revealKids (f : Bytes → PTrie) : List (Option Bytes) → Kids
  | [] => .nil
  | none :: more => .none (revealKids f more)
  | some ch :: more => .some (f ch) (revealKids f more)

/-- Reveal every node and value of the store reachable from `h` (depth ≤ `fuel`). The node
decoding is `TrieBuild.buildFor`'s (`RawTrieNodeWithSize`, `raw_node.rs:10-92`); a node whose
bytes do not decode canonically stays unrevealed. -/
def revealAll (s : HStore) : Nat → Bytes → PTrie
  | 0, h => .hash h
  | fuel + 1, h =>
    match hGet s h with
    | none => .hash h
    | some node =>
      if node.length < 9 then .hash h else
      let mem := leNat (node.drop (node.length - 8))
      let body := node.take (node.length - 8)
      match body with
      | 0 :: rest =>
        let klen := leNat (rest.take 4)
        match hpDecode ((rest.drop 4).take klen) with
        | some (k, true) =>
          let r2 := rest.drop (4 + klen)
          if r2.length != 36 then .hash h else
          .leaf k (hSlot s (leNat (r2.take 4)) (r2.drop 4)) mem
        | _ => .hash h
      | 3 :: rest =>
        let klen := leNat (rest.take 4)
        match hpDecode ((rest.drop 4).take klen) with
        | some (k, false) =>
          let child := rest.drop (4 + klen)
          if child.length != 32 then .hash h else
          .ext k (revealAll s fuel child) mem
        | _ => .hash h
      | 1 :: rest =>
        let bm := leNat (rest.take 2)
        let hs := kidHashes 16 bm (rest.drop 2)
        if rest.length != 2 + 32 * (hs.filter Option.isSome).length then .hash h else
        .branch none (revealKids (revealAll s fuel) hs) mem
      | 2 :: rest =>
        if rest.length < 36 then .hash h else
        let v := hSlot s (leNat (rest.take 4)) ((rest.drop 4).take 32)
        let rest := rest.drop 36
        let bm := leNat (rest.take 2)
        let hs := kidHashes 16 bm (rest.drop 2)
        if rest.length != 2 + 32 * (hs.filter Option.isSome).length then .hash h else
        .branch (some v) (revealKids (revealAll s fuel) hs) mem
      | _ => .hash h

/-- Keys are ≤ 1 + 64 + 1 + 2048 bytes (contract data, `max_length_storage_key = 2048`,
`53.yaml:13`) = 4228 nibbles; each revealed node consumes ≥ 1 nibble except extensions,
which alternate with branches. -/
def revealFuel : Nat := 10000

def revealTrie (values : List Bytes) (root : Bytes) : PTrie :=
  revealAll (mkHStore values) revealFuel root

/-- `Trie::EMPTY_ROOT`. -/
def emptyRoot : Bytes := zeros 32

def rootHash : Option PTrie → Bytes
  | none => emptyRoot
  | some t => t.hashOf

end NearSpecV3.D2

namespace NearSpec

open NearSpecV3.D2

/-! ## Kids helpers -/

def Kids.at : Kids → Nat → Option PTrie
  | .nil, _ => Option.none
  | .none _, 0 => Option.none
  | .some c _, 0 => Option.some c
  | .none r, i + 1 => Kids.at r i
  | .some _ r, i + 1 => Kids.at r i

def Kids.put : Kids → Nat → Option PTrie → Kids
  | .nil, _, _ => .nil
  | .none r, 0, c => match c with | Option.some c => .some c r | Option.none => .none r
  | .some _ r, 0, c => match c with | Option.some c => .some c r | Option.none => .none r
  | .none r, i + 1, c => .none (Kids.put r i c)
  | .some x r, i + 1, c => .some x (Kids.put r i c)

/-- The children present, with their indices, in index order. -/
def Kids.present : Kids → Nat → List (Nat × PTrie)
  | .nil, _ => []
  | .none r, i => Kids.present r (i + 1)
  | .some c r, i => (i, c) :: Kids.present r (i + 1)

/-! ## Delete (`generic_delete` + `squash_node`) -/

/-- `extend_child(ext, child)` (`squash.rs:113-178`) for a *revealed* child; `none` result =
`Empty`. -/
def extendChild (k : List Nat) : PTrie → Option (Option PTrie)
  | .hash _ => none
  | .leaf k2 s _ => some (some (.leaf (k ++ k2) s (leafMem (k ++ k2) s.len)))
  | .branch v cs m => some (some (.ext k (.branch v cs m) (extOwnMem k + m)))
  | .ext k2 c m => some (some (.ext (k ++ k2) c (extOwnMem (k ++ k2) + (m - extOwnMem k2))))

/-- `squash_node` of a branch (`squash.rs:45-98`): 0 children ⇒ `Empty` or a leaf with empty
key; one child and no value ⇒ `extend_child([idx], child)` (reads the child); else unchanged.
Outer `none` = the remaining child is not revealed (`MissingTrieValue`). -/
def squashBranch (v : Option Slot) (cs : Kids) (m : Nat) : Option (Option PTrie) :=
  match Kids.present cs 0, v with
  | [], none => some none
  | [], some s => some (some (.leaf [] s (leafMem [] s.len)))
  | [(i, c)], none => extendChild [i] c
  | _, _ => some (some (.branch v cs m))

mutual
/-- Delete `key` (nibble path). `none` ⇔ a node on the visited path (or a node read by
squashing) is unrevealed. `some (deleted, t')` with `t' = none` for the empty node. -/
def PTrie.del : PTrie → List Nat → Option (Bool × Option PTrie)
  | .hash _, _ => none
  | .leaf k s m, key => if k = key then some (true, none) else some (false, some (.leaf k s m))
  | .ext k c m, key =>
    if isPrefix k key then
      match c.mem?, c.del (key.drop k.length) with
      | some _, some (true, c') =>
        match c' with
        | none => some (true, none)
        | some c' => (extendChild k c').map fun r => (true, r)
      | some _, some (false, _) => some (false, some (.ext k c m))
      | _, _ => none
    else some (false, some (.ext k c m))
  | .branch v cs m, [] =>
    match v with
    | none => some (false, some (.branch v cs m))
    | some s => (squashBranch none cs (m - valueMem s.len)).map fun r => (true, r)
  | .branch v cs m, n :: rest =>
    match Kids.delAt cs n rest with
    | none => none
    | some none => some (false, some (.branch v cs m))
    | some (some (cs', old, new)) => (squashBranch v cs' (m - old + new)).map fun r => (true, r)
/-- Delete in child slot `n`: `some none` = no deletion (absent child or key not found),
`some (some (kids', old mem, new mem))` = deleted. -/
def Kids.delAt : Kids → Nat → List Nat → Option (Option (Kids × Nat × Nat))
  | .nil, _, _ => some none
  | .none _, 0, _ => some none
  | .some c r, 0, key =>
    match c.mem?, c.del key with
    | some cm, some (true, c') =>
      some (some ((match c' with | some c' => .some c' r | none => .none r), cm,
                  (match c' with | some c' => c'.memD | none => 0)))
    | some _, some (false, _) => some none
    | _, _ => none
  | .none r, i + 1, key => (Kids.delAt r i key).map fun o => o.map fun (k, a, b) => (.none k, a, b)
  | .some c r, i + 1, key => (Kids.delAt r i key).map fun o => o.map fun (k, a, b) => (.some c k, a, b)
end

/-! ## Path-only lookup (`get_optimized_ref`) -/

mutual
/-- `some (some slot)` present (value possibly unrevealed), `some none` absent, `none`
undetermined (a node on the path is unrevealed). -/
def PTrie.findRef : PTrie → List Nat → Option (Option Slot)
  | .hash _, _ => none
  | .leaf k v _, key => if k = key then some (some v) else some none
  | .ext k c _, key => if isPrefix k key then c.findRef (key.drop k.length) else some none
  | .branch v _ _, [] => some v
  | .branch _ cs _, n :: rest => Kids.findRef cs n rest
def Kids.findRef : Kids → Nat → List Nat → Option (Option Slot)
  | .nil, _, _ => some none
  | .none _, 0, _ => some none
  | .some c _, 0, key => c.findRef key
  | .none r, i + 1, key => Kids.findRef r i key
  | .some _ r, i + 1, key => Kids.findRef r i key
end

/-! ## Prefix iteration -/

mutual
/-- All keys of a subtree (prefix `acc`), reading every node and value. -/
def PTrie.allKeys : PTrie → List Nat → Option (List (List Nat))
  | .hash _, _ => none
  | .leaf k v _, acc => match v with
    | .val _ => some [acc ++ k]
    | .ref _ _ => none
  | .ext k c _, acc => c.allKeys (acc ++ k)
  | .branch v cs _, acc => do
    let here ← match v with
      | none => some []
      | some (.val _) => some [acc]
      | some (.ref _ _) => none
    let kids ← Kids.allKeys cs 0 acc
    pure (here ++ kids)
def Kids.allKeys : Kids → Nat → List Nat → Option (List (List Nat))
  | .nil, _, _ => some []
  | .none r, i, acc => Kids.allKeys r (i + 1) acc
  | .some c r, i, acc => do
    let a ← c.allKeys (acc ++ [i])
    let b ← Kids.allKeys r (i + 1) acc
    pure (a ++ b)
end

mutual
/-- Keys with nibble prefix `pre` in the trie, as `seek_prefix` + iteration read them
(`ops/iter.rs:160-232`): along the prefix path; a leaf / extension whose key extends the
remaining prefix, or the node reached when the prefix is exhausted, is iterated entirely;
a diverging leaf / extension or a missing branch child ends the iteration. -/
def PTrie.prefixKeys : PTrie → List Nat → List Nat → Option (List (List Nat))
  | .hash _, _, _ => none
  | .leaf k v m, pre, acc =>
    if isPrefix pre k then (PTrie.leaf k v m).allKeys acc else some []
  | .ext k c m, pre, acc =>
    if isPrefix k pre then c.prefixKeys (pre.drop k.length) (acc ++ k)
    else if isPrefix pre k then (PTrie.ext k c m).allKeys acc
    else some []
  | .branch v cs m, [], acc => (PTrie.branch v cs m).allKeys acc
  | .branch _ cs _, n :: rest, acc => Kids.prefixKeys cs n rest (acc ++ [n])
def Kids.prefixKeys : Kids → Nat → List Nat → List Nat → Option (List (List Nat))
  | .nil, _, _, _ => some []
  | .none _, 0, _, _ => some []
  | .some c _, 0, rest, acc => c.prefixKeys rest acc
  | .none r, i + 1, rest, acc => Kids.prefixKeys r i rest acc
  | .some _ r, i + 1, rest, acc => Kids.prefixKeys r i rest acc
end


end NearSpec
