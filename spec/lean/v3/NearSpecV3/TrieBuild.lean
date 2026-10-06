import ArenaCore.SHA256Fast
import NearSpec.TrieUpsert

/-!
# Partial tries from recorded storage (`PartialState::TrieValues`)

nearcore's validator wraps `base_state` in `Trie::from_recorded_storage(storage,
root)` (`chain/chain/src/runtime/mod.rs:1201-1258`): every node or value is looked
up **by its SHA-256 hash** in the recorded set; a missing one is a
`MissingTrieValue` storage error, which fails validation
(`chunk_validation.rs`, mutation `w.base_state.drop_node`).

`buildFor store root keys` reveals exactly the nodes on the nibble paths of
`keys` that are present in `store` (and the values at those keys), and leaves
every other subtree as `PTrie.hash`. `NearSpec.PTrie.find` then answers
*present* / *proven absent* / *undetermined*; the relation rejects on
*undetermined*, which is exactly nearcore's `MissingTrieValue` for the keys
the D0 semantics reads. The node decoding mirrors `RawTrieNodeWithSize`
(`core/store/src/trie/raw_node.rs:10-92`); a revealed node whose bytes do not
decode to a canonical node is left unrevealed, so its subtree is undetermined.
Soundness never depends on this builder: the relation re-hashes the built trie
(`PTrie.hashOf = root`) and `PTrie.wf` makes node serialization injective.

**Fuel.** `fuel` bounds the recursion depth (one level per revealed node);
`trieFuel = 400` exceeds any path (keys are ≤ 66 bytes = 132 nibbles in D0, and
a path alternates at most one extension per branch).
-/

namespace NearSpecV3

open NearSpec

abbrev Store := List (Bytes × Bytes)

def mkStore (values : List Bytes) : Store := values.map fun v => (sha256 v, v)

def storeGet (s : Store) (h : Bytes) : Option Bytes :=
  match s.find? (fun p => p.1 == h) with
  | some p => some p.2
  | none => none

def hpDecode : Bytes → Option (List Nat × Bool)
  | [] => none
  | f :: rest =>
    let hi := f.toNat / 16
    let odd := hi % 2 == 1
    let leaf := hi / 2 % 2 == 1
    if hi > 3 then none
    else if !odd && f.toNat % 16 != 0 then none
    else some ((if odd then [f.toNat % 16] else []) ++ nibbles rest, leaf)

def kidHashes : Nat → Nat → Bytes → List (Option Bytes)
  | 0, _, _ => []
  | k + 1, bm, bs =>
    if bm % 2 == 1 then some (bs.take 32) :: kidHashes k (bm / 2) (bs.drop 32)
    else none :: kidHashes k (bm / 2) bs

def trieFuel : Nat := 400

/-- Value slot: reveal the value if it is wanted and present with the right length. -/
def mkSlot (s : Store) (len : Nat) (vh : Bytes) (want : Bool) : Slot :=
  match (if want then storeGet s vh else none) with
  | some v => if v.length == len then .val v else .ref len vh
  | none => .ref len vh

def buildKidsWith (f : Bytes → List (List Nat) → PTrie) : Nat → List (Option Bytes) → List (List Nat) → Kids
  | _, [], _ => .nil
  | i, none :: more, keys => .none (buildKidsWith f (i + 1) more keys)
  | i, some ch :: more, keys =>
    let ks := (keys.filter (fun k => k.head? == some i)).map (·.drop 1)
    .some (f ch ks) (buildKidsWith f (i + 1) more keys)

def branchWith (f : Bytes → List (List Nat) → PTrie) (h : Bytes) (v : Option Slot) (rest : Bytes)
    (keys : List (List Nat)) (mem : Nat) : PTrie :=
  let bm := leNat (rest.take 2)
  let hs := kidHashes 16 bm (rest.drop 2)
  let nkids := (hs.filter Option.isSome).length
  if rest.length != 2 + 32 * nkids then .hash h else
  .branch v (buildKidsWith f 0 hs keys) mem

def buildFor (s : Store) : Nat → Bytes → List (List Nat) → PTrie
  | 0, h, _ => .hash h
  | fuel + 1, h, keys =>
    if keys.isEmpty then .hash h else
    match storeGet s h with
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
          .leaf k (mkSlot s (leNat (r2.take 4)) (r2.drop 4) (keys.any (· == k))) mem
        | _ => .hash h
      | 3 :: rest =>
        let klen := leNat (rest.take 4)
        match hpDecode ((rest.drop 4).take klen) with
        | some (k, false) =>
          let child := rest.drop (4 + klen)
          if child.length != 32 then .hash h else
          let keys' := (keys.filter (isPrefix k)).map (·.drop k.length)
          .ext k (buildFor s fuel child keys') mem
        | _ => .hash h
      | 1 :: rest => branchWith (buildFor s fuel) h none rest keys mem
      | 2 :: rest =>
        if rest.length < 36 then .hash h else
        branchWith (buildFor s fuel) h (some (mkSlot s (leNat (rest.take 4)) ((rest.drop 4).take 32)
          (keys.any (· == [])))) (rest.drop 36) keys mem
      | _ => .hash h

/-- Partial pre-state trie revealing the paths of `keys` (nibble paths). -/
def partialTrie (values : List Bytes) (root : Bytes) (keys : List (List Nat)) : PTrie :=
  buildFor (mkStore values) trieFuel root keys

end NearSpecV3
