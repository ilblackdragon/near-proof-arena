import NearSpecV3.ChunkValidationD2

/-!
# Witness normal form: definitions (executable; part of the verifier model)

Every degree of freedom nearcore's lenient witness decoding leaves, beyond the three
validator-ignored fields (`CanonDefs`):

* `source_receipt_proofs` is a `HashMap` decoded without strict order: entries in any
  order, a duplicate key keeps the last value. Normal form: one entry per key (the last
  one), keys in increasing byte order (`normEntriesD2`).
* `PartialState::TrieValues` (every transition's `base_state`) is a `Vec` used as a
  hash-indexed store (`NearSpecV3.D2.mkHStore`: last value wins per hash): any order,
  duplicates and values the validator never reads are accepted. In D2 the relation reveals
  the **whole** recorded trie reachable from the root (`NearSpecV3.D2.revealAll`). Normal
  form: exactly the values `revealAll` looks up (`qAll` mirrors it and records every hash
  it passes to `hGet`), as the store answers them, without duplicates, in increasing byte
  order (`normValsH`).

Definitions only; the judge compiles this module.
-/

namespace ReexecV3D3

open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## Byte order and insertion sort -/

/-- Lexicographic `≤` on byte strings (a proper prefix is smaller). -/
def bytesLe : Bytes → Bytes → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a.toNat < b.toNat then true else if a = b then bytesLe as bs else false

def insertBy {α : Type} (le : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if le x y then x :: y :: ys else y :: insertBy le x ys

def isort {α : Type} (le : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => insertBy le x (isort le xs)

/-- Remove duplicates, keeping the last occurrence. -/
def dedupLastBy {α : Type} (k : α → Bytes) : List α → List α
  | [] => []
  | e :: es => if es.any (fun x => k x == k e) then dedupLastBy k es else e :: dedupLastBy k es

/-! ## Receipt-proof entries -/

def normEntriesD2 (es : List EntryD2) : List EntryD2 :=
  isort (fun a b => bytesLe a.key b.key) (dedupLastBy (·.key) es)

/-! ## Trie values: the read set of `revealAll` -/

/-- Hashes looked up by `revealKids (revealAll s fuel)`. -/
def qKidsAll (f : Bytes → List Bytes) : List (Option Bytes) → List Bytes
  | [] => []
  | none :: more => qKidsAll f more
  | some ch :: more => f ch ++ qKidsAll f more

/-- Every hash `revealAll s fuel h` passes to `hGet` (node and value lookups). -/
def qAll (s : HStore) : Nat → Bytes → List Bytes
  | 0, _ => []
  | fuel + 1, h =>
    h :: match hGet s h with
    | none => []
    | some node =>
      if node.length < 9 then [] else
      let body := node.take (node.length - 8)
      match body with
      | 0 :: rest =>
        let klen := leNat (rest.take 4)
        match hpDecode ((rest.drop 4).take klen) with
        | some (_, true) =>
          let r2 := rest.drop (4 + klen)
          if r2.length != 36 then [] else [r2.drop 4]
        | _ => []
      | 3 :: rest =>
        let klen := leNat (rest.take 4)
        match hpDecode ((rest.drop 4).take klen) with
        | some (_, false) =>
          let child := rest.drop (4 + klen)
          if child.length != 32 then [] else qAll s fuel child
        | _ => []
      | 1 :: rest =>
        let bm := leNat (rest.take 2)
        let hs := kidHashes 16 bm (rest.drop 2)
        if rest.length != 2 + 32 * (hs.filter Option.isSome).length then [] else
        qKidsAll (qAll s fuel) hs
      | 2 :: rest =>
        if rest.length < 36 then [] else
        let vh := (rest.drop 4).take 32
        let rest := rest.drop 36
        let bm := leNat (rest.take 2)
        let hs := kidHashes 16 bm (rest.drop 2)
        if rest.length != 2 + 32 * (hs.filter Option.isSome).length then [] else
        vh :: qKidsAll (qAll s fuel) hs
      | _ => []

/-- The values the store answers for the looked-up hashes, without duplicates, in byte order. -/
def normValsH (values : List Bytes) (q : List Bytes) : List Bytes :=
  isort bytesLe (dedupLastBy id (q.filterMap (hGet (mkHStore values))))

end ReexecV3D3
