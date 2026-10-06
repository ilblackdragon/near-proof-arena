import NearSpecV3.WitnessV3
import NearSpecV3.TrieBuild

/-!
# Witness normal form: definitions (executable; part of the verifier model)

Every degree of freedom nearcore's lenient witness decoding leaves, beyond the three
validator-ignored fields of `CanonDefs`:

* `source_receipt_proofs` is a `HashMap` decoded without strict order: entries in any
  order, a duplicate key keeps the last value. Normal form: one entry per key (the last
  one), keys in increasing byte order (`normEntries`).
* `PartialState::TrieValues` (every transition's `base_state`) is a `Vec` used as a
  hash-indexed store: any order, duplicates and values the validator never reads are
  accepted. Normal form: exactly the values the relation looks up while building its
  partial tries (`qFor` mirrors `NearSpecV3.buildFor` and records every hash it looks
  up), without duplicates, in increasing byte order (`normVals`).

Definitions only; the judge compiles this module.
-/

namespace ReexecV3D0

open NearSpec NearSpecV3

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

def normEntries (es : List ProofEntry) : List ProofEntry :=
  isort (fun a b => bytesLe a.key b.key) (dedupLastBy (·.key) es)

/-! ## Trie values: the read set of `buildFor` -/

/-- Hashes looked up by `buildKidsWith (buildFor s fuel)`. -/
def qKids (f : Bytes → List (List Nat) → List Bytes) : Nat → List (Option Bytes) → List (List Nat) → List Bytes
  | _, [], _ => []
  | i, none :: more, keys => qKids f (i + 1) more keys
  | i, some ch :: more, keys =>
    let ks := (keys.filter (fun k => k.head? == some i)).map (·.drop 1)
    f ch ks ++ qKids f (i + 1) more keys

def qBranch (f : Bytes → List (List Nat) → List Bytes) (rest : Bytes) (keys : List (List Nat)) :
    List Bytes :=
  let bm := leNat (rest.take 2)
  let hs := kidHashes 16 bm (rest.drop 2)
  let nkids := (hs.filter Option.isSome).length
  if rest.length != 2 + 32 * nkids then [] else qKids f 0 hs keys

/-- Every hash `buildFor s fuel h keys` passes to `storeGet` (node and value lookups). -/
def qFor (s : Store) : Nat → Bytes → List (List Nat) → List Bytes
  | 0, _, _ => []
  | fuel + 1, h, keys =>
    if keys.isEmpty then [] else
    h :: match storeGet s h with
    | none => []
    | some node =>
      if node.length < 9 then [] else
      let body := node.take (node.length - 8)
      match body with
      | 0 :: rest =>
        let klen := leNat (rest.take 4)
        match hpDecode ((rest.drop 4).take klen) with
        | some (k, true) =>
          let r2 := rest.drop (4 + klen)
          if r2.length != 36 then [] else
          if keys.any (· == k) then [r2.drop 4] else []
        | _ => []
      | 3 :: rest =>
        let klen := leNat (rest.take 4)
        match hpDecode ((rest.drop 4).take klen) with
        | some (k, false) =>
          let child := rest.drop (4 + klen)
          if child.length != 32 then [] else
          qFor s fuel child ((keys.filter (isPrefix k)).map (·.drop k.length))
        | _ => []
      | 1 :: rest => qBranch (qFor s fuel) rest keys
      | 2 :: rest =>
        if rest.length < 36 then [] else
        (if keys.any (· == []) then [(rest.drop 4).take 32] else []) ++
          qBranch (qFor s fuel) (rest.drop 36) keys
      | _ => []

/-- The values found for the looked-up hashes, without duplicates, in byte order. -/
def normVals (values : List Bytes) (q : List Bytes) : List Bytes :=
  isort bytesLe (dedupLastBy id (q.filterMap (storeGet (mkStore values))))

end ReexecV3D0
