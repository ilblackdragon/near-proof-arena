import Std.Data.HashMap
import NearSpecV3.Wasm.Crypto

/-!
# Chunk-scoped trie state for the trie-backed `External` (data part)

The pre-state of a chunk as nearcore's stateless validator sees it: the recorded storage
(`PartialState::TrieValues`, every node and value keyed by its SHA-256) and `prev_state_root`;
the chunk's write overlay; the chunk-scoped trie-node accounting cache. The charging rules are in
`TrieAccounting.lean`; this module has no gas (so `Machine.St` can hold it).

`lookupPath` is `Trie::lookup_from_state_column` (`core/store/src/trie/mod.rs:1270-1330`) over the
recorded storage: every node retrieved is listed (root first; the last one also when the key is
absent); a node missing from the recorded storage is `MissingTrieValue`; node decoding is
`RawTrieNodeWithSize` (`raw_node.rs:10-92`).
-/

namespace NearSpecV3.Wasm.TTN

abbrev Store := Std.HashMap ByteArray ByteArray

def mkStore (values : List ByteArray) : Store :=
  values.foldl (fun m v => m.insert (Crypto.sha256 v) v) {}

def leN (d : ByteArray) (off n : Nat) : Nat :=
  (List.range n).foldr (fun i acc => (d.get! (off + i)).toNat + 256 * acc) 0

def nibblesOf (d : ByteArray) : List Nat :=
  d.toList.flatMap fun b => [b.toNat / 16, b.toNat % 16]

/-- `NibbleSlice::from_encoded`: (nibbles, is_leaf); `none` = not a canonical encoding. -/
def hpDecode (d : ByteArray) : Option (List Nat × Bool) :=
  match d.toList with
  | [] => none
  | f :: rest =>
    let hi := f.toNat / 16
    if hi > 3 then none
    else if hi % 2 == 0 && f.toNat % 16 != 0 then none
    else some ((if hi % 2 == 1 then [f.toNat % 16] else []) ++ (ByteArray.mk rest.toArray |> nibblesOf),
               hi / 2 % 2 == 1)

inductive Node where
  | leaf (key : List Nat) (vlen : Nat) (vh : ByteArray)
  | ext (key : List Nat) (child : ByteArray)
  | branch (value : Option (Nat × ByteArray)) (kids : Array (Option ByteArray))

/-- `RawTrieNodeWithSize` decoding (borsh): tag, body, then `memory_usage: u64`. -/
def decodeNode (n : ByteArray) : Option Node := do
  if n.size < 9 then none
  let body := n.extract 0 (n.size - 8)
  let tag := body.get! 0
  let kids (off : Nat) : Option (Array (Option ByteArray)) := do
    if body.size < off + 2 then none
    let bm := leN body off 2
    let mut out := #[]
    let mut p := off + 2
    for i in [0:16] do
      if bm / 2 ^ i % 2 == 1 then
        out := out.push (some (body.extract p (p + 32))); p := p + 32
      else out := out.push none
    if p != body.size then none
    pure out
  match tag.toNat with
  | 0 =>
    let klen := leN body 1 4
    let (k, isLeaf) ← hpDecode (body.extract 5 (5 + klen))
    if !isLeaf || body.size != 5 + klen + 36 then none
    pure (.leaf k (leN body (5 + klen) 4) (body.extract (9 + klen) (41 + klen)))
  | 3 =>
    let klen := leN body 1 4
    let (k, isLeaf) ← hpDecode (body.extract 5 (5 + klen))
    if isLeaf || body.size != 5 + klen + 32 then none
    pure (.ext k (body.extract (5 + klen) (37 + klen)))
  | 1 => pure (.branch none (← kids 1))
  | 2 =>
    if body.size < 37 then none
    pure (.branch (some (leN body 1 4, body.extract 5 37)) (← kids 37))
  | _ => none

/-- What one lookup visits: retrieved node hashes in order, and the value reference if present. -/
structure Lookup where
  nodes : List ByteArray
  value : Option (Nat × ByteArray)

def errMissing : String := "StorageInconsistentState(MissingTrieValue)"

def isPrefixN : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && isPrefixN as bs

/-- `lookup_from_state_column` from node `h` (fuel: one per node; paths are ≤ 2·key nibbles). -/
def lookupFrom (st : Store) : Nat → ByteArray → List Nat → List ByteArray → Except String Lookup
  | 0, _, _, _ => .error "unmodeled: lookup fuel"
  | fuel + 1, h, key, acc =>
    match st.get? h with
    | none => .error errMissing
    | some bytes =>
      let acc := h :: acc
      match decodeNode bytes with
      | none => .error "StorageInconsistentState(node decoding)"
      | some (.leaf k len vh) =>
        .ok { nodes := acc.reverse, value := if k == key then some (len, vh) else none }
      | some (.ext k c) =>
        if isPrefixN k key then lookupFrom st fuel c (key.drop k.length) acc
        else .ok { nodes := acc.reverse, value := none }
      | some (.branch v kids) =>
        match key with
        | [] => .ok { nodes := acc.reverse, value := v }
        | n :: rest =>
          match kids[n]? with
          | some (some c) => lookupFrom st fuel c rest acc
          | _ => .ok { nodes := acc.reverse, value := none }

def emptyRoot : ByteArray := ⟨Array.replicate 32 0⟩

def lookup (st : Store) (root : ByteArray) (key : ByteArray) : Except String Lookup :=
  if root == emptyRoot then .ok { nodes := [], value := none }
  else lookupFrom st (2 * key.size * 2 + 4) root (nibblesOf key) []

/-- `AccountingState` (`ext.rs:645-748`), one per chunk application. -/
structure Acct where
  cache : Std.HashMap ByteArray Unit := {}
  db : Nat := 0
  mem : Nat := 0

def Acct.touch (a : Acct) (h : ByteArray) : Acct :=
  if a.cache.contains h then { a with mem := a.mem + 1 }
  else { a with db := a.db + 1, cache := a.cache.insert h () }

def Acct.touchAll (a : Acct) (hs : List ByteArray) : Acct := hs.foldl Acct.touch a

/-- Chunk-scoped trie state of the trie-backed `External`. `overlay` = the `TrieUpdate` changes of
the chunk so far (committed receipts + the current receipt's prospective), keyed by full trie key;
`none` = removed. `prefix` = `TrieKey::ContractData` prefix of the current account
(`col::CONTRACT_DATA = 9`, account id, `ACCOUNT_DATA_SEPARATOR = ','`). -/
structure RealStore where
  store : Store
  root : ByteArray
  overlay : Std.HashMap ByteArray (Option ByteArray) := {}
  acct : Acct := {}
  pfx : ByteArray := .empty

def contractDataPrefix (account : String) : ByteArray :=
  (ByteArray.mk #[9]) ++ account.toUTF8 ++ (ByteArray.mk #[44])

end NearSpecV3.Wasm.TTN
