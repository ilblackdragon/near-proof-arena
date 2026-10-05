import NearSpec.SHA256

/-!
# NEAR state trie: node encoding, hashing, partial tries

Source (nearcore 2.13.4):
* `core/store/src/trie/raw_node.rs:10-92` — `RawTrieNodeWithSize { node, memory_usage: u64 }`,
  `RawTrieNode = Leaf(Vec<u8>, ValueRef)=0 | BranchNoValue(Children)=1 |
  BranchWithValue(ValueRef, Children)=2 | Extension(Vec<u8>, CryptoHash)=3`;
  `Children` = `u16` LE bitmap (bit i ⇔ child i) then child hashes in index order;
  node hash = `sha256(borsh(RawTrieNodeWithSize))`.
* `core/primitives/src/state.rs:82-87` — `ValueRef { length: u32, hash }`: values are
  never inlined in nodes.
* `core/store/src/trie/nibble_slice.rs:100-158` — nibbles high-first; hex-prefix
  `encode_nibbles(nibs, is_leaf)`.
* `core/store/src/trie/ops/interface.rs:78-105`, `trie/mod.rs:158` —
  `memory_usage` (part of the hashed bytes).

## Partial tries

A `PTrie` is the part of the shard trie a prover reveals: nodes on the paths to
the touched keys, with all other subtrees represented only by their hash
(`PTrie.hash`). Each revealed node carries the `memory_usage` stored in its
serialization. The slice never inserts/deletes keys and never changes a value's
length (Account V1 is always 72 bytes), so nearcore's update keeps the trie
shape and every `memory_usage` unchanged; only the hashes along the touched
paths change. `PTrie.set` therefore replaces a value in place and keeps every
stored `memory_usage` (see `spec/near-transfer-receipt-v1.md` §Trie).
-/

namespace NearSpec

/-- A value slot: revealed bytes, or an unrevealed `ValueRef (length, hash)`. -/
inductive Slot where
  | val (v : Bytes)
  | ref (len : Nat) (h : Bytes)
  deriving Repr, DecidableEq

mutual
inductive PTrie where
  /-- unrevealed subtree, by node hash -/
  | hash (h : Bytes)
  | leaf (key : List Nat) (v : Slot) (mem : Nat)
  | ext (key : List Nat) (child : PTrie) (mem : Nat)
  | branch (v : Option Slot) (cs : Kids) (mem : Nat)
/-- The 16 children of a branch, index order; `none` = no child. -/
inductive Kids where
  | nil
  | none (rest : Kids)
  | some (c : PTrie) (rest : Kids)
end

def Slot.valueRef : Slot → Bytes
  | .val v => u32 v.length ++ sha256 v
  | .ref len h => u32 len ++ h

def Slot.get : Slot → Option Bytes
  | .val v => some v
  | .ref _ _ => none

/-- Bytes to nibbles, high nibble first. -/
def nibbles : Bytes → List Nat
  | [] => []
  | b :: bs => b.toNat / 16 :: b.toNat % 16 :: nibbles bs

def packNibbles : List Nat → Bytes
  | a :: b :: rest => UInt8.ofNat (a * 16 + b) :: packNibbles rest
  | _ => []

/-- `NibbleSlice::encode_nibbles(nibs, is_leaf)`. -/
def hexPrefix (nibs : List Nat) (isLeaf : Bool) : Bytes :=
  let leafBit := if isLeaf then 32 else 0
  match nibs.length % 2, nibs with
  | 1, n :: rest => UInt8.ofNat (16 + n + leafBit) :: packNibbles rest
  | _, _ => UInt8.ofNat leafBit :: packNibbles nibs

def kidsBitmap : Kids → Nat → Nat
  | .nil, _ => 0
  | .none r, i => kidsBitmap r (i + 1)
  | .some _ r, i => 2 ^ i + kidsBitmap r (i + 1)

mutual
/-- Node hash (`RawTrieNodeWithSize::hash`) of a partial trie. -/
def PTrie.hashOf : PTrie → Bytes
  | .hash h => h
  | .leaf k v mem =>
    let hp := hexPrefix k true
    sha256 ([0] ++ u32 hp.length ++ hp ++ v.valueRef ++ u64 mem)
  | .ext k c mem =>
    let hp := hexPrefix k false
    sha256 ([3] ++ u32 hp.length ++ hp ++ c.hashOf ++ u64 mem)
  | .branch none cs mem =>
    sha256 ([1] ++ u16 (kidsBitmap cs 0) ++ Kids.hashes cs ++ u64 mem)
  | .branch (some v) cs mem =>
    sha256 ([2] ++ v.valueRef ++ u16 (kidsBitmap cs 0) ++ Kids.hashes cs ++ u64 mem)
def Kids.hashes : Kids → Bytes
  | .nil => []
  | .none r => Kids.hashes r
  | .some c r => c.hashOf ++ Kids.hashes r
end

def nibblesOk (k : List Nat) : Bool := k.all (· < 16)
def slotOk : Slot → Bool
  | .val v => v.length < 4294967296
  | .ref len h => len < 4294967296 && h.length == 32

mutual
/-- Well-formedness: the node serialization is injective on well-formed partial
tries (nibbles < 16, exactly 16 child slots, 32-byte hashes, widths in range),
so a hash match pins down every revealed field. -/
def PTrie.wf : PTrie → Bool
  | .hash h => h.length == 32
  | .leaf k v mem => nibblesOk k && slotOk v && mem < 18446744073709551616 &&
      (hexPrefix k true).length < 4294967296
  | .ext k c mem => nibblesOk k && c.wf && mem < 18446744073709551616 &&
      (hexPrefix k false).length < 4294967296
  | .branch v cs mem => (match v with | some s => slotOk s | none => true) &&
      Kids.wf cs 16 && mem < 18446744073709551616
def Kids.wf : Kids → Nat → Bool
  | .nil, n => n == 0
  | .none r, n => n != 0 && Kids.wf r (n - 1)
  | .some c r, n => n != 0 && c.wf && Kids.wf r (n - 1)
end

/-- Is `p` a prefix of `l`? -/
def isPrefix : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && isPrefix as bs

mutual
/-- Value stored at nibble path `key`, if the path is fully revealed and the key
exists with a revealed value. -/
def PTrie.get : PTrie → List Nat → Option Bytes
  | .hash _, _ => none
  | .leaf k v _, key => if k == key then v.get else none
  | .ext k c _, key => if isPrefix k key then c.get (key.drop k.length) else none
  | .branch v _ _, [] => v.bind Slot.get
  | .branch _ cs _, n :: rest => Kids.get cs n rest
def Kids.get : Kids → Nat → List Nat → Option Bytes
  | .nil, _, _ => none
  | .none _, 0, _ => none
  | .some c _, 0, key => c.get key
  | .none r, i + 1, key => Kids.get r i key
  | .some _ r, i + 1, key => Kids.get r i key
end

mutual
/-- Replace the (existing, revealed) value at `key` by `nv`; shape and stored
`memory_usage` unchanged. `none` if the key is not present/revealed. -/
def PTrie.set : PTrie → List Nat → Bytes → Option PTrie
  | .hash _, _, _ => none
  | .leaf k v mem, key, nv =>
    if k == key then (v.get.map fun _ => .leaf k (.val nv) mem) else none
  | .ext k c mem, key, nv =>
    if isPrefix k key then (c.set (key.drop k.length) nv).map fun c' => .ext k c' mem else none
  | .branch v cs mem, [], nv =>
    match v with
    | some (.val _) => some (.branch (some (.val nv)) cs mem)
    | _ => none
  | .branch v cs mem, n :: rest, nv => (Kids.set cs n rest nv).map fun cs' => .branch v cs' mem
def Kids.set : Kids → Nat → List Nat → Bytes → Option Kids
  | .nil, _, _, _ => none
  | .none _, 0, _, _ => none
  | .some c r, 0, key, nv => (c.set key nv).map fun c' => .some c' r
  | .none r, i + 1, key, nv => (Kids.set r i key nv).map .none
  | .some c r, i + 1, key, nv => (Kids.set r i key nv).map (.some c)
end

mutual
/-- Total serialized size of the revealed nodes and values (bytes). -/
def PTrie.revealedBytes : PTrie → Nat
  | .hash _ => 0
  | .leaf k v _ =>
    (1 + 4 + (hexPrefix k true).length + 36 + 8) + (match v with | .val b => b.length | _ => 0)
  | .ext k c _ => (1 + 4 + (hexPrefix k false).length + 32 + 8) + c.revealedBytes
  | .branch v cs _ =>
    (match v with | some (.val b) => 1 + 36 + b.length | some _ => 1 + 36 | none => 1) +
      2 + 32 * Kids.count cs + 8 + Kids.revealedBytes cs
def Kids.revealedBytes : Kids → Nat
  | .nil => 0
  | .none r => Kids.revealedBytes r
  | .some c r => c.revealedBytes + Kids.revealedBytes r
def Kids.count : Kids → Nat
  | .nil => 0
  | .none r => Kids.count r
  | .some _ r => 1 + Kids.count r
end

/-- `TrieKey::Account { account_id }` = `0x00 ‖ utf8(account_id)`
(`core/primitives/src/trie_key.rs:457-460`), as a nibble path. -/
def accountKeyPath (accountId : Bytes) : List Nat := nibbles (0 :: accountId)

end NearSpec
