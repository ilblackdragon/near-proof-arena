import ZkFormal.Near.Spec.Good

/-!
# ZkFormal.Near.Spec.Prune — records of a witness (`extOf`)

`extOf c w` prunes the witness trie to the nodes on the paths of the touched
keys (the receivers' account keys), numbers the revealed nodes (root `0`,
every node once, preorder), marks the receivers' value slots `touched` (their
bytes go to `vals0`), turns every other revealed value into a `ref`, and
records each receipt's slot.  Hashes are unchanged and
`revealedOf ≤ revealedBytes` (`Spec/CompleteTrie.lean`).

The construction is in two steps, both structurally recursive (kernel
reducible and executable):

* `prune keys t : PTrie` — keeps exactly the nodes some key of `keys` reaches
  (a leaf only if its key *is* one of the remaining keys, an extension only if
  its key is a prefix of one), replaces every other subtree by
  `.hash t.hashOf`, and turns a branch value no key ends at into a `ref`.
  In a pruned trie every `.val` slot is the slot of a key in `keys`.
* `recs p base : List NodeRec` — preorder records of `p` with root id `base`
  (`.val` ↦ `touched`, `.ref` ↦ `ref`, `.hash` child ↦ `Kid.hash`);
  `vl p` the per-node revealed value (relative ids), `slotIdx p key` the
  relative id of the node `p.get key` reads.
-/

namespace ZkFormal.Near

open NearSpec NearSpec.TransferV1

namespace Prune

/-! ## Pruning a partial trie to a set of keys -/

/-- Keys continuing below an extension with key `k`. -/
def afterExt (k : List Nat) (keys : List (List Nat)) : List (List Nat) :=
  keys.filterMap fun key => if isPrefix k key then some (key.drop k.length) else none

/-- Keys continuing below child `j` of a branch. -/
def afterNib (j : Nat) (keys : List (List Nat)) : List (List Nat) :=
  keys.filterMap fun key =>
    match key with
    | x :: rest => if x = j then some rest else none
    | [] => none

/-- An unrevealed copy of a value slot (same `valueRef`). -/
def toRef : Slot → Slot
  | .val v => .ref v.length (sha256 v)
  | .ref len h => .ref len h

mutual
/-- Prune `t` to the nodes reached by `keys` (nibble paths relative to `t`). -/
def prune (keys : List (List Nat)) : PTrie → PTrie
  | .hash h => .hash h
  | .leaf k v mem =>
    if keys.contains k then .leaf k v mem else .hash (PTrie.leaf k v mem).hashOf
  | .ext k c mem =>
    if (afterExt k keys).isEmpty then .hash (PTrie.ext k c mem).hashOf
    else .ext k (prune (afterExt k keys) c) mem
  | .branch v cs mem =>
    if keys.isEmpty then .hash (PTrie.branch v cs mem).hashOf
    else .branch (if keys.contains [] then v else v.map toRef) (pruneKids keys 0 cs) mem
/-- Prune the children of a branch; `j` = index of the first child. -/
def pruneKids (keys : List (List Nat)) : Nat → Kids → Kids
  | _, .nil => .nil
  | j, .none r => .none (pruneKids keys (j + 1) r)
  | j, .some c r => .some (prune (afterNib j keys) c) (pruneKids keys (j + 1) r)
end

/-! ## Numbering (preorder) -/

mutual
/-- Number of revealed (non-`hash`) nodes. -/
def cnt : PTrie → Nat
  | .hash _ => 0
  | .leaf _ _ _ => 1
  | .ext _ c _ => 1 + cnt c
  | .branch _ cs _ => 1 + cntKids cs
def cntKids : Kids → Nat
  | .nil => 0
  | .none r => cntKids r
  | .some c r => cnt c + cntKids r
end

def vslot : Slot → VSlot
  | .val _ => .touched
  | .ref len h => .ref len h

/-- The child slot of subtree `c` whose root (if revealed) gets id `id`. -/
def kidOf : PTrie → Nat → Kid
  | .hash h, _ => .hash h
  | _, id => .node id

/-- Child slots of a branch whose first revealed child gets id `id`. -/
def kidsList : Kids → Nat → List Kid
  | .nil, _ => []
  | .none r, id => .none :: kidsList r id
  | .some c r, id => kidOf c id :: kidsList r (id + cnt c)

mutual
/-- Preorder records of `p`, root id `b`. -/
def recs : PTrie → Nat → List NodeRec
  | .hash _, _ => []
  | .leaf k v mem, _ => [.leaf k (vslot v) mem]
  | .ext k c mem, b => .ext k (kidOf c (b + 1)) mem :: recs c (b + 1)
  | .branch v cs mem, b => .branch (v.map vslot) (kidsList cs (b + 1)) mem :: recsKids cs (b + 1)
def recsKids : Kids → Nat → List NodeRec
  | .nil, _ => []
  | .none r, b => recsKids r b
  | .some c r, b => recs c b ++ recsKids r (b + cnt c)
end

mutual
/-- Revealed value of each node (preorder, relative ids). -/
def vl : PTrie → List (Option Bytes)
  | .hash _ => []
  | .leaf _ v _ => [v.get]
  | .ext _ c _ => none :: vl c
  | .branch v cs _ => v.bind Slot.get :: vlKids cs
def vlKids : Kids → List (Option Bytes)
  | .nil => []
  | .none r => vlKids r
  | .some c r => vl c ++ vlKids r
end

mutual
/-- Relative id of the node whose value `p.get key` reads (mirrors `get`). -/
def slotIdx : PTrie → List Nat → Nat
  | .hash _, _ => 0
  | .leaf _ _ _, _ => 0
  | .ext k c _, key => 1 + slotIdx c (key.drop k.length)
  | .branch _ _ _, [] => 0
  | .branch _ cs _, n :: rest => 1 + slotIdxKids cs n rest
def slotIdxKids : Kids → Nat → List Nat → Nat
  | .nil, _, _ => 0
  | .none _, 0, _ => 0
  | .some c _, 0, key => slotIdx c key
  | .none r, i + 1, key => slotIdxKids r i key
  | .some c r, i + 1, key => cnt c + slotIdxKids r i key
end

/-- The touched keys of a witness: the receivers' account keys. -/
def keysOf (w : Witness) : List (List Nat) :=
  w.receipts.map fun r => accountKeyPath r.receiverId

/-- The pruned witness trie. -/
def prunedOf (w : Witness) : PTrie := prune (keysOf w) w.trie

/-- Value function of a list of revealed values. -/
def valsOfList (l : List (Option Bytes)) (k : Nat) : Bytes :=
  match l[k]? with
  | some (some v) => v
  | _ => []

end Prune

open Prune in
/-- Records of a witness (pruned to the touched paths). -/
def extOf (_c : Claim) (w : Witness) : Ext :=
  { ns := recs (prunedOf w) 0
    vals0 := valsOfList (vl (prunedOf w))
    rs := w.receipts
    slot := fun r => slotIdx (prunedOf w)
      (accountKeyPath (w.receipts.getD r ⟨[], [], [], [], ⟨0, []⟩, 0, 0⟩).receiverId) }

end ZkFormal.Near
