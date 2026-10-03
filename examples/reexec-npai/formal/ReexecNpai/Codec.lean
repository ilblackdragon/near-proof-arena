import NearSpec.TransferV1
import NearSpec.ClaimCodec

/-!
# `reexec-npai-v1` proof codec

The proof carries the same relation witness as `reexec-witness-v1` (the
receipts, byte-identical to the request, and the partial pre-state trie), but
the trie is laid out for a bytecode verifier:

```
proof = u32 n ‖ Receipt × n                (nearcore borsh = NearSpec.encodeReceipts)
        ‖ u32 N ‖ rec × N                   (revealed trie nodes in post-order; the last is the root)
rec   = 1 ‖ u32 |v| ‖ v ‖ pre(leaf)               leaf, revealed value
      | 2 ‖ pre(leaf)                              leaf, value by reference
      | 3 ‖ u8 e ‖ pre(ext)                        extension; e = 1 iff the child is revealed
      | 4 ‖ u16 ex ‖ pre(branch)                   branch without value
      | 5 ‖ u32 |v| ‖ v ‖ u16 ex ‖ pre(branch')    branch, revealed value
      | 6 ‖ u16 ex ‖ pre(branch')                  branch, value by reference
pre(leaf)    = 0 ‖ u32 |hp| ‖ hp ‖ u32 len ‖ h32 ‖ u64 mem
pre(ext)     = 3 ‖ u32 |hp| ‖ hp ‖ h32 ‖ u64 mem
pre(branch)  = 1 ‖ u16 bm ‖ h32 × popcount bm ‖ u64 mem
pre(branch') = 2 ‖ u32 len ‖ h32 ‖ u16 bm ‖ h32 × popcount bm ‖ u64 mem
```

`pre(·)` is exactly nearcore's `RawTrieNodeWithSize` serialization, whose
SHA-256 is the node hash, except at *placeholders*: the value-hash field of a
revealed value and the child-hash field of a revealed child. The decoder
ignores placeholder bytes; the verifier overwrites them with the computed
hashes before hashing the node. `hp` is the hex-prefix key encoding (it must
be canonical), `bm` the children bitmap and `ex ⊆ bm` the revealed children.
Revealed children are the records that precede their parent (post-order), so
the decoder is a fold with a stack of finished subtrees.
-/

namespace ReexecNpai

open NearSpec NearSpec.TransferV1

/-! ## Receipts (same as `reexec-witness-v1`) -/

/-- Fixed tail between `gas_price` and `deposit`: no output data receivers, no
input data ids, exactly one action, `Action::Transfer`. -/
def receiptMid : Bytes := u32 0 ++ u32 0 ++ u32 1 ++ [3]

/-- Strict decoder of one single-Transfer action receipt (nearcore borsh). -/
def decReceipt : Parser Receipt := fun bs =>
  match readBorshBytes bs with
  | none => none
  | some (pred, bs) =>
  match readBorshBytes bs with
  | none => none
  | some (recv, bs) =>
  match readHash bs with
  | none => none
  | some (rid, bs) =>
  match readU8 bs with
  | none => none
  | some (tag, bs) =>
  if tag ≠ 0 then none else
  match readBorshBytes bs with
  | none => none
  | some (signer, bs) =>
  match readU8 bs with
  | none => none
  | some (kt, bs) =>
  if kt ≠ 0 ∧ kt ≠ 1 then none else
  match takeN (if kt = 0 then 32 else 64) bs with
  | none => none
  | some (kd, bs) =>
  match readU128 bs with
  | none => none
  | some (gp, bs) =>
  match takeN 13 bs with
  | none => none
  | some (mid, bs) =>
  if mid ≠ receiptMid then none else
  (readU128 bs).map fun (dep, r) =>
    ({ predecessorId := pred, receiverId := recv, receiptId := rid, signerId := signer,
       signerPk := ⟨kt, kd⟩, gasPrice := gp, deposit := dep }, r)

/-! ## Trie: encoder -/

def revealed : PTrie → Bool
  | .hash _ => false
  | _ => true

/-- Slot bytes of a child in its parent's preimage as written by the honest
prover: the hash of an unrevealed child, zeros (placeholder) for a revealed
one. -/
def slotOf : PTrie → Bytes
  | .hash h => h
  | _ => zeros 32

def kidSlots : Kids → Bytes
  | .nil => []
  | .none r => kidSlots r
  | .some c r => slotOf c ++ kidSlots r

/-- Bitmap of the revealed children (bit `i` = child `i`). -/
def expBits : Kids → Nat → Nat
  | .nil, _ => 0
  | .none r, i => expBits r (i + 1)
  | .some c r, i => (if revealed c then 2 ^ i else 0) + expBits r (i + 1)

/-- `u32 len ‖ hash` part of a value slot (placeholder hash for a revealed value). -/
def refPart : Slot → Bytes
  | .val v => u32 v.length ++ zeros 32
  | .ref len h => u32 len ++ h

/-- Revealed value bytes in front of a record. -/
def valPart : Slot → Bytes
  | .val v => u32 v.length ++ v
  | .ref _ _ => []

def kindLeaf : Slot → UInt8
  | .val _ => 1
  | .ref _ _ => 2

def kindBr : Option Slot → UInt8
  | none => 4
  | some (.val _) => 5
  | some (.ref _ _) => 6

def optValPart : Option Slot → Bytes
  | none => []
  | some s => valPart s

/-- Head of a branch preimage: tag and value reference. -/
def brHead : Option Slot → Bytes
  | none => [1]
  | some s => [2] ++ refPart s

def preLeaf (k : List Nat) (s : Slot) (m : Nat) : Bytes :=
  [0] ++ u32 (hexPrefix k true).length ++ hexPrefix k true ++ refPart s ++ u64 m

def preExt (k : List Nat) (c : PTrie) (m : Nat) : Bytes :=
  [3] ++ u32 (hexPrefix k false).length ++ hexPrefix k false ++ slotOf c ++ u64 m

def preBr (v : Option Slot) (cs : Kids) (m : Nat) : Bytes :=
  brHead v ++ u16 (kidsBitmap cs 0) ++ kidSlots cs ++ u64 m

mutual
/-- Post-order encoding of the revealed nodes. -/
def encT : PTrie → Bytes
  | .hash _ => []
  | .leaf k s m => [kindLeaf s] ++ valPart s ++ preLeaf k s m
  | .ext k c m => encT c ++ [3, if revealed c then 1 else 0] ++ preExt k c m
  | .branch v cs m =>
    encKids cs ++ [kindBr v] ++ optValPart v ++ u16 (expBits cs 0) ++ preBr v cs m
def encKids : Kids → Bytes
  | .nil => []
  | .none r => encKids r
  | .some c r => encT c ++ encKids r
end

mutual
/-- Number of revealed nodes. -/
def cntT : PTrie → Nat
  | .hash _ => 0
  | .leaf _ _ _ => 1
  | .ext _ c _ => cntT c + 1
  | .branch _ cs _ => cntKids cs + 1
def cntKids : Kids → Nat
  | .nil => 0
  | .none r => cntKids r
  | .some c r => cntT c + cntKids r
end

def encTrie (t : PTrie) : Bytes := u32 (cntT t) ++ encT t

def encodeProof (w : Witness) : Bytes := encodeReceipts w.receipts ++ encTrie w.trie

/-! ## Trie: decoder -/

/-- The nibbles `k` with `hexPrefix k leaf = hp`, if `hp` is canonical. -/
def keyOfHP (leaf : Bool) : Bytes → Option (List Nat)
  | [] => none
  | b :: tl =>
    let lb := if leaf then 32 else 0
    if b.toNat = lb then some (nibbles tl)
    else if 16 + lb ≤ b.toNat ∧ b.toNat < 32 + lb then some ((b.toNat - (16 + lb)) :: nibbles tl)
    else none

/-- Number of set bits among the low `n` bits. -/
def popc : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => x % 2 + popc n (x / 2)

/-- Split into `n` chunks of 32 bytes (`bs` has length `32 n`). -/
def chunks32 : Nat → Bytes → List Bytes
  | 0, _ => []
  | n + 1, bs => bs.take 32 :: chunks32 n (bs.drop 32)

/-- The 16 child slots from the bitmaps `bm` (present) and `ex` (revealed),
the slot bytes `hs` of the present children and the revealed children `cs`
(both in index order); every list must be consumed exactly. -/
def mkKids : Nat → Nat → Nat → List Bytes → List PTrie → Option Kids
  | 0, _, _, [], [] => some .nil
  | 0, _, _, _, _ => none
  | n + 1, bm, ex, hs, cs =>
    if bm % 2 = 1 then
      match hs with
      | [] => none
      | h :: hs' =>
        if ex % 2 = 1 then
          match cs with
          | [] => none
          | c :: cs' => (mkKids n (bm / 2) (ex / 2) hs' cs').map (.some c)
        else (mkKids n (bm / 2) (ex / 2) hs' cs).map (.some (.hash h))
    else if ex % 2 = 1 then none
    else (mkKids n (bm / 2) (ex / 2) hs cs).map .none

/-- Pop `n` finished subtrees (stack top first); the result is in push order. -/
def popN : Nat → List PTrie → Option (List PTrie × List PTrie)
  | 0, stk => some ([], stk)
  | _ + 1, [] => none
  | n + 1, x :: stk => (popN n stk).map fun (cs, r) => (cs ++ [x], r)

/-- Value part of a leaf/branch record: `kind ∈ {1, 5}` has a revealed value. -/
def decVal (hasVal : Bool) : Parser (Option Bytes) := fun bs =>
  if hasVal then (readBorshBytes bs).map fun (v, r) => (some v, r) else some (none, bs)

/-- The slot from the revealed value (if any) and the `len ‖ h32` fields. -/
def mkSlot (vo : Option Bytes) (len : Nat) (h : Bytes) : Option Slot :=
  match vo with
  | some v => if len = v.length then some (.val v) else none
  | none => some (.ref len h)

/-- One leaf record body (after the kind byte). -/
def decLeaf (hasVal : Bool) (stk : List PTrie) : Parser (List PTrie) := fun bs =>
  match decVal hasVal bs with
  | none => none
  | some (vo, bs) =>
  match readU8 bs with
  | none => none
  | some (tag, bs) =>
  if tag ≠ 0 then none else
  match readU32 bs with
  | none => none
  | some (hl, bs) =>
  match takeN hl bs with
  | none => none
  | some (hp, bs) =>
  match keyOfHP true hp with
  | none => none
  | some key =>
  match readU32 bs with
  | none => none
  | some (len, bs) =>
  match takeN 32 bs with
  | none => none
  | some (h, bs) =>
  match readU64 bs with
  | none => none
  | some (mm, bs) =>
  (mkSlot vo len h).map fun s => (.leaf key s mm :: stk, bs)

/-- One extension record body. -/
def decExt (stk : List PTrie) : Parser (List PTrie) := fun bs =>
  match readU8 bs with
  | none => none
  | some (e, bs) =>
  if e > 1 then none else
  match readU8 bs with
  | none => none
  | some (tag, bs) =>
  if tag ≠ 3 then none else
  match readU32 bs with
  | none => none
  | some (hl, bs) =>
  match takeN hl bs with
  | none => none
  | some (hp, bs) =>
  match keyOfHP false hp with
  | none => none
  | some key =>
  match takeN 32 bs with
  | none => none
  | some (h, bs) =>
  match readU64 bs with
  | none => none
  | some (mm, bs) =>
  if e = 1 then
    match stk with
    | [] => none
    | c :: stk' => some (.ext key c mm :: stk', bs)
  else some (.ext key (.hash h) mm :: stk, bs)

/-- One branch record body; `kind ∈ {4, 5, 6}`. -/
def decBranch (kind : Nat) (stk : List PTrie) : Parser (List PTrie) := fun bs =>
  match decVal (kind = 5) bs with
  | none => none
  | some (vo, bs) =>
  match readU16 bs with
  | none => none
  | some (ex, bs) =>
  match readU8 bs with
  | none => none
  | some (tag, bs) =>
  if tag ≠ (if kind = 4 then 1 else 2) then none else
  match (if kind = 4 then some ((0, []), bs)
         else match readU32 bs with
              | none => none
              | some (len, bs) => (takeN 32 bs).map fun (h, r) => ((len, h), r)) with
  | none => none
  | some ((len, h), bs) =>
  match readU16 bs with
  | none => none
  | some (bm, bs) =>
  match takeN (32 * popc 16 bm) bs with
  | none => none
  | some (slots, bs) =>
  match readU64 bs with
  | none => none
  | some (mm, bs) =>
  match (if kind = 4 then some none else (mkSlot vo len h).map some) with
  | none => none
  | some v =>
  match popN (popc 16 ex) stk with
  | none => none
  | some (cs, stk') =>
  (mkKids 16 bm ex (chunks32 (popc 16 bm) slots) cs).map fun kids =>
    (.branch v kids mm :: stk', bs)

/-- One record. -/
def decRec (stk : List PTrie) : Parser (List PTrie) := fun bs =>
  match bs with
  | [] => none
  | kd :: bs =>
    if kd.toNat = 1 then decLeaf true stk bs
    else if kd.toNat = 2 then decLeaf false stk bs
    else if kd.toNat = 3 then decExt stk bs
    else if kd.toNat = 4 ∨ kd.toNat = 5 ∨ kd.toNat = 6 then decBranch kd.toNat stk bs
    else none

def decRecs : Nat → List PTrie → Parser (List PTrie)
  | 0, stk, bs => some (stk, bs)
  | n + 1, stk, bs =>
    match decRec stk bs with
    | none => none
    | some (stk', bs') => decRecs n stk' bs'

/-- The trie section: `u32 N ‖ rec × N`, exactly one finished tree, nothing after. -/
def decTrie (bs : Bytes) : Option PTrie :=
  match readU32 bs with
  | none => none
  | some (n, bs) =>
    match decRecs n [] bs with
    | some ([t], []) => some t
    | _ => none

def decodeProof (pb : Bytes) : Option Witness :=
  match readU32 pb with
  | none => none
  | some (n, bs) =>
    match readMany decReceipt n bs with
    | none => none
    | some (rs, bs) => (decTrie bs).map fun t => ⟨rs, t⟩

end ReexecNpai
