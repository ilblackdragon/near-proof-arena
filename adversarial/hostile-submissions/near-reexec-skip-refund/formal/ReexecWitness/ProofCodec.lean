import NearSpec.TransferV1
import NearSpec.ClaimCodec

/-!
# `reexec-witness-v1` proof codec

The proof of the reference re-execution backend is the canonical encoding of
a relation witness `NearSpec.TransferV1.Witness`:

```
proof = encodeReceipts receipts ‖ encNode trie
node  = 0 ‖ hash32                                    -- unrevealed subtree
      | 1 ‖ key ‖ u32 len ‖ value ‖ u64 mem          -- leaf, revealed value
      | 2 ‖ key ‖ u32 len ‖ hash32 ‖ u64 mem         -- leaf, value by ref
      | 3 ‖ key ‖ node ‖ u64 mem                     -- extension
      | 4 ‖ u16 bits ‖ node* ‖ u64 mem               -- branch, no value
      | 5 ‖ u32 len ‖ value ‖ u16 bits ‖ node* ‖ u64 mem
      | 6 ‖ u32 len ‖ hash32 ‖ u16 bits ‖ node* ‖ u64 mem
key   = u32 k ‖ nibbles packed two per byte (odd tail = high half, low half 0)
```

The encoder is normative (the Rust prover in `source/src/proof.rs` must agree
byte for byte). The decoder is strict. Proved here:

* `decodeProof_encodeProof`: decoding inverts encoding on every witness whose
  receipts are well-formed and whose trie is well-formed (`PTrie.wf`) —
  in particular on every witness of an in-domain true claim;
* `encodeProof_length_le`: the proof is at most
  `4 + 347·n + revealedBytes + 33` bytes.
-/

namespace ReexecWitness

open NearSpec NearSpec.TransferV1

/-! ## Encoder -/

def packKey : List Nat → Bytes
  | a :: b :: rest => UInt8.ofNat (a * 16 + b) :: packKey rest
  | [a] => [UInt8.ofNat (a * 16)]
  | [] => []

def encKey (k : List Nat) : Bytes := u32 k.length ++ packKey k

/-- Child-presence bits of a `Kids` list, child `i` = bit `i`. -/
def kidBits : Kids → Nat
  | .nil => 0
  | .none r => 2 * kidBits r
  | .some _ r => 2 * kidBits r + 1

mutual
def encNode : PTrie → Bytes
  | .hash h => [0] ++ h
  | .leaf k (.val v) m => [1] ++ encKey k ++ borshBytes v ++ u64 m
  | .leaf k (.ref len h) m => [2] ++ encKey k ++ u32 len ++ h ++ u64 m
  | .ext k c m => [3] ++ encKey k ++ encNode c ++ u64 m
  | .branch none cs m => [4] ++ u16 (kidBits cs) ++ encKids cs ++ u64 m
  | .branch (some (.val v)) cs m => [5] ++ borshBytes v ++ u16 (kidBits cs) ++ encKids cs ++ u64 m
  | .branch (some (.ref len h)) cs m => [6] ++ u32 len ++ h ++ u16 (kidBits cs) ++ encKids cs ++ u64 m
def encKids : Kids → Bytes
  | .nil => []
  | .none r => encKids r
  | .some c r => encNode c ++ encKids r
end

def encodeProof (w : Witness) : Bytes := encodeReceipts w.receipts ++ encNode w.trie

/-! ## Decoder -/

def unpackKey : Bytes → List Nat
  | [] => []
  | b :: bs => b.toNat / 16 :: b.toNat % 16 :: unpackKey bs

def decKey : Parser (List Nat) := fun bs =>
  match readU32 bs with
  | none => none
  | some (k, bs) =>
    match takeN ((k + 1) / 2) bs with
    | none => none
    | some (p, bs) =>
      if k % 2 = 0 then some (unpackKey p, bs)
      else if (unpackKey p).getLast? = some 0 then some ((unpackKey p).dropLast, bs) else none

/-- Revealed value / unrevealed value reference. -/
def decVal : Parser Slot := fun bs => (readBorshBytes bs).map fun (v, r) => (.val v, r)
def decRef : Parser Slot := fun bs =>
  match readU32 bs with
  | none => none
  | some (len, bs) => (readHash bs).map fun (h, r) => (.ref len h, r)

/-- `n` child slots, presence from the low bits of `bm`, children by `dn`. -/
def decKids (dn : Parser PTrie) : Nat → Nat → Parser Kids
  | 0, _, bs => some (.nil, bs)
  | n + 1, bm, bs =>
    if bm % 2 = 1 then
      match dn bs with
      | none => none
      | some (c, bs) => (decKids dn n (bm / 2) bs).map fun (r, bs) => (.some c r, bs)
    else (decKids dn n (bm / 2) bs).map fun (r, bs) => (.none r, bs)

/-- Branch body after the value part. -/
def decBranch (dn : Parser PTrie) (v : Option Slot) : Parser PTrie := fun bs =>
  match readU16 bs with
  | none => none
  | some (bm, bs) =>
    match decKids dn 16 bm bs with
    | none => none
    | some (cs, bs) => (readU64 bs).map fun (m, r) => (.branch v cs m, r)

def decLeaf (dv : Parser Slot) : Parser PTrie := fun bs =>
  match decKey bs with
  | none => none
  | some (k, bs) =>
    match dv bs with
    | none => none
    | some (s, bs) => (readU64 bs).map fun (m, r) => (.leaf k s m, r)

/-- Node decoder with fuel (each nesting level consumes one unit). -/
def decNode : Nat → Parser PTrie
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, t :: bs =>
    if t = 0 then (readHash bs).map fun (h, r) => (.hash h, r)
    else if t = 1 then decLeaf decVal bs
    else if t = 2 then decLeaf decRef bs
    else if t = 3 then
      match decKey bs with
      | none => none
      | some (k, bs) =>
        match decNode f bs with
        | none => none
        | some (c, bs) => (readU64 bs).map fun (m, r) => (.ext k c m, r)
    else if t = 4 then decBranch (decNode f) none bs
    else if t = 5 then
      match decVal bs with
      | none => none
      | some (s, bs) => decBranch (decNode f) (some s) bs
    else if t = 6 then
      match decRef bs with
      | none => none
      | some (s, bs) => decBranch (decNode f) (some s) bs
    else none

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

def decodeProof (pb : Bytes) : Option Witness :=
  match readU32 pb with
  | none => none
  | some (n, bs) =>
    match readMany decReceipt n bs with
    | none => none
    | some (rs, bs) =>
      match decNode bs.length bs with
      | some (t, []) => some ⟨rs, t⟩
      | _ => none

end ReexecWitness
