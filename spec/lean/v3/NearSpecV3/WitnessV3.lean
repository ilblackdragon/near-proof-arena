import NearSpecV3.ClaimV3

/-!
# `witness.bin` — `near-arena-witness-v3` and the real `ChunkStateWitness` bytes

`witness.bin = bytes "near-arena-witness-v3" ‖ bytes state_witness ‖ Vec<bytes> contract_code`
(spec/claim-v3.md §3). `state_witness` is nearcore's borsh `ChunkStateWitness::V2`
(`core/primitives/src/stateless_validation/state_witness.rs:93-166, 279-295`),
decoded here with nearcore's rules:

* trailing bytes rejected; total size ≤ 64 MiB (`MAX_UNCOMPRESSED_STATE_WITNESS_SIZE`);
* `HashMap<ChunkHash, ReceiptProof>` (`source_receipt_proofs`) is decoded leniently,
  exactly like borsh 1.5.3 without `de_strict_order` (`de/mod.rs:541-574`): entries
  in any order, a duplicate key keeps the **last** value. We keep the raw entry list;
  `proofMap` below implements last-wins lookup and the map's length (number of
  distinct keys). Canonicality is decided by the relation, not the decoder.
* `MerklePathItem.direction` is a derived enum: 0 = Left, 1 = Right, else error.

Domain D0 (spec §6) is enforced here only where the decoder would otherwise need
the full nearcore type universe: every receipt in every entry (including entries
overridden by a later duplicate) must have the D0 receipt shape (`w.proof_shape`),
and `transactions`/`new_transactions` must be empty (`w.no_txs`).
-/

namespace NearSpecV3

open NearSpec

structure Transition where
  blockHash : Bytes
  values : List Bytes
  postStateRoot : Bytes
  deriving Repr

structure ShardProof where
  fromShard : Nat
  toShard : Nat
  path : List (Bytes × Nat)   -- (sibling hash, direction 0 = Left / 1 = Right)
  deriving Repr

structure ProofEntry where
  key : Bytes                 -- ChunkHash
  receipts : List Receipt
  proof : ShardProof
  deriving Repr

structure StateWitness where
  epochId : Bytes
  innerBytes : Bytes          -- canonical (re-encoded) bytes of the header's tagged inner
  inner : ChunkInner
  main : Transition
  entries : List ProofEntry   -- in encoded order (duplicates allowed)
  appliedReceiptsHash : Bytes
  nTransactions : Nat
  implicit : List Transition
  nNewTransactions : Nat
  deriving Repr

def MAX_WITNESS : Nat := 67108864

def pTransition : P Transition := fun bs => do
  let (bh, bs) ← pHash "transition block_hash" bs
  let (t, bs) ← pU8 "PartialState tag" bs
  if t != 0 then throw "decode: PartialState tag"
  let (vals, bs) ← pVec "trie values" (pBytes "trie value") bs
  let (post, bs) ← pHash "post_state_root" bs
  pure (⟨bh, vals, post⟩, bs)

def pPathItem : P (Bytes × Nat) := fun bs => do
  let (h, bs) ← pHash "path hash" bs
  let (d, bs) ← pU8 "path direction" bs
  if d > 1 then throw "decode: MerklePathItem direction"
  pure ((h, d), bs)

def pEntry : P ProofEntry := fun bs => do
  let (k, bs) ← pHash "ChunkHash" bs
  let (rs, bs) ← pVec "proof receipts" pReceipt bs
  let (f, bs) ← pU64 "from_shard_id" bs
  let (t, bs) ← pU64 "to_shard_id" bs
  let (path, bs) ← pVec "merkle path" pPathItem bs
  pure (⟨k, rs, ⟨f, t, path⟩⟩, bs)

/-- The whole `ShardChunkHeader::V3` (tag 2 ‖ tagged inner ‖ height_included ‖ signature);
returns the canonical inner bytes and the parsed inner. Height_included and the
signature are decoded (nearcore rejects invalid signature encodings) but unused. -/
def pChunkHeader : P (Bytes × ChunkInner) := fun bs => do
  let (t, bs) ← pU8 "ShardChunkHeader tag" bs
  if t != 2 then throw "invalid: ShardChunkHeader is not V3"
  let start := bs
  let (ci, bs) ← pChunkInner bs
  let innerBytes := consumed start bs
  let (_, bs) ← pU64 "height_included" bs
  let (_, bs) ← pSignature "chunk signature" bs
  pure ((innerBytes, ci), bs)

def decodeStateWitness (bs : Bytes) : Except String StateWitness := do
  if bs.length > MAX_WITNESS then throw "decode: witness larger than 64 MiB"
  let (t, bs) ← pU8 "ChunkStateWitness tag" bs
  if t != 1 then throw "decode: ChunkStateWitness tag"
  let (eid, bs) ← pHash "epoch_id" bs
  let ((ib, ci), bs) ← pChunkHeader bs
  let (main, bs) ← pTransition bs
  let (entries, bs) ← pVec "source_receipt_proofs" pEntry bs
  let (arh, bs) ← pHash "applied_receipts_hash" bs
  let (ntx, bs) ← pU32 "transactions" bs
  if ntx != 0 then throw "out of domain (w.no_txs): transactions"
  let (impl, bs) ← pVec "implicit_transitions" pTransition bs
  let (nnew, bs) ← pU32 "new_transactions" bs
  if nnew != 0 then throw "out of domain (w.no_txs): new_transactions"
  if !bs.isEmpty then throw "decode: Not all bytes read"
  pure ⟨eid, ib, ci, main, entries, arh, ntx, impl, nnew⟩

/-- `witness.bin` → (state witness bytes, contract codes). -/
def decodeWitnessFile (bs : Bytes) : Except String (Bytes × List Bytes) := do
  let ((), bs) ← dTag witnessTag "witness format" bs
  let (sw, bs) ← pBytes "state_witness" bs
  let (codes, bs) ← pVec "contract_code" (pBytes "code") bs
  if !bs.isEmpty then throw "decode: trailing bytes in witness.bin"
  pure (sw, codes)

/-! ## Last-wins map semantics of the decoded `HashMap` -/

def lookupLast (k : Bytes) : List ProofEntry → Option ProofEntry
  | [] => none
  | e :: es =>
    match lookupLast k es with
    | some x => some x
    | none => if e.key == k then some e else none

def distinctKeys : List ProofEntry → List Bytes
  | [] => []
  | e :: es => let ks := distinctKeys es; if ks.contains e.key then ks else e.key :: ks

end NearSpecV3
