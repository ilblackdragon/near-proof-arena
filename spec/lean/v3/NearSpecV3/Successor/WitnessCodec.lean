import NearSpecV3.ChunkValidationD2

/-! The authenticated witness envelope is unchanged across action/receipt codec versions.
Only the receipt and transaction parsers vary; the legacy specialization is definitionally equal.
-/
namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2

def pEntryWith (receipt : P D2.Rcpt) : P EntryD2 := fun bs => do
  let (k, bs) ← pHash "ChunkHash" bs
  let (rs, bs) ← pVec "proof receipts" receipt bs
  let (f, bs) ← pU64 "from_shard_id" bs
  let (t, bs) ← pU64 "to_shard_id" bs
  let (path, bs) ← pVec "merkle path" pPathItem bs
  pure (⟨k, rs, ⟨f, t, path⟩⟩, bs)

def decodeStateWitnessWith (receipt : P D2.Rcpt) (transaction : P D2.TxD2) (bs : Bytes) : Except String StateWitnessD2 := do
  if lenT bs > MAX_WITNESS then throw "decode: witness larger than 64 MiB"
  let (t, bs) ← pU8 "ChunkStateWitness tag" bs
  if t != 1 then throw "decode: ChunkStateWitness tag"
  let (eid, bs) ← pHash "epoch_id" bs
  let ((ib, ci), bs) ← pChunkHeader bs
  let (main, bs) ← pTransition bs
  let (entries, bs) ← pVec "source_receipt_proofs" (pEntryWith receipt) bs
  let (arh, bs) ← pHash "applied_receipts_hash" bs
  let (txs, bs) ← pVec "transactions" transaction bs
  let (impl, bs) ← pVec "implicit_transitions" pTransition bs
  let (ntxs, bs) ← pVec "new_transactions" transaction bs
  if !bs.isEmpty then throw "decode: Not all bytes read"
  pure ⟨eid, ib, ci, main, entries, arh, txs, impl, ntxs⟩

theorem decodeStateWitnessWith_legacy (bs : Bytes) :
    decodeStateWitnessWith pRcpt pTxD2 bs = decodeStateWitnessD2 bs := rfl

end NearSpecV3.Successor
