import ZkFormal.V3.Fast.Hash
import NearSpecV3.ChunkValidationV0

/-!
# Header chain with the fast SHA-256 (candidate-side `@[csimp]`, see `Fast.Hash`)

Identical copies of `blockHash`, `decodeBlockV6`, `chunkHash`, `slotLeaf`, `merklizeBorsh`,
`outgoingReceiptsRoot` and `decodeBlk`, compiled with the fast hash in scope, each redirected
by a `@[csimp]` lemma proved by `rfl`.
-/

namespace ZkFormal.V3.Fast

open NearSpec NearSpecV3

def blockHashF (prevHash lite rest : Bytes) : Bytes :=
  sha256 (sha256 (sha256 lite ++ sha256 rest) ++ prevHash)

@[csimp] theorem blockHash_csimp : @blockHash = @blockHashF := rfl

def decodeBlockV6F (version : Nat) (prevHash lite rest : Bytes) : Except String BlockHdr := do
  if version != 5 then throw "out of domain (c.headers): block header is not V6"
  let (h, l) ← pU64 "height" lite
  let (eid, l) ← pHash "epoch_id" l
  let (neid, l) ← pHash "next_epoch_id" l
  let (_, l) ← pHash "prev_state_root" l
  let (_, l) ← pHash "prev_outcome_root" l
  let (ts, l) ← pU64 "timestamp" l
  let (_, l) ← pHash "next_bp_hash" l
  let (_, l) ← pHash "block_merkle_root" l
  if !l.isEmpty then throw "decode: trailing bytes in inner_lite"
  let (_, r) ← pHash "block_body_hash" rest
  let (_, r) ← pHash "prev_chunk_outgoing_receipts_root" r
  let (chr, r) ← pHash "chunk_headers_root" r
  let (_, r) ← pHash "chunk_tx_root" r
  let (rv, r) ← pHash "random_value" r
  let (_, r) ← pVec "prev_validator_proposals" pValidatorStake r
  let (_, r) ← pVec "chunk_mask" (pBool "chunk_mask") r
  let (ngp, r) ← pU128 "next_gas_price" r
  let (_, r) ← pU128 "total_supply" r
  let (_, r) ← pHash "last_final_block" r
  let (_, r) ← pHash "last_ds_final_block" r
  let (_, r) ← pU64 "block_ordinal" r
  let (_, r) ← pU64 "prev_height" r
  let (_, r) ← pOption "epoch_sync_data_hash" (pHash "epoch_sync_data_hash") r
  let (_, r) ← pVec "approvals" pApproval r
  let (_, r) ← pU32 "latest_protocol_version" r
  let (_, r) ← pVec "chunk_endorsements" (pBytes "chunk_endorsements row") r
  let (_, r) ← pOption "shard_split" (fun bs => do
      let (_, bs) ← pU64 "split shard" bs
      let (_, bs) ← pAccountId "split boundary" bs
      pure ((), bs)) r
  if !r.isEmpty then throw "decode: trailing bytes in inner_rest"
  pure { version, prevHash, height := h, epochId := eid, nextEpochId := neid, timestamp := ts,
         randomValue := rv, chunkHeadersRoot := chr, nextGasPrice := ngp,
         hash := blockHash prevHash lite rest }

@[csimp] theorem decodeBlockV6_csimp : @decodeBlockV6 = @decodeBlockV6F := rfl

def chunkHashF (innerBytes encodedMerkleRoot : Bytes) : Bytes :=
  sha256 (sha256 innerBytes ++ encodedMerkleRoot)

@[csimp] theorem chunkHash_csimp : @chunkHash = @chunkHashF := rfl

def merklizeBorshF (items : List Bytes) : Bytes := merkleRoot (items.map sha256)

@[csimp] theorem merklizeBorsh_csimp : @merklizeBorsh = @merklizeBorshF := rfl

def slotLeafF (s : ChunkSlot) (ci : ChunkInner) : Bytes :=
  chunkHash s.inner ci.encodedMerkleRoot ++ u64 s.heightIncluded

@[csimp] theorem slotLeaf_csimp : @slotLeaf = @slotLeafF := rfl

def outgoingReceiptsRootF (l : Layout) (rs : List Receipt) : Bytes :=
  merklizeBorsh (l.shardIds.map fun s =>
    sha256 (u64 s ++ encodeReceipts (rs.filter fun r => l.shardOf r.receiverId == s)))

@[csimp] theorem outgoingReceiptsRoot_csimp : @outgoingReceiptsRoot = @outgoingReceiptsRootF := rfl

def decodeBlkF (r : BlockRec) : Except String Blk := do
  let hdr ← decodeBlockV6 r.headerVersion r.prevHash r.innerLite r.innerRest
  let slots ← r.slots.mapM fun s => do
    let ci ← decodeChunkInner s.inner
    pure (s, ci)
  check (merklizeBorsh (slots.map fun (s, ci) => slotLeaf s ci) == hdr.chunkHeadersRoot)
    "invalid: chunk slots do not match chunk_headers_root"
  pure ⟨r, hdr, slots⟩

@[csimp] theorem decodeBlk_csimp : @decodeBlk = @decodeBlkF := rfl

end ZkFormal.V3.Fast
