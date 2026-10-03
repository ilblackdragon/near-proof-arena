import NearSpec.Codec
import NearSpec.ClaimCodecV2

/-!
# v2 decoders and reference claim derivation (NOT part of the trusted relation)

Strict decoders for `request.bin` / `witness.bin` of `near/pv86/receipt-transfer-batch/v1`
(`spec/claim-v2.md`), the partial-trie builder (v1's `Codec.build`, asked to
reveal the receivers' Account paths AND the path to `0x0f`), and `deriveClaim`,
used by `nearspec-check --scope v2`. The checker re-validates every result with
`decide (TransferV2.NearRelation c w)`, so a bug here can only cause a rejection.
-/

namespace NearSpec.CodecV2

open NearSpec NearSpec.TransferV2 NearSpec.Codec

/-- `"near-arena-request-v2"` -/
def requestFormat : Bytes :=
  [110, 101, 97, 114, 45, 97, 114, 101, 110, 97, 45, 114, 101, 113, 117, 101, 115, 116, 45, 118, 50]
/-- `"near-arena-witness-v2"` -/
def witnessFormat : Bytes :=
  [110, 101, 97, 114, 45, 97, 114, 101, 110, 97, 45, 119, 105, 116, 110, 101, 115, 115, 45, 118, 50]

structure Request where
  protocolVersion : Nat
  chainId : Bytes
  shardId : Nat
  blockHeight : Nat
  blockGasPrice : Nat
  gasLimit : Nat
  delayedReceiptsGas : Nat
  bufferedReceiptsGas : Nat
  receiptBytes : Nat
  allowedShard : Nat
  missedChunksCount : Nat
  preStateRoot : Bytes
  receipts : List Receipt

def decodeRequest (bs : Bytes) : Except String Request := do
  let ((), bs) ← pTag requestFormat "request format" bs
  let ((), bs) ← pTag TransferV2.statementId "statement id" bs
  let (pv, bs) ← lift "protocol_version" readU32 bs
  let (chain, bs) ← lift "chain_id" readBorshBytes bs
  if !chainIdOk chain then throw "bad chain_id"
  let (shard, bs) ← lift "shard_id" readU64 bs
  let (h, bs) ← lift "block_height" readU64 bs
  let (gp, bs) ← lift "block_gas_price" readU128 bs
  let (gl, bs) ← lift "gas_limit" readU64 bs
  let (dg, bs) ← lift "delayed_receipts_gas" readU128 bs
  let (bg, bs) ← lift "buffered_receipts_gas" readU128 bs
  let (rb, bs) ← lift "receipt_bytes" readU64 bs
  let (als, bs) ← lift "allowed_shard" readU16 bs
  let (mc, bs) ← lift "missed_chunks_count" readU64 bs
  let (root, bs) ← lift "pre_state_root" readHash bs
  let (n, bs) ← lift "receipt count" readU32 bs
  let (rs, bs) ← pMany pReceipt n bs
  if !bs.isEmpty then throw "trailing bytes"
  pure ⟨pv, chain, shard, h, gp, gl, dg, bg, rb, als, mc, root, rs⟩

def decodeWitness (bs : Bytes) : Except String (Bytes × List Bytes) := do
  let ((), bs) ← pTag witnessFormat "witness format" bs
  let (root, bs) ← lift "pre_state_root" readHash bs
  let (tag, bs) ← lift "PartialState tag" readU8 bs
  if tag != 0 then throw "PartialState tag != TrieValues(0)"
  let (n, bs) ← lift "value count" readU32 bs
  let (vs, bs) ← pMany (lift "value" readBorshBytes) n bs
  if !bs.isEmpty then throw "trailing bytes"
  if !sortedStrict vs then throw "witness values not strictly ascending"
  pure (root, vs)

def buildWitness (req : Request) (values : List Bytes) : TransferV2.Witness :=
  let store : Store := values.foldl (fun m v => m.insert (sha256 v) v) {}
  let keys := bwKeyPath :: req.receipts.map (fun r => accountKeyPath r.receiverId)
  ⟨req.receipts, build store req.preStateRoot keys⟩

def deriveClaim (req : Request) (w : TransferV2.Witness) : Except String TransferV2.Claim := do
  let hdr : TransferV2.Claim :=
    { protocolVersion := req.protocolVersion, chainId := req.chainId, shardId := req.shardId,
      blockHeight := req.blockHeight, blockGasPrice := req.blockGasPrice, gasLimit := req.gasLimit,
      delayedReceiptsGas := req.delayedReceiptsGas, bufferedReceiptsGas := req.bufferedReceiptsGas,
      receiptBytes := req.receiptBytes, allowedShard := req.allowedShard,
      missedChunksCount := req.missedChunksCount,
      preStateRoot := req.preStateRoot, receiptCount := req.receipts.length,
      receiptsCommitment := receiptsCommitment req.shardId req.receipts,
      postStateRoot := zeroHash, outcomeRoot := zeroHash, refundCount := 0,
      refundsCommitment := zeroHash, gasBurntTotal := 0, tokensBurntTotal := 0 }
  if hdr.protocolVersion != Params.protocolVersion then throw "out of domain: protocol_version"
  if hdr.chainId != Params.chainId then throw "out of domain: chain_id"
  let n := req.receipts.length
  if n < 1 || n > Params.maxBatch then throw "out of domain: batch size"
  if !((n - 1) * Params.G < req.gasLimit) then throw "out of domain: gas limit"
  if !(req.receipts.all Receipt.inSlice) then throw "out of domain: receipt fields (ids/key/named receiver/system)"
  if !(decide (req.receipts.map Receipt.receiptId).Nodup) then throw "out of domain: duplicate receipt id"
  if !(req.shardId < maxShardIdExcl) then throw "out of domain: shard_id >= 2^32"
  if req.delayedReceiptsGas != 0 || req.bufferedReceiptsGas != 0 || req.receiptBytes != 0 then
    throw "out of domain: congestion info not zero"
  if w.trie.hashOf != req.preStateRoot then throw "witness does not hash to pre_state_root"
  if !w.trie.wf then throw "witness trie not well-formed"
  if w.trie.revealedBytes > Params.maxWitnessBytes then throw "out of domain: witness too large"
  let ctx := hdr.ctx
  match w.trie.find bwKeyPath with
  | none => throw "witness does not determine the bandwidth-scheduler key 0x0f"
  | some (some b) =>
    if (Bandwidth.State.decode b).isNone then
      throw "out of domain: bandwidth scheduler state does not decode"
  | some none => pure ()
  match bandwidthStep ctx w.trie with
  | none => throw "witness path to 0x0f insufficient for the update"
  | some t =>
  match TransferV1.runBatch ⟨ctx.blockHeight, ctx.blockGasPrice⟩ t w.receipts with
  | none =>
    let i := (firstFailing ⟨ctx.blockHeight, ctx.blockGasPrice⟩ 0 ⟨t, [], [], 0, 0⟩ w.receipts).getD 0
    throw s!"out of domain: receipt {i} (missing/unrevealed receiver, not AccountV1, overflow, or storage stake)"
  | some _ =>
  match runChunk ctx w with
  | none => throw "out of domain: gas refund while link (S,S) is not allowed (missed chunk)"
  | some acc =>
    let o := Outputs.ofAcc acc
    pure { hdr with postStateRoot := o.postStateRoot, outcomeRoot := o.outcomeRoot,
                    refundCount := o.refundCount, refundsCommitment := o.refundsCommitment,
                    gasBurntTotal := o.gasBurntTotal, tokensBurntTotal := o.tokensBurntTotal }

end NearSpec.CodecV2
