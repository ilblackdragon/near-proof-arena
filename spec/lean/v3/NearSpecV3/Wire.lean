import NearSpec.Primitives
import NearSpec.AccountId

/-!
# nearcore borsh decoders used by `near/pv86/chunk-validation/v0`

Strict decoders (truncation, unknown tags, invalid account ids, out-of-range
enum values all fail) for the nearcore types that appear in a
`ChunkStateWitness` and in the chain context of `claim.bin`. Each decoder
accepts exactly the byte strings nearcore's `BorshDeserialize` accepts **for the
shapes the D0 domain admits**; shapes outside D0 are rejected with an
`out of domain` error (spec/near-chunk-validation-v0.md §6). Citations:
docs/research/chunk-validation-boundary.md §2 (layouts) and the nearcore source
lines given per decoder.

Parsers are `Bytes → Except String (α × Bytes)` (`P α`); every combinator is
structurally recursive (kernel-reducible).
-/

namespace NearSpecV3

open NearSpec

abbrev P (α : Type) := Bytes → Except String (α × Bytes)

def lift {α} (what : String) (p : Parser α) : P α := fun bs =>
  match p bs with
  | some r => .ok r
  | none => .error s!"decode: truncated {what}"

/-! Tail-recursive byte-list helpers: the kernel evaluates them iteratively, so
`decide +kernel` works on multi-kilobyte witnesses (the structurally recursive
`List.length` / `NearSpec.takeN` nest one kernel frame per byte). -/

def revAppend : List UInt8 → List UInt8 → List UInt8
  | [], acc => acc
  | b :: bs, acc => revAppend bs (b :: acc)

def takeAcc : Nat → List UInt8 → List UInt8 → Option (List UInt8 × List UInt8)
  | 0, acc, rest => some (revAppend acc [], rest)
  | _ + 1, _, [] => none
  | n + 1, acc, b :: bs => takeAcc n (b :: acc) bs

/-- `takeN` (same result, tail-recursive). -/
def takeT (n : Nat) : Parser Bytes := fun bs => takeAcc n [] bs

def lenAcc : List UInt8 → Nat → Nat
  | [], n => n
  | _ :: bs, n => lenAcc bs (n + 1)

/-- `List.length` (same result, tail-recursive). -/
def lenT (b : List UInt8) : Nat := lenAcc b 0

def readBytesT : Parser Bytes := fun bs =>
  match readU32 bs with
  | none => none
  | some (n, rest) => takeT n rest

def pU8 (w : String) : P Nat := lift w readU8
def pU16 (w : String) : P Nat := lift w readU16
def pU32 (w : String) : P Nat := lift w readU32
def pU64 (w : String) : P Nat := lift w readU64
def pU128 (w : String) : P Nat := lift w readU128
def pHash (w : String) : P Bytes := lift w readHash
def pBytes (w : String) : P Bytes := lift w readBytesT
def pTake (n : Nat) (w : String) : P Bytes := lift w (takeT n)

def pMany {α} (p : P α) : Nat → P (List α)
  | 0, bs => .ok ([], bs)
  | n + 1, bs => do
    let (a, bs) ← p bs
    let (as, bs) ← pMany p n bs
    pure (a :: as, bs)

def pVec {α} (w : String) (p : P α) : P (List α) := fun bs => do
  let (n, bs) ← pU32 (w ++ " length") bs
  pMany p n bs

def pOption {α} (w : String) (p : P α) : P (Option α) := fun bs => do
  let (t, bs) ← pU8 (w ++ " option tag") bs
  match t with
  | 0 => pure (none, bs)
  | 1 => do let (a, bs) ← p bs; pure (some a, bs)
  | _ => throw s!"decode: invalid option tag for {w}"

def pBool (w : String) : P Bool := fun bs => do
  let (t, bs) ← pU8 w bs
  match t with
  | 0 => pure (false, bs)
  | 1 => pure (true, bs)
  | _ => throw s!"decode: invalid bool {w}"

/-- Bytes consumed by a parser (to keep the exact encoding of a sub-value). -/
def consumed (before after : Bytes) : Bytes :=
  match takeT (lenT before - lenT after) before with
  | some (h, _) => h
  | none => []

/-- `AccountId`: borsh string + `validate` (near-account-id-2.0.0 `src/borsh.rs:9-30`). -/
def pAccountId (w : String) : P Bytes := fun bs => do
  let (a, bs) ← pBytes w bs
  if AccountId.valid a then pure (a, bs) else throw s!"decode: invalid account id ({w})"

/-- `PublicKey` (`core/crypto/src/signature.rs:371-411`): 0 ED25519 (32), 1 SECP256K1 (64),
2 MLDSA65 (1952); other tags fail. -/
def pPublicKey (w : String) : P PublicKey := fun bs => do
  let (t, bs) ← pU8 (w ++ " key type") bs
  let n ← match t with
    | 0 => pure 32 | 1 => pure 64 | 2 => pure 1952
    | _ => throw s!"decode: unknown PublicKey tag ({w})"
  let (d, bs) ← pTake n w bs
  pure (⟨t, d⟩, bs)

/-- `Signature` (`signature.rs:1168-1196`): ED25519 64 bytes with `sig[63] & 0xE0 = 0`,
SECP256K1 65 bytes, MLDSA65 3309 bytes. Returns the raw encoding. -/
def pSignature (w : String) : P Bytes := fun bs => do
  let (t, rest) ← pU8 (w ++ " signature type") bs
  match t with
  | 0 => do
    let (d, rest) ← pTake 64 w rest
    if (d.getD 63 0).toNat / 32 != 0 then throw s!"decode: ed25519 signature high bits ({w})"
    pure (consumed bs rest, rest)
  | 1 => do let (_, rest) ← pTake 65 w rest; pure (consumed bs rest, rest)
  | 2 => do let (_, rest) ← pTake 3309 w rest; pure (consumed bs rest, rest)
  | _ => throw s!"decode: unknown signature tag ({w})"

/-! ## Receipts (D0 shape) -/

/-- nearcore borsh `Receipt` restricted to the D0 shape (`ReceiptV0` untagged,
`core/primitives/src/receipt.rs:221-233`; `ReceiptEnum::Action = 0`, `ActionReceipt`
with no output data receivers, no input data ids, exactly one `Transfer` action).
`system` is allowed as predecessor (refund receipts). Any other shape:
`out of domain` (r.shape). -/
def pReceipt : P Receipt := fun bs => do
  let (pred, bs) ← pAccountId "predecessor_id" bs
  let (recv, bs) ← pAccountId "receiver_id" bs
  let (rid, bs) ← pHash "receipt_id" bs
  let (tag, bs) ← pU8 "ReceiptEnum tag" bs
  if tag != 0 then throw "out of domain (r.shape): ReceiptEnum is not Action(0)"
  let (signer, bs) ← pAccountId "signer_id" bs
  let (pk, bs) ← pPublicKey "signer_public_key" bs
  if pk.tag == 2 then throw "out of domain (r.shape): ML-DSA signer key"
  let (gp, bs) ← pU128 "gas_price" bs
  let (nout, bs) ← pU32 "output_data_receivers" bs
  if nout != 0 then throw "out of domain (r.shape): output_data_receivers"
  let (nin, bs) ← pU32 "input_data_ids" bs
  if nin != 0 then throw "out of domain (r.shape): input_data_ids"
  let (nact, bs) ← pU32 "actions" bs
  if nact != 1 then throw "out of domain (r.shape): not exactly one action"
  let (atag, bs) ← pU8 "action tag" bs
  if atag != 3 then throw "out of domain (r.shape): action is not Transfer(3)"
  let (dep, bs) ← pU128 "deposit" bs
  if !AccountId.isNamed recv then throw "out of domain (r.shape): receiver is not a named account"
  pure ({ predecessorId := pred, receiverId := recv, receiptId := rid, signerId := signer,
          signerPk := pk, gasPrice := gp, deposit := dep }, bs)

/-! ## Chunk header inner (V4 / V5), `shard_chunk_header_inner.rs:365-427` -/

structure Congestion where
  delayedGas : Nat
  bufferedGas : Nat
  receiptBytes : Nat
  allowedShard : Nat
  deriving DecidableEq, Repr

structure BwRequest where
  toShard : Nat
  bitmap : Bytes   -- 5 bytes, bit i = byte i/8 bit i%8 (Lsb0)
  deriving DecidableEq, Repr

structure ChunkInner where
  tag : Nat                       -- 3 = V4, 4 = V5
  prevBlockHash : Bytes
  prevStateRoot : Bytes
  prevOutcomeRoot : Bytes
  encodedMerkleRoot : Bytes
  encodedLength : Nat
  heightCreated : Nat
  shardId : Nat
  prevGasUsed : Nat
  gasLimit : Nat
  prevBalanceBurnt : Nat
  prevOutgoingReceiptsRoot : Bytes
  txRoot : Bytes
  proposals : List Bytes          -- raw `ValidatorStake` encodings
  congestion : Congestion
  bwRequests : List BwRequest
  proposedSplit : Option Bytes    -- raw `TrieSplit` (V5 only)
  deriving Repr

/-- `ValidatorStake::V1 = 0 ‖ AccountId ‖ PublicKey ‖ u128` (`types.rs:589-601, 787-798`). -/
def pValidatorStake : P Bytes := fun bs => do
  let (t, rest) ← pU8 "ValidatorStake tag" bs
  if t != 0 then throw "decode: ValidatorStake tag"
  let (_, rest) ← pAccountId "stake account" rest
  let (_, rest) ← pPublicKey "stake key" rest
  let (_, rest) ← pU128 "stake" rest
  pure (consumed bs rest, rest)

def pCongestion : P Congestion := fun bs => do
  let (t, bs) ← pU8 "CongestionInfo tag" bs
  if t != 0 then throw "decode: CongestionInfo tag"
  let (d, bs) ← pU128 "delayed_receipts_gas" bs
  let (b, bs) ← pU128 "buffered_receipts_gas" bs
  let (r, bs) ← pU64 "receipt_bytes" bs
  let (a, bs) ← pU16 "allowed_shard" bs
  pure (⟨d, b, r, a⟩, bs)

def pBwRequest : P BwRequest := fun bs => do
  let (s, bs) ← pU16 "to_shard" bs
  let (m, bs) ← pTake 5 "bitmap" bs
  pure (⟨s, m⟩, bs)

def pBwRequests : P (List BwRequest) := fun bs => do
  let (t, bs) ← pU8 "BandwidthRequests tag" bs
  if t != 0 then throw "decode: BandwidthRequests tag"
  pVec "requests" pBwRequest bs

/-- `TrieSplit { boundary_account, left_memory: u64, right_memory: u64 }` (`trie_split.rs:20-27`). -/
def pTrieSplit : P Bytes := fun bs => do
  let (_, rest) ← pAccountId "boundary_account" bs
  let (_, rest) ← pU64 "left_memory" rest
  let (_, rest) ← pU64 "right_memory" rest
  pure (consumed bs rest, rest)

/-- Tagged `ShardChunkHeaderInner`, V4 or V5 only (`validate_version` at PV 86,
`sharding.rs:606-632`); other tags: error. -/
def pChunkInner : P ChunkInner := fun bs => do
  let (tag, bs) ← pU8 "ShardChunkHeaderInner tag" bs
  if tag != 3 && tag != 4 then throw "invalid: chunk header inner version not V4/V5"
  let (pbh, bs) ← pHash "prev_block_hash" bs
  let (psr, bs) ← pHash "prev_state_root" bs
  let (por, bs) ← pHash "prev_outcome_root" bs
  let (emr, bs) ← pHash "encoded_merkle_root" bs
  let (el, bs) ← pU64 "encoded_length" bs
  let (hc, bs) ← pU64 "height_created" bs
  let (sid, bs) ← pU64 "shard_id" bs
  let (pgu, bs) ← pU64 "prev_gas_used" bs
  let (gl, bs) ← pU64 "gas_limit" bs
  let (pbb, bs) ← pU128 "prev_balance_burnt" bs
  let (porr, bs) ← pHash "prev_outgoing_receipts_root" bs
  let (txr, bs) ← pHash "tx_root" bs
  let (props, bs) ← pVec "prev_validator_proposals" pValidatorStake bs
  let (ci, bs) ← pCongestion bs
  let (bw, bs) ← pBwRequests bs
  let (split, bs) ← if tag == 4 then pOption "proposed_split" pTrieSplit bs else pure (none, bs)
  pure ({ tag, prevBlockHash := pbh, prevStateRoot := psr, prevOutcomeRoot := por,
          encodedMerkleRoot := emr, encodedLength := el, heightCreated := hc, shardId := sid,
          prevGasUsed := pgu, gasLimit := gl, prevBalanceBurnt := pbb,
          prevOutgoingReceiptsRoot := porr, txRoot := txr, proposals := props,
          congestion := ci, bwRequests := bw, proposedSplit := split }, bs)

/-- Decode a complete tagged inner (no trailing bytes). -/
def decodeChunkInner (b : Bytes) : Except String ChunkInner := do
  let (ci, rest) ← pChunkInner b
  if !rest.isEmpty then throw "decode: trailing bytes after chunk inner"
  pure ci

/-- `chunk_hash = sha256(sha256(borsh(inner)) ‖ encoded_merkle_root)` (`sharding.rs:291-296`). -/
def chunkHash (innerBytes encodedMerkleRoot : Bytes) : Bytes :=
  sha256 (sha256 innerBytes ++ encodedMerkleRoot)

/-! ## Block header V6 (`block_header.rs:30-47, 308-354, 647-664, 781-791`) -/

structure BlockHdr where
  version : Nat
  prevHash : Bytes
  height : Nat
  epochId : Bytes
  nextEpochId : Bytes
  timestamp : Nat
  randomValue : Bytes
  chunkHeadersRoot : Bytes
  nextGasPrice : Nat
  hash : Bytes
  deriving Repr

/-- `SHA256(SHA256(SHA256(lite) ‖ SHA256(rest)) ‖ prev_hash)`. -/
def blockHash (prevHash lite rest : Bytes) : Bytes :=
  sha256 (sha256 (sha256 lite ++ sha256 rest) ++ prevHash)

def pApproval : P Unit := fun bs => do
  let (_, bs) ← pOption "approval" (pSignature "approval") bs
  pure ((), bs)

/-- Decode a V6 header from its hashed parts. -/
def decodeBlockV6 (version : Nat) (prevHash lite rest : Bytes) : Except String BlockHdr := do
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

end NearSpecV3
