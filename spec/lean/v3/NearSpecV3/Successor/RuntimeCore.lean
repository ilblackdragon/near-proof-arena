import NearSpecV3.Successor.StorageExecution
import NearSpecV3.Successor.WitnessCodec
import NearSpecV3.Successor.ZstdFrame
import NearSpecV3.GenesisD3
import NearSpecV3.Resharding

/-! Parameterized validation shell. The legacy driver reduces definitionally to the original
checkers (proved below); the recorder driver changes only main execution and its size guard. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2

/-- An implicit transition's kind, as `ImplicitTransitionParams` distinguishes it
(`chunk_validation.rs:103-110`). -/
inductive ImplicitKind where
  /-- `ImplicitTransitionParams::ApplyOldChunk`: apply the block's transactions/receipts. -/
  | applyOldChunk
  /-- `ImplicitTransitionParams::Resharding`: split the parent trie at a boundary account and keep
  one child's half. The payload is the validator's `(boundary_account, retain_mode)`. -/
  | resharding (boundaryAccount : Bytes) (mode : RetainMode)
  deriving DecidableEq, Repr

/-- How an implicit transition is applied. The signed and D2 drivers have exactly one kind —
`applyOldChunk` — so their split handling is definitionally absent. A resharding-enabled driver adds
the `resharding` kind. -/
def implicitKindOf (l : Layout) (shardId : Nat) (numNewChunksSeen : Nat) :
    Except String ImplicitKind := do
  match ← reshardingTransitionOf l shardId numNewChunksSeen with
  | some (bd, mode) => pure (.resharding bd mode)
  | none => pure .applyOldChunk

/-- Historical constant from the superseded `w.compressed_size` approximation: the largest borsh
witness whose zstd encoding certainly stayed within `MAX_COMPRESSED_STATE_WITNESS_SIZE` = 48 MiB.
The 48 MiB cap is now enforced exactly on the distributed compressed bytes by `decodeWitnessFileV`
(the `near-arena-cwitness-v3` format), so this is no longer part of any relation; it is retained only
for `TierProofs.witnessBound_le`. -/
def compressedSafeWitnessBytes : Nat := 50000000

theorem compressedSafeWitnessBytes_ok :
    compressedSafeWitnessBytes + compressedSafeWitnessBytes / 256 + 65536 < 50331648 := by decide

/-- `MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE` = 64 MiB
(`core/primitives/src/stateless_validation/contract_distribution.rs:371`). -/
def maxContractCodeResponseBytes : Nat := 67108864

/-- The borsh size of the `Vec<CodeBytes>` a `ContractCodeResponse` carries: a 4-byte vector length
prefix and, per code, a 4-byte length prefix and the bytes. The `codes` of `witness.bin` are exactly
those the cold validator must fetch. -/
def codeResponseBytes (codes : List Bytes) : Nat :=
  codes.foldl (fun acc c => acc + 4 + lenT c) 4

/-- `MAX_COMPRESSED_STATE_WITNESS_SIZE` = 48 MiB (`partial_witness.rs:18`), the cap on a distributed
`EncodedChunkStateWitness`'s `encoded_length` (`validate.rs:82-88`). -/
def maxCompressedWitnessBytes : Nat := 50331648

/-- `"near-arena-cwitness-v3"`: the versioned `witness.bin` tag whose state-witness field carries the
distributed zstd `EncodedChunkStateWitness` bytes rather than the decoded witness. Spelled as an
explicit byte list (not `String.toUTF8`) so it is kernel-reducible on the `decide +kernel` path. -/
def witnessTagC : Bytes :=
  [110, 101, 97, 114, 45, 97, 114, 101, 110, 97, 45, 99, 119, 105, 116, 110, 101, 115, 115, 45, 118, 51]

/-- Versioned `witness.bin` decoder. The original `near-arena-witness-v3` format (state witness in the
clear) decodes exactly as `decodeWitnessFile`. The `near-arena-cwitness-v3` format carries the
compressed `EncodedChunkStateWitness`: its `encoded_length` must be `≤ MAX_COMPRESSED_STATE_WITNESS_SIZE`
(nearcore rejects otherwise, `validate.rs:82-88`), then it is zstd-decoded under the 64 MiB
`CountingRead` cut-off (`Zstd.decompressBytesCapped`) exactly as `CompressedData::decode` does; the
resulting borsh state witness feeds the same pipeline. -/
def decodeWitnessFileV (bs : Bytes) : Except String (Bytes × List Bytes) :=
  -- The tag is a borsh byte string: 4-byte LE length then the bytes. The `c`-format tag is 22 bytes
  -- (`[22,0,0,0]` prefix), distinct from the 21-byte original, so the prefix disambiguates.
  if bs.take (witnessTagC.length + 4) == ([22, 0, 0, 0] ++ witnessTagC) then
    (do
      let ((), bs) ← dTag witnessTagC "compressed witness format" bs
      let (enc, bs) ← pBytes "encoded_state_witness" bs
      let (codes, bs) ← pVec "contract_code" (pBytes "code") bs
      if !bs.isEmpty then throw "decode: trailing bytes in witness.bin"
      if lenT enc > maxCompressedWitnessBytes then
        throw "invalid: encoded_length exceeds MAX_COMPRESSED_STATE_WITNESS_SIZE"
      let sw ← Zstd.decompressBytesCapped enc
      pure (sw, codes))
  else
    decodeWitnessFile bs

structure ExecutionDriver where
  apply : ActionHooks → Prims → Env → PTrie → Option ValidatorUpdateFacts →
    List (Bytes × Nat) → List Rcpt → List (TxD2 × Bool) → Congestion → Except String MainOutD2
  sizeOk : Nat → Nat → Bool
  decodeWitness : Bytes → Except String StateWitnessD2 := decodeStateWitnessD2
  receiptShard : Layout → Rcpt → Nat := fun l r => l.shardOf r.recv
  validateRouting : Layout → List Rcpt → Except String Unit := fun _ _ => pure ()
  outgoingRoot : Layout → List Rcpt → Bytes := outgoingReceiptsRootD2
  /-- Decide resharding implicit transitions instead of excluding a claim whose epochs differ in
  shard layout or whose facts carry a split gate. `false` is the signed and D2 behaviour: both
  guards stay in force and no implicit transition can be a resharding. -/
  resharding : Bool := false
  /-- Lift the `c.blocks.length ≤ 32` chain-segment bound. That bound is inherited from the D0 design
  to keep the AIR's public-segment and table heights small — a prover-capacity restriction, not a
  protocol condition (Gate B forbids such bounds in an accepted configuration). The pipeline already
  walks an arbitrary `c.blocks` list, so lifting it adds no semantics. `false` keeps the signed and
  D2 behaviour exactly. -/
  segmentUnbounded : Bool := false
  /-- Lift the `|state_witness| ≤ 8 MiB` bound (`out of domain (w.size)`). That bound is the D0
  design's witness-capacity choice, not a nearcore condition: the pinned validator decodes a
  `ChunkStateWitness` of up to `MAX_UNCOMPRESSED_STATE_WITNESS_SIZE` = 64 MiB
  (`core/primitives/src/stateless_validation/state_witness.rs:19-20`, enforced by
  `CompressedData::decode`, `core/primitives/src/utils/compression.rs:44-47`), and that bound is
  kept exactly by the witness decoder (`decodeStateWitnessWith`, `lenT bs > MAX_WITNESS` ⇒ reject).
  `false` keeps the signed and D2 behaviour exactly. -/
  witnessUnbounded : Bool := false
  /-- Lift the `numShards ≤ 64` half of `c.layout`. nearcore's validator has no shard-count limit
  (the pinned mainnet epoch config bounds dynamic resharding at `max_number_of_shards = 10`,
  `core/primitives/res/epoch_configs/mainnet/85.json:26`); the 64 is the D0 design's routing-table
  size. `1 ≤ numShards` stays. `false` keeps the signed and D2 behaviour exactly. -/
  layoutUnbounded : Bool := false
  /-- Exclude (out of domain) a chunk whose cold-fetched contract code cannot be delivered within
  nearcore's one `ContractCodeResponse`. A cold validator requests the chunk's accessed pre-state
  contract codes (`record_contract_call`, `runtime/runtime/src/function_call.rs:355-392`: a call is
  recorded only when the code is present in the pre-state with that hash) that are missing from its
  compiled cache — for a cold validator, all of them — and the producer answers with a single
  `ContractCodeResponse` carrying `Vec<CodeBytes>`, decoded under
  `MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE` = 64 MiB on the borsh-serialized vector
  (`core/primitives/src/stateless_validation/contract_distribution.rs:371-399`). The fetched codes
  are exactly the `codes` appended to `witness.bin` (the oracle's cold judge appends the response
  contents, `partial_witness_tracker.rs:693-696`). When their borsh size
  `4 + Σ (4 + |code|)` exceeds 64 MiB the response cannot be decoded, so the verdict depends on the
  validator's compiled-contract cache rather than the witness; this is excluded with
  `w.code_response_size`. `false` keeps the signed and D2 behaviour exactly (no such guard). -/
  codeResponseCap : Bool := false
  /-- Decode `witness.bin` with the versioned dispatcher `decodeWitnessFileV`, which accepts both the
  original `near-arena-witness-v3` format (the state witness in the clear) and the
  `near-arena-cwitness-v3` format carrying the distributed `EncodedChunkStateWitness` zstd bytes
  (rejects `encoded_length > MAX_COMPRESSED_STATE_WITNESS_SIZE` = 50,331,648, then zstd-decodes under
  the 64 MiB cut-off). `false` keeps the signed and D2 behaviour exactly (`decodeWitnessFile`). -/
  compressedWitness : Bool := false
  /-- Blind replay: skip every comparison against a value the transition *produces* — the main and
  implicit `post_state_root`s and the endorsed header's output fields (state/outcome/outgoing-receipt
  roots, gas used, balance burnt, proposals, congestion, bandwidth requests, encoded merkle root and
  length). The checker still computes them and returns them in its `Observable`, so a harness can
  supply inputs with those fields zeroed and compare the emitted values against the chain. `false`
  is every accepting configuration: the guards are `false || x`, which reduces to `x`. -/
  blindOutputs : Bool := false
  /-- How each implicit transition is applied. The default is the signed behaviour: every implicit
  transition is an old-chunk application. A resharding-enabled driver consults the layout's split
  map instead. -/
  implicitKind : Layout → Nat → Nat → Except String ImplicitKind := fun _ _ _ => .ok .applyOldChunk
  /-- Apply a resharding implicit transition to a parent trie and return the child's new root. Only
  reached when `implicitKind` returns `.resharding`, so the signed path never calls it. -/
  splitApply : PTrie → Bytes → RetainMode → Except String Bytes :=
    fun _ _ _ => .error "unmodeled: resharding transition"

def legacyDriver : ExecutionDriver :=
  { apply := applyNewChunkD2, sizeOk := fun base removals => base + 2000 * removals ≤ 4000000 }

def recorderDriver (cfg : Wasm.NearCfg) (globals : Bool := false)
    (codePolicy : CodeWitnessPolicy := .coldPartial) : ExecutionDriver := {
  apply := fun _ p e t vu props incoming txs congestion =>
    StorageExecution.run cfg p e t vu props incoming txs congestion globals codePolicy,
  sizeOk := fun _ _ => true,
  codeResponseCap := true,
  compressedWitness := true,
  decodeWitness := if globals then
    decodeStateWitnessWith GlobalCodecs.pRcptGlobal GlobalCodecs.pTxD2Global
    else decodeStateWitnessD2,
  receiptShard := if globals then fun l r => r.routedShard l else fun l r => l.shardOf r.recv,
  validateRouting := if globals then fun l rs => do
    for r in rs do
      let _ ← StorageExecution.globalTarget l r
    else fun _ _ => pure (),
  outgoingRoot := if globals then fun l rs =>
    merklizeBorsh (l.shardIds.map fun shard =>
      sha256 (u64 shard ++ encodeRcpts (rs.filter fun r => r.routedShard l == shard)))
    else outgoingReceiptsRootD2 }

/-- The resharding tiers' driver: `recorderDriver` with `resharding := true`. A non-genesis segment is
checked by `ReshardCore.checkReshardCoreObs`, which walks the segment across layout boundaries and
places split transitions itself (`checkSuccessor` dispatches there). A segment reaching genesis still
goes through `checkD2CoreGWith`, whose prefix keeps `c.same_layout`, so no split can occur on that
path; `implicitKind` therefore stays the signed `applyOldChunk`. (It used to be `implicitKindOf`, which
decided a split from the witness layout's split map alone and the block *index*: every post-split
child witness with an old-chunk implicit transition was then mistaken for a split.) -/
def reshardingDriver (cfg : Wasm.NearCfg) (globals : Bool := false)
    (codePolicy : CodeWitnessPolicy := .coldPartial) : ExecutionDriver :=
  { recorderDriver cfg globals codePolicy with
    resharding := true
    splitApply := splitRootE }


def checkD2CoreWithObs (driver : ExecutionDriver) (hooks : ActionHooks) (allowCodes : Bool) (claimBytes witnessBytes : Bytes)
    (gasCap : Option Nat := none) : Except String Observable := do
  -- 3.1 decoding, actor checks
  let c ← (decodeClaimE claimBytes).mapError (fun e => s!"invalid claim: {e}")
  let (swBytes, codes) ←
    (if driver.compressedWitness then decodeWitnessFileV witnessBytes else decodeWitnessFile witnessBytes)
  if !allowCodes then check codes.isEmpty "out of domain (w.no_code): contract code"
  if driver.codeResponseCap then
    check (codeResponseBytes codes ≤ maxContractCodeResponseBytes)
      "out of domain (w.code_response_size): cold-fetched contract code exceeds MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE"
  if !driver.witnessUnbounded then
    check (lenT swBytes ≤ 8388608) "out of domain (w.size): witness larger than 8 MiB"
  let w ← driver.decodeWitness swBytes
  check (w.innerBytes == c.chunkInner) "invalid: witness chunk header differs from the claim"
  check (w.epochId == c.epochId) "invalid: epoch id"
  let H ← (decodeChunkInner c.chunkInner).mapError (fun e => s!"invalid claim: {e}")
  check (c.protocolVersion == 86) "out of domain (c.pv86)"
  -- 3.2 chain segment
  let blks ← c.blocks.mapM decodeBlk
  check (!blks.isEmpty) "invalid: empty chain segment"
  -- epoch table: exactly the referenced epochs, ascending; one layout; PV 86
  let referenced := dedupSorted (c.epochId :: blks.map (·.hdr.epochId))
  check (strictlyAscending (c.epochs.map (·.epochId)))
    "invalid: epoch table not strictly ascending"
  check (c.epochs.map (·.epochId) == referenced) "invalid: epoch table does not match the referenced epochs"
  let ep ← match c.epochs.find? (·.epochId == c.epochId) with
    | some e => pure e
    | none => throw "invalid: epoch_id not in the epoch table"
  check (ep.protocolVersion == c.protocolVersion)
    "invalid: epoch table does not match epoch_id / protocol_version"
  check (c.epochs.all (·.protocolVersion == 86)) "out of domain (c.pv86): epoch protocol version"
  -- The resharding guards are lifted when the driver decides resharding transitions. When it does
  -- not (the signed and D2 drivers), they remain exactly as they were: one shard layout and no split
  -- gate. When it does, the split's own semantics take over below (the implicit-transition loop
  -- applies the split and checks the child's post-state root), so a differing layout is no longer a
  -- reason to exclude the claim.
  if !driver.resharding then
    check (c.epochs.all (·.shardLayout == ep.shardLayout)) "out of domain (c.same_layout): resharding"
  let L ← decodeLayout ep.shardLayout
  if !driver.layoutUnbounded then
    check (1 ≤ L.numShards && L.numShards ≤ 64) "out of domain (c.layout)"
  else
    check (1 ≤ L.numShards) "out of domain (c.layout)"
  check (rsGenesisParamsOk c.rsDataParts c.rsTotalParts) "invalid: Reed-Solomon parameters"
  if !driver.segmentUnbounded then
    check (c.blocks.length ≤ 32) "out of domain (c.segment)"
  check (c.epochStartAfter.length == c.blocks.length) "invalid: epoch_start_after length"
  check (c.epochStartAfter.all (·.toNat ≤ 1)) "invalid: epoch_start_after flag"
  -- epoch_start_after vs headers (spec/claim-v3.md §2.2)
  let afterEpochs := c.epochId :: blks.map (·.hdr.epochId)
  check ((List.range blks.length).all fun i =>
      match blks[i]?, afterEpochs[i]?, c.epochStartAfter[i]? with
      | some b, some e, some f =>
        (if f.toNat == 1 then e == b.hdr.nextEpochId else e == b.hdr.epochId) &&
        (!b.isGenesis || f.toNat == 1)
      | _, _, _ => false)
    "invalid: epoch_start_after inconsistent with the headers"
  if !driver.resharding then
    check (c.applyFacts.all fun f => f.splitGate.isNone) "out of domain (c.no_split_gate)"
  -- step 6: check_valid_for_config on new_transactions (size gate; no signature check)
  check (w.newTxs.all TxD2.sizeOk) "invalid: new transaction exceeds max_transaction_size"
  let hashes := blks.map (·.hdr.hash)
  check (hashes.headD [] == H.prevBlockHash) "invalid: segment does not start at prev_block_hash"
  check ((blks.zip (hashes.drop 1)).all fun (b, h) => b.hdr.prevHash == h)
    "invalid: segment is not hash-linked"
  check (blks.all fun b => b.slots.length == L.numShards) "invalid: slot count"
  let idx ← match L.index H.shardId with
    | some i => pure i
    | none => throw "invalid: shard not in layout"
  let isNew := fun (b : Blk) => match b.slots[idx]? with
    | some (s, _) => s.heightIncluded == b.hdr.height
    | none => false
  check (blks.all fun b => b.slots.all fun (sl, _) => sl.heightIncluded ≤ b.hdr.height)
    "invalid: height_included above block height (block_congestion_info panics)"
  let b2i ← match blks.findIdx? isNew with
    | some i => pure i
    | none => throw "invalid: segment has no new chunk"
  let B2 ← match blks[b2i]? with | some b => pure b | none => throw "invalid: walk"
  check (!B2.isGenesis) "out of domain (c.not_genesis)"
  check c.genesisChunkExtra.isNone "invalid: genesis_chunk_extra for a non-genesis main block"
  let stop ← match (blks.drop (b2i + 1)).findIdx? isNew with
    | some j => pure (b2i + 1 + j)
    | none => throw "invalid: segment does not reach the last-but-one new chunk"
  check (stop + 1 == blks.length) "invalid: segment is not exactly the blocks the validator reads"
  let implicitIdx := (List.range b2i).reverse            -- oldest first
  let sourceBlks := (blks.drop b2i).take (stop - b2i)
  check (c.applyFacts.length == 1 + implicitIdx.length) "invalid: apply_facts length"
  -- validator_update present iff the applied block starts an epoch
  let appliedIdx := b2i :: implicitIdx
  check ((appliedIdx.zip c.applyFacts).all fun (i, f) =>
      f.validatorUpdate.isSome == (c.epochStartAfter.getD (i + 1) 0 == 1))
    "invalid: validator_update does not match the epoch start"
  let prevB2 ← match blks[b2i + 1]? with | some b => pure b | none => throw "invalid: walk"
  let slotB2 ← match B2.slots[idx]? with | some p => pure p.2 | none => throw "invalid: slot"
  -- 3.3 / 3.4 source receipts
  let mut receipts : List Rcpt := []
  let mut used : Nat := 0
  for S in sourceBlks do
    let mut proofs : List EntryD2 := []
    for (s, ci) in S.slots do
      if s.heightIncluded == S.hdr.height then
        let key := chunkHash s.inner ci.encodedMerkleRoot
        let e ← match lookupLastD2 key w.entries with
          | some e => pure e
          | none => throw "invalid: missing source receipt proof"
        driver.validateRouting L e.receipts
        check (e.proof.fromShard == ci.shardId) "invalid: receipt proof from_shard_id"
        check (e.proof.toShard == H.shardId) "invalid: receipt proof to_shard_id"
        check (verifyReceiptProofD2 ci.prevOutgoingReceiptsRoot e) "invalid: receipt proof merkle path"
        proofs := proofs ++ [e]
        used := used + 1
    let shuffled ← match shuffleWithSeed proofs S.hdr.prevHash with
      | some p => pure p
      | none => throw "invalid: shuffle fuel exhausted (probability < 2^-1024)"
    receipts := receipts ++
      (shuffled.map fun e => e.receipts.filter fun r => driver.receiptShard L r == H.shardId).flatten
  check ((distinctKeysD2 w.entries).length == used) "invalid: source_receipt_proofs contains extra proofs"
  check (sha256 (encodeRcpts receipts) == w.appliedReceiptsHash) "invalid: applied receipts hash"
  -- steps 8, 9: transactions of the last new chunk and their validity flags
  check (merklizeBorsh (w.txs.map TxD2.raw) == slotB2.txRoot) "invalid: transaction root of the last chunk"
  check (c.txValid.length == w.txs.length) "invalid: tx_valid length"
  -- 3.5 main transition
  let sched ← match Scheduler.Params.calculate Scheduler.Config.pv86 L.numShards with
    | some p => pure p
    | none => throw "invalid: bandwidth scheduler params (assert panics)"
  let facts0 := c.applyFacts.headD ⟨none, 0, none⟩
  let ctxB2 := blockCtx L H.shardId slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  -- E2: the recorded storage merged with the contract codes (`codes = []` unless `allowCodes`)
  let merged := w.main.values ++ codes
  let store := mkHStore merged
  let env : Env := { envOf c ctxB2 B2 facts0.minimumStake sched with
                     store := store, preRoot := slotB2.prevStateRoot }
  let tMain := revealAll store revealFuel slotB2.prevStateRoot
  check (tMain.hashOf == slotB2.prevStateRoot) "invalid: main base_state does not hash to prev_state_root"
  let lastProps := slotB2.proposals.filterMap decodeProposal
  let out ← driver.apply hooks prims env tMain facts0.validatorUpdate lastProps receipts
    (w.txs.zip (c.txValid.map (· != 0))) slotB2.congestion
  -- w.size: sums the merged list (conservative; spec/near-chunk-validation-d3.md §2.2)
  let baseBytes := (merged.map List.length).foldl (· + ·) 0
  check (driver.sizeOk baseBytes out.cdRemovals)
    "out of domain (w.size): storage-proof upper bound may exceed main_storage_proof_size_soft_limit"
  -- D3: per-chunk WASM gas cap (`G_α`, D3_WASM_REQUIREMENTS §1.1/§2.4); D2 passes `none`
  if let some cap := gasCap then
    check (out.wasmGas ≤ cap) s!"out of domain (e.g_alpha): chunk function-call gas {out.wasmGas} > G_α {cap}"
  let mut root := out.root
  check (driver.blindOutputs || root == w.main.postStateRoot) "invalid: main transition post state root"
  -- 3.6 implicit transitions
  check (w.implicit.length == implicitIdx.length) "invalid: implicit transitions count"
  let mainProps := out.proposals.map fun p => (p.acct, p.stake)
  -- Each implicit transition is either an old-chunk application (`ImplicitTransitionParams::
  -- ApplyOldChunk`) or, when the driver decides resharding, a split (`ImplicitTransitionParams::
  -- Resharding`). The validator derives the split from the *next* layout's split map and this
  -- shard's position in it (`get_resharding_transition`, `chunk_validation.rs:258-308`); the kind is
  -- therefore a property of the layout and the shard, not of the witness's transition list. The
  -- count and the post-state-root comparison are the same for both kinds, so a wrongly classified
  -- split fails the same `post_state_root` check an old-chunk mis-application does.
  for ((i, f), T) in (implicitIdx.zip (c.applyFacts.drop 1)).zip w.implicit do
    let M ← match blks[i]? with | some b => pure b | none => throw "invalid: walk"
    let ctxM := blockCtx L H.shardId slotB2.gasLimit M M.hdr.nextGasPrice
    let envM : Env := envOf c ctxM M f.minimumStake sched
    let tM := revealTrie T.values root
    match ← driver.implicitKind L H.shardId i with
    | .applyOldChunk =>
      root ← applyMissingChunkD2 prims envM tM f.validatorUpdate mainProps
    | .resharding bd mode =>
      -- The split's trie is the parent trie the witness reveals for this transition; the child's
      -- root is its retained half's hash. Congestion bookkeeping is checked by the header
      -- comparison below (`H.congestion`), which the split's finalization must match.
      root ← driver.splitApply tM bd mode
    check (driver.blindOutputs || root == T.postStateRoot) "invalid: implicit transition post state root"
  -- 3.7 comparison with the endorsed header
  check (driver.blindOutputs || H.prevStateRoot == root) "invalid: InvalidStateRoot"
  check (driver.blindOutputs || H.prevOutcomeRoot == outcomeRootD1 out.outcomes) "invalid: InvalidOutcomesProof"
  check (driver.blindOutputs || H.proposals == out.proposals.map Proposal.encode) "invalid: InvalidValidatorProposals"
  check (H.gasLimit == slotB2.gasLimit) "invalid: InvalidGasLimit"
  check (driver.blindOutputs || H.prevGasUsed == out.gasUsed) "invalid: InvalidGasUsed"
  check (driver.blindOutputs || H.prevBalanceBurnt == out.balanceBurnt) "invalid: InvalidBalanceBurnt"
  check (driver.blindOutputs || H.prevOutgoingReceiptsRoot == driver.outgoingRoot L out.outgoing) "invalid: InvalidReceiptsProof"
  check (driver.blindOutputs || H.congestion == out.congestion) "invalid: InvalidCongestionInfo"
  check (driver.blindOutputs || H.bwRequests == out.bwRequests) "invalid: InvalidBandwidthRequests"
  check H.proposedSplit.isNone "invalid: InvalidChunkHeaderShardSplit"
  check (H.txRoot == merklizeBorsh (w.newTxs.map TxD2.raw)) "invalid: InvalidTxRoot"
  let body := u32 w.newTxs.length ++ concatAll (w.newTxs.map TxD2.raw) ++ encodeRcpts out.outgoing
  match encodedMerkleRoot c.rsDataParts c.rsTotalParts body with
  | none => throw "invalid: Reed-Solomon parameters"
  | some (emr, len) =>
    check (driver.blindOutputs || H.encodedMerkleRoot == emr) "invalid: InvalidChunkEncodedMerkleRoot"
    check (driver.blindOutputs || H.encodedLength == len) "invalid: InvalidChunkEncodedLength"
    return { stateRoot := root
             outcomeRoot := outcomeRootD1 out.outcomes
             gasBurnt := out.gasUsed
             balanceBurnt := out.balanceBurnt
             outgoingReceiptsRoot := driver.outgoingRoot L out.outgoing
             proposals := out.proposals.map Proposal.encode
             txRoot := merklizeBorsh (w.newTxs.map TxD2.raw)
             encodedMerkleRoot := emr
             encodedLength := len
             congestion := out.congestion
             bwRequests := out.bwRequests
             logs := out.outcomes.map (fun o => o.logs) |>.flatten
             receiptCount := out.outgoing.length
             wasmGas := out.wasmGas
             outcomes := out.outcomes
             outgoing := out.outgoing
             stateChanges := out.committed
             computeUsage := out.compute
             detail := out.detail }

/-- The successor's whole-state checker: the observable checker projected to its verdict, the same
shape as `checkD2Core`, so `checkD2CoreWith_legacy` stays `rfl`. -/
def checkD2CoreWith (driver : ExecutionDriver) (hooks : ActionHooks) (allowCodes : Bool) (claimBytes witnessBytes : Bytes)
    (gasCap : Option Nat := none) : Except String Unit :=
  (checkD2CoreWithObs driver hooks allowCodes claimBytes witnessBytes gasCap).map fun _ => ()



def checkD2CoreGWith (driver : ExecutionDriver) (hooks : ActionHooks) (allowCodes : Bool) (claimBytes witnessBytes : Bytes)
    (gasCap : Option Nat := none) : Except String Unit := do
  -- 3.1 decoding, actor checks
  let c ← (decodeClaimE claimBytes).mapError (fun e => s!"invalid claim: {e}")
  let (swBytes, codes) ←
    (if driver.compressedWitness then decodeWitnessFileV witnessBytes else decodeWitnessFile witnessBytes)
  if !allowCodes then check codes.isEmpty "out of domain (w.no_code): contract code"
  if driver.codeResponseCap then
    check (codeResponseBytes codes ≤ maxContractCodeResponseBytes)
      "out of domain (w.code_response_size): cold-fetched contract code exceeds MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE"
  if !driver.witnessUnbounded then
    check (lenT swBytes ≤ 8388608) "out of domain (w.size): witness larger than 8 MiB"
  let w ← driver.decodeWitness swBytes
  check (w.innerBytes == c.chunkInner) "invalid: witness chunk header differs from the claim"
  check (w.epochId == c.epochId) "invalid: epoch id"
  let H ← (decodeChunkInner c.chunkInner).mapError (fun e => s!"invalid claim: {e}")
  check (c.protocolVersion == 86) "out of domain (c.pv86)"
  -- 3.2 chain segment
  let blks ← c.blocks.mapM decodeBlk
  check (!blks.isEmpty) "invalid: empty chain segment"
  let referenced := dedupSorted (c.epochId :: blks.map (·.hdr.epochId))
  check (strictlyAscending (c.epochs.map (·.epochId)))
    "invalid: epoch table not strictly ascending"
  check (c.epochs.map (·.epochId) == referenced) "invalid: epoch table does not match the referenced epochs"
  let ep ← match c.epochs.find? (·.epochId == c.epochId) with
    | some e => pure e
    | none => throw "invalid: epoch_id not in the epoch table"
  check (ep.protocolVersion == c.protocolVersion)
    "invalid: epoch table does not match epoch_id / protocol_version"
  check (c.epochs.all (·.protocolVersion == 86)) "out of domain (c.pv86): epoch protocol version"
  check (c.epochs.all (·.shardLayout == ep.shardLayout)) "out of domain (c.same_layout): resharding"
  let L ← decodeLayout ep.shardLayout
  if !driver.layoutUnbounded then
    check (1 ≤ L.numShards && L.numShards ≤ 64) "out of domain (c.layout)"
  else
    check (1 ≤ L.numShards) "out of domain (c.layout)"
  check (rsGenesisParamsOk c.rsDataParts c.rsTotalParts) "invalid: Reed-Solomon parameters"
  if !driver.segmentUnbounded then
    check (c.blocks.length ≤ 32) "out of domain (c.segment)"
  check (c.epochStartAfter.length == c.blocks.length) "invalid: epoch_start_after length"
  check (c.epochStartAfter.all (·.toNat ≤ 1)) "invalid: epoch_start_after flag"
  let afterEpochs := c.epochId :: blks.map (·.hdr.epochId)
  check ((List.range blks.length).all fun i =>
      match blks[i]?, afterEpochs[i]?, c.epochStartAfter[i]? with
      | some b, some e, some f =>
        (if f.toNat == 1 then e == b.hdr.nextEpochId else e == b.hdr.epochId) &&
        (!b.isGenesis || f.toNat == 1)
      | _, _, _ => false)
    "invalid: epoch_start_after inconsistent with the headers"
  check (c.applyFacts.all fun f => f.splitGate.isNone) "out of domain (c.no_split_gate)"
  check (w.newTxs.all TxD2.sizeOk) "invalid: new transaction exceeds max_transaction_size"
  let hashes := blks.map (·.hdr.hash)
  check (hashes.headD [] == H.prevBlockHash) "invalid: segment does not start at prev_block_hash"
  check ((blks.zip (hashes.drop 1)).all fun (b, h) => b.hdr.prevHash == h)
    "invalid: segment is not hash-linked"
  check (blks.all fun b => b.slots.length == L.numShards) "invalid: slot count"
  let idx ← match L.index H.shardId with
    | some i => pure i
    | none => throw "invalid: shard not in layout"
  let isNew := fun (b : Blk) => match b.slots[idx]? with
    | some (s, _) => s.heightIncluded == b.hdr.height
    | none => false
  check (blks.all fun b => b.slots.all fun (sl, _) => sl.heightIncluded ≤ b.hdr.height)
    "invalid: height_included above block height (block_congestion_info panics)"
  let b2i ← match blks.findIdx? isNew with
    | some i => pure i
    | none => throw "invalid: segment has no new chunk"
  let B2 ← match blks[b2i]? with | some b => pure b | none => throw "invalid: walk"
  -- **The non-genesis domain is delegated, not re-implemented.** For a non-genesis `B2` this
  -- function must decide *exactly* what `checkD2Core` decides — the genesis module's whole claim is
  -- that it extends the domain without touching the non-genesis relation. Rather than duplicating
  -- ~60 downstream checks (the first draft did, and silently dropped all ten endorsed-header
  -- comparisons, wrongly accepting 307 header mutants), we return `checkD2Core`'s own result. The
  -- prefix checks above are identical to `checkD2Core`'s and idempotent, so the delegate's outcome
  -- is the outcome this function would reach anyway; the re-decode is the price of the guarantee.
  if !B2.isGenesis then
    return (← checkD2CoreWith driver hooks allowCodes claimBytes witnessBytes gasCap)
  -- genesis branch (`chunk_validation.rs:403-413`): B2 genesis ⇒ the main transition is the stored
  -- genesis chunk extra, and `genesis_chunk_extra` must be present (claim-v3 T14).
  let gen? : Option ChunkExtra ← if B2.isGenesis then
      match c.genesisChunkExtra with
      | some g => match decodeChunkExtra g with
        | .ok ce => pure (some ce)
        | .error e => throw s!"invalid claim: genesis_chunk_extra: {e}"
      | none => throw "invalid: genesis_chunk_extra missing for a genesis main block"
    else
      match c.genesisChunkExtra with
      | some _ => throw "invalid: genesis_chunk_extra for a non-genesis main block"
      | none => pure none
  -- A genesis block is the first block of the chain: no block can be older than it in the segment
  -- (`blks[i].prevHash = hash(blks[i+1])`, so B2 genesis at `b2i` with a successor would require a
  -- SHA-256 output equal to zero).
  if B2.isGenesis then
    check (b2i + 1 == blks.length) "invalid: blocks older than the genesis block in the segment"
  let stop ← match (blks.drop (b2i + 1)).findIdx? isNew with
    | some j => pure (b2i + 1 + j)
    | none =>
      -- For a genesis B2 there is no last-but-one new chunk: the validator's walk stops at genesis
      -- (`chunk_validation.rs:225-227`), so B2 is the last block of the segment and the source
      -- blocks are exactly `[B2]`.
      if B2.isGenesis then pure b2i
      else throw "invalid: segment does not reach the last-but-one new chunk"
  check (stop + 1 == blks.length) "invalid: segment is not exactly the blocks the validator reads"
  let implicitIdx := (List.range b2i).reverse            -- oldest first
  let sourceBlks := (blks.drop b2i).take (stop - b2i)
  -- applied blocks: main block B2 first (non-genesis only), then implicit blocks
  -- (`pre_validate…` pushes B2 only when it is not genesis; `chunk_validation.rs:403-440`).
  let appliedIdx := (if B2.isGenesis then [] else [b2i]) ++ implicitIdx
  check (c.applyFacts.length == appliedIdx.length) "invalid: apply_facts length"
  check ((appliedIdx.zip c.applyFacts).all fun (i, f) =>
      f.validatorUpdate.isSome == (c.epochStartAfter.getD (i + 1) 0 == 1))
    "invalid: validator_update does not match the epoch start"
  let slotB2 ← match B2.slots[idx]? with | some p => pure p.2 | none => throw "invalid: slot"
  -- 3.3 / 3.4 source receipts. Genesis source blocks carry no receipt proofs and contribute no
  -- receipts (`chunk_validation.rs:456-469`: genesis ⇒ `source_receipt_proofs` empty, `vec![]`).
  let mut receipts : List Rcpt := []
  let mut used : Nat := 0
  for S in sourceBlks do
    if S.isGenesis then
      check (w.entries.isEmpty) "invalid: source_receipt_proofs must be empty for a genesis source block"
    else
      let mut proofs : List EntryD2 := []
      for (s, ci) in S.slots do
        if s.heightIncluded == S.hdr.height then
          let key := chunkHash s.inner ci.encodedMerkleRoot
          let e ← match lookupLastD2 key w.entries with
            | some e => pure e
            | none => throw "invalid: missing source receipt proof"
          driver.validateRouting L e.receipts
          check (e.proof.fromShard == ci.shardId) "invalid: receipt proof from_shard_id"
          check (e.proof.toShard == H.shardId) "invalid: receipt proof to_shard_id"
          check (verifyReceiptProofD2 ci.prevOutgoingReceiptsRoot e) "invalid: receipt proof merkle path"
          proofs := proofs ++ [e]
          used := used + 1
      let shuffled ← match shuffleWithSeed proofs S.hdr.prevHash with
        | some p => pure p
        | none => throw "invalid: shuffle fuel exhausted (probability < 2^-1024)"
      receipts := receipts ++
        (shuffled.map fun e => e.receipts.filter fun r => driver.receiptShard L r == H.shardId).flatten
  check ((distinctKeysD2 w.entries).length == used) "invalid: source_receipt_proofs contains extra proofs"
  check (sha256 (encodeRcpts receipts) == w.appliedReceiptsHash) "invalid: applied receipts hash"
  -- steps 8, 9: transactions of the last new chunk and their validity flags
  check (merklizeBorsh (w.txs.map TxD2.raw) == slotB2.txRoot) "invalid: transaction root of the last chunk"
  check (c.txValid.length == w.txs.length) "invalid: tx_valid length"
  -- genesis: the flags are derived all-1 (`chunk_validation.rs:382-386`), so a truthful claim
  -- carries all 1s (claim-v3 T13).
  if B2.isGenesis then
    check (c.txValid.all (·.toNat == 1)) "invalid: tx_valid not all 1 for a genesis main block"
  -- 3.5 main transition
  let sched ← match Scheduler.Params.calculate Scheduler.Config.pv86 L.numShards with
    | some p => pure p
    | none => throw "invalid: bandwidth scheduler params (assert panics)"
  let facts0 := c.applyFacts.headD ⟨none, 0, none⟩
  let ctxB2 := blockCtx L H.shardId slotB2.gasLimit B2 B2.hdr.nextGasPrice
  let merged := w.main.values ++ codes
  let store := mkHStore merged
  -- w.size: sums the merged list (conservative; spec/near-chunk-validation-d3.md §2.2)
  let baseBytes := (merged.map List.length).foldl (· + ·) 0
  -- The main transition's output. Genesis: the stored chunk extra, with no outgoing receipts
  -- (`chunk_validation.rs:602-604`), and the header's `prev_state_root` is its `state_root`
  -- possibly updated by implicit transitions.
  let mut root : Bytes ← match gen? with
    | some ce =>
      check (w.main.postStateRoot == ce.stateRoot)
        "invalid: main transition post state root differs from genesis_chunk_extra"
      -- No trie reads happen for a genesis chunk, so the witness's `base_state` is unread and its
      -- removals are zero; the proof-size bound is applied to the merged list as in D2.
      check (driver.sizeOk baseBytes 0)
        "out of domain (w.size): storage-proof upper bound may exceed main_storage_proof_size_soft_limit"
      pure ce.stateRoot
    | none =>
      let env : Env := { envOf c ctxB2 B2 facts0.minimumStake sched with
                         store := store, preRoot := slotB2.prevStateRoot }
      let tMain := revealAll store revealFuel slotB2.prevStateRoot
      check (tMain.hashOf == slotB2.prevStateRoot) "invalid: main base_state does not hash to prev_state_root"
      let lastProps := slotB2.proposals.filterMap decodeProposal
      let out ← driver.apply hooks prims env tMain facts0.validatorUpdate lastProps receipts
        (w.txs.zip (c.txValid.map (· != 0))) slotB2.congestion
      check (driver.sizeOk baseBytes out.cdRemovals)
        "out of domain (w.size): storage-proof upper bound may exceed main_storage_proof_size_soft_limit"
      -- D3: per-chunk WASM gas cap (`G_α`, D3_WASM_REQUIREMENTS §1.1/§2.4); D2 passes `none`
      if let some cap := gasCap then
        check (out.wasmGas ≤ cap) s!"out of domain (e.g_alpha): chunk function-call gas {out.wasmGas} > G_α {cap}"
      check (out.root == w.main.postStateRoot) "invalid: main transition post state root"
      pure out.root
  -- 3.6 implicit transitions (`chunk_validation.rs:662-750`): applied to the main transition's
  -- chunk extra. For genesis these are the *only* applied transitions and they run on the stored
  -- genesis chunk extra's root.
  check (w.implicit.length == implicitIdx.length) "invalid: implicit transitions count"
  -- For genesis, `mainProps` is the genesis chunk extra's proposals; `applyMissingChunkD2` reads
  -- them for the validator-account filtering (`process_state_update`, `runtime/mod.rs:229-271`).
  -- The implicit transitions are applied against the genesis root, so the proposals passed in are
  -- the genesis chunk extra's — not a computed main transition's. For a genesis chunk the list is
  -- empty in every recorded case (`create_genesis_chunk_extra` stores `vec![]`), and the argument
  -- only filters this shard's stake-info entries, so an empty list is the validator's value.
  let mainProps : List (Bytes × Nat) := match gen? with
    | some ce => ce.proposals.filterMap decodeProposal
    | none => []
  for ((i, f), T) in (implicitIdx.zip (c.applyFacts.drop (if B2.isGenesis then 0 else 1))).zip w.implicit do
    let M ← match blks[i]? with | some b => pure b | none => throw "invalid: walk"
    let ctxM := blockCtx L H.shardId slotB2.gasLimit M M.hdr.nextGasPrice
    let envM : Env := envOf c ctxM M f.minimumStake sched
    let tM := revealTrie T.values root
    root ← applyMissingChunkD2 prims envM tM f.validatorUpdate mainProps
    check (root == T.postStateRoot) "invalid: implicit transition post state root"
  -- 3.7 comparison with the endorsed header (`validate.rs:133-188`)
  check (H.prevStateRoot == root) "invalid: InvalidStateRoot"
  match gen? with
  | some ce =>
    check (H.prevOutcomeRoot == ce.outcomeRoot) "invalid: InvalidOutcomesProof"
    check (H.proposals == ce.proposals) "invalid: InvalidValidatorProposals"
    check (H.gasLimit == ce.gasLimit) "invalid: InvalidGasLimit"
    check (H.prevGasUsed == ce.gasUsed) "invalid: InvalidGasUsed"
    check (H.prevBalanceBurnt == ce.balanceBurnt) "invalid: InvalidBalanceBurnt"
    check (H.prevOutgoingReceiptsRoot == emptyOutgoingReceiptsRootD2 L)
      "invalid: InvalidReceiptsProof"
    check (H.congestion == ce.congestion) "invalid: InvalidCongestionInfo"
    check ((some H.bwRequests) == ce.bandwidthRequests) "invalid: InvalidBandwidthRequests"
    check (H.proposedSplit == ce.proposedSplit) "invalid: InvalidChunkHeaderShardSplit"
  | none => pure ()
  check (H.txRoot == merklizeBorsh (w.newTxs.map TxD2.raw)) "invalid: InvalidTxRoot"
  let body := u32 w.newTxs.length ++ concatAll (w.newTxs.map TxD2.raw) ++ encodeRcpts []
  match encodedMerkleRoot c.rsDataParts c.rsTotalParts body with
  | none => throw "invalid: Reed-Solomon parameters"
  | some (emr, len) =>
    check (H.encodedMerkleRoot == emr) "invalid: InvalidChunkEncodedMerkleRoot"
    check (H.encodedLength == len) "invalid: InvalidChunkEncodedLength"


theorem legacy_core_eq (h : ActionHooks) (a : Bool) (c w : Bytes) (cap : Option Nat) :
    checkD2CoreWith legacyDriver h a c w cap = checkD2Core h a c w cap := rfl

theorem legacy_genesis_eq (h : ActionHooks) (a : Bool) (c w : Bytes) (cap : Option Nat) :
    checkD2CoreGWith legacyDriver h a c w cap = checkD2CoreG h a c w cap := rfl

end NearSpecV3.Successor
