import NearSpecV3.ChunkValidationD1
import NearSpecV3.D2.RuntimeD2

/-!
# `NearSpecV3.ChunkValidationD2` — `Rel_D2(claim, witness)`

The statement `near/pv86/chunk-validation/v0` restricted to domain D2
(spec/near-chunk-validation-d2.md): every non-WASM action, all receipt kinds, the delayed
queue, outgoing buffers and bandwidth requests, yield timeouts, validator accounts updates and
segments spanning several epochs with one shard layout. Same claim and witness formats;
`checkD2 claimBytes witnessBytes` returns

* `.ok ()` — `Rel(c, w) ∧ InD2(c, w)`;
* `.error "invalid: …"` — `¬Rel(c, w)` (as far as decided inside D2);
* `.error "out of domain …"` — the case leaves D2.

Differences from `checkD1` (§11 of the D2 spec): the witness decoder admits every D2 receipt
and transaction shape (`D2.pRcpt`, `D2.pTxD2`); several epochs (`epoch_start_after` checked
against the headers, `validator_update` present iff the applied block starts an epoch); the main
transition is `D2.applyNewChunkD2` on the fully revealed recorded storage, implicit
transitions `D2.applyMissingChunkD2`; the header comparison uses the computed validator
proposals, congestion info and bandwidth requests; `w.size` bounds the storage-proof upper
bound.
-/

namespace NearSpecV3

open NearSpec NearSpecV3.D2

structure EntryD2 where
  key : Bytes
  receipts : List Rcpt
  proof : ShardProof

structure StateWitnessD2 where
  epochId : Bytes
  innerBytes : Bytes
  inner : ChunkInner
  main : Transition
  entries : List EntryD2
  appliedReceiptsHash : Bytes
  txs : List TxD2
  implicit : List Transition
  newTxs : List TxD2

def pEntryD2 : P EntryD2 := fun bs => do
  let (k, bs) ← pHash "ChunkHash" bs
  let (rs, bs) ← pVec "proof receipts" pRcpt bs
  let (f, bs) ← pU64 "from_shard_id" bs
  let (t, bs) ← pU64 "to_shard_id" bs
  let (path, bs) ← pVec "merkle path" pPathItem bs
  pure (⟨k, rs, ⟨f, t, path⟩⟩, bs)

def decodeStateWitnessD2 (bs : Bytes) : Except String StateWitnessD2 := do
  if lenT bs > MAX_WITNESS then throw "decode: witness larger than 64 MiB"
  let (t, bs) ← pU8 "ChunkStateWitness tag" bs
  if t != 1 then throw "decode: ChunkStateWitness tag"
  let (eid, bs) ← pHash "epoch_id" bs
  let ((ib, ci), bs) ← pChunkHeader bs
  let (main, bs) ← pTransition bs
  let (entries, bs) ← pVec "source_receipt_proofs" pEntryD2 bs
  let (arh, bs) ← pHash "applied_receipts_hash" bs
  let (txs, bs) ← pVec "transactions" pTxD2 bs
  let (impl, bs) ← pVec "implicit_transitions" pTransition bs
  let (ntxs, bs) ← pVec "new_transactions" pTxD2 bs
  if !bs.isEmpty then throw "decode: Not all bytes read"
  pure ⟨eid, ib, ci, main, entries, arh, txs, impl, ntxs⟩

def lookupLastD2 (k : Bytes) : List EntryD2 → Option EntryD2
  | [] => none
  | e :: es =>
    match lookupLastD2 k es with
    | some x => some x
    | none => if e.key == k then some e else none

def distinctKeysD2 : List EntryD2 → List Bytes
  | [] => []
  | e :: es => let ks := distinctKeysD2 es; if ks.contains e.key then ks else e.key :: ks

def verifyReceiptProofD2 (root : Bytes) (e : EntryD2) : Bool :=
  let item := sha256 (u64 e.proof.toShard ++ encodeRcpts e.receipts)
  rootFromPath (sha256 item) e.proof.path == root

def outgoingReceiptsRootD2 (l : Layout) (rs : List Rcpt) : Bytes :=
  merklizeBorsh (l.shardIds.map fun s =>
    sha256 (u64 s ++ encodeRcpts (rs.filter fun r => l.shardOf r.recv == s)))

/-- Strictly ascending byte order of epoch ids. -/
def strictlyAscending : List Bytes → Bool
  | a :: b :: rest => bytesLt a b && strictlyAscending (b :: rest)
  | _ => true

def dedupSorted (l : List Bytes) : List Bytes :=
  (sortKV (l.map fun k => (k, none))).foldr (fun (k, _) acc =>
    match acc with
    | k' :: _ => if k == k' then acc else k :: acc
    | [] => [k]) []

/-- The `Env` of a block `b` (main or implicit transition): the `ApplyCtx` plus the E1 facts of
the block header and of its epoch's claim record (spec/near-chunk-validation-d3.md §3, §8 E1). -/
def envOf (c : Claim) (ctx : ApplyCtx) (b : Blk) (minStake : Nat) (sched : Scheduler.Params) : Env :=
  let ep := c.epochs.find? (·.epochId == b.hdr.epochId)
  { ctx, chainId := c.chainId, minStake, sched,
    blockTimestamp := b.hdr.timestamp, randomValue := b.hdr.randomValue,
    epochHeight := (ep.map (·.epochHeight)).getD 0,
    validators := (ep.map (·.validators)).getD [] }

/-- The D2 pipeline with the `FunctionCall` hooks as a parameter (the D3 checker reuses it).
`allowCodes = false` keeps D2's `w.no_code` (any contract code ⇒ out of domain); with
`allowCodes = true` the witness's code blobs are appended to the main recorded storage exactly as
the partial-witness tracker does (`pwt.rs:693-696`): the main trie is revealed from, and
`Env.codeOf` looks up, the merged list `w.main.values ++ codes` (E2). The hooks reach the merged
storage, the pre-state root and the block / epoch facts through `ActCtx.env`. -/
def checkD2Core (hooks : ActionHooks) (allowCodes : Bool) (claimBytes witnessBytes : Bytes) :
    Except String Unit := do
  -- 3.1 decoding, actor checks
  let c ← (decodeClaimE claimBytes).mapError (fun e => s!"invalid claim: {e}")
  let (swBytes, codes) ← decodeWitnessFile witnessBytes
  if !allowCodes then check codes.isEmpty "out of domain (w.no_code): contract code"
  check (lenT swBytes ≤ 8388608) "out of domain (w.size): witness larger than 8 MiB"
  let w ← decodeStateWitnessD2 swBytes
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
  check (c.epochs.all (·.shardLayout == ep.shardLayout)) "out of domain (c.same_layout): resharding"
  let L ← decodeLayout ep.shardLayout
  check (1 ≤ L.numShards && L.numShards ≤ 64) "out of domain (c.layout)"
  check (rsGenesisParamsOk c.rsDataParts c.rsTotalParts) "invalid: Reed-Solomon parameters"
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
        check (e.proof.fromShard == ci.shardId) "invalid: receipt proof from_shard_id"
        check (e.proof.toShard == H.shardId) "invalid: receipt proof to_shard_id"
        check (verifyReceiptProofD2 ci.prevOutgoingReceiptsRoot e) "invalid: receipt proof merkle path"
        proofs := proofs ++ [e]
        used := used + 1
    let shuffled ← match shuffleWithSeed proofs S.hdr.prevHash with
      | some p => pure p
      | none => throw "invalid: shuffle fuel exhausted (probability < 2^-1024)"
    receipts := receipts ++
      (shuffled.map fun e => e.receipts.filter fun r => L.shardOf r.recv == H.shardId).flatten
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
  let out ← applyNewChunkD2 hooks prims env tMain facts0.validatorUpdate lastProps receipts
    (w.txs.zip (c.txValid.map (· != 0))) slotB2.congestion
  -- w.size: sums the merged list (conservative; spec/near-chunk-validation-d3.md §2.2)
  let baseBytes := (merged.map List.length).foldl (· + ·) 0
  check (baseBytes + 2000 * out.cdRemovals ≤ 4000000)
    "out of domain (w.size): storage-proof upper bound may exceed main_storage_proof_size_soft_limit"
  let mut root := out.root
  check (root == w.main.postStateRoot) "invalid: main transition post state root"
  -- 3.6 implicit transitions
  check (w.implicit.length == implicitIdx.length) "invalid: implicit transitions count"
  let mainProps := out.proposals.map fun p => (p.acct, p.stake)
  for ((i, f), T) in (implicitIdx.zip (c.applyFacts.drop 1)).zip w.implicit do
    let M ← match blks[i]? with | some b => pure b | none => throw "invalid: walk"
    let ctxM := blockCtx L H.shardId slotB2.gasLimit M M.hdr.nextGasPrice
    let envM : Env := envOf c ctxM M f.minimumStake sched
    let tM := revealTrie T.values root
    root ← applyMissingChunkD2 prims envM tM f.validatorUpdate mainProps
    check (root == T.postStateRoot) "invalid: implicit transition post state root"
  -- 3.7 comparison with the endorsed header
  check (H.prevStateRoot == root) "invalid: InvalidStateRoot"
  check (H.prevOutcomeRoot == outcomeRootD1 out.outcomes) "invalid: InvalidOutcomesProof"
  check (H.proposals == out.proposals.map Proposal.encode) "invalid: InvalidValidatorProposals"
  check (H.gasLimit == slotB2.gasLimit) "invalid: InvalidGasLimit"
  check (H.prevGasUsed == out.gasUsed) "invalid: InvalidGasUsed"
  check (H.prevBalanceBurnt == out.balanceBurnt) "invalid: InvalidBalanceBurnt"
  check (H.prevOutgoingReceiptsRoot == outgoingReceiptsRootD2 L out.outgoing) "invalid: InvalidReceiptsProof"
  check (H.congestion == out.congestion) "invalid: InvalidCongestionInfo"
  check (H.bwRequests == out.bwRequests) "invalid: InvalidBandwidthRequests"
  check H.proposedSplit.isNone "invalid: InvalidChunkHeaderShardSplit"
  check (H.txRoot == merklizeBorsh (w.newTxs.map TxD2.raw)) "invalid: InvalidTxRoot"
  let body := u32 w.newTxs.length ++ concatAll (w.newTxs.map TxD2.raw) ++ encodeRcpts out.outgoing
  match encodedMerkleRoot c.rsDataParts c.rsTotalParts body with
  | none => throw "invalid: Reed-Solomon parameters"
  | some (emr, len) =>
    check (H.encodedMerkleRoot == emr) "invalid: InvalidChunkEncodedMerkleRoot"
    check (H.encodedLength == len) "invalid: InvalidChunkEncodedLength"

/-- The D2 checker: `checkD2Core` with `d2Hooks` (FunctionCall ⇒ out of domain) and `w.no_code`. -/
def checkD2 (claimBytes witnessBytes : Bytes) : Except String Unit :=
  checkD2Core d2Hooks false claimBytes witnessBytes

/-- **The D2 relation** on canonical bytes. -/
def acceptsD2 (claimBytes witnessBytes : Bytes) : Bool :=
  match checkD2 claimBytes witnessBytes with
  | .ok () => true
  | .error _ => false

def RelD2 (claimBytes witnessBytes : Bytes) : Prop := acceptsD2 claimBytes witnessBytes = true

instance (c w : Bytes) : Decidable (RelD2 c w) := by unfold RelD2; infer_instance

end NearSpecV3
