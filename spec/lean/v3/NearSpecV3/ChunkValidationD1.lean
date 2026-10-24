import NearSpecV3.ChunkValidationV0
import NearSpecV3.RuntimeD1
import NearSpecV3.Observable

/-!
# `NearSpecV3.ChunkValidationD1` — `Rel_D1(claim, witness)`

The statement `near/pv86/chunk-validation/v0` restricted to domain D1
(spec/near-chunk-validation-d1.md): D0 plus Transfer transactions. Same claim and witness
formats as D0 (spec/claim-v3.md); `checkD1 claimBytes witnessBytes` returns

* `.ok ()` — `Rel(c, w) ∧ InD1(c, w)`;
* `.error "invalid: …"` — `¬Rel(c, w)` (as far as decided inside D1);
* `.error "out of domain …"` — the case leaves D1.

Differences from `checkD0` (each cites nearcore; spec §3 step numbers of the v0 doc):

* witness decoding admits `transactions` / `new_transactions` in the D1 shape (`TxD1.pTxD1`);
* step 6: every `new_transactions[i]` passes `check_valid_for_config`
  (`chunk_validation.rs:323-341`) — the size gate; **no signature check** on new transactions;
* step 8: `merklize(transactions).root = tx_root` of the last new chunk (`chunk_validation.rs:368-380`);
* step 9: `|tx_valid| = |transactions|` (the trusted validity flags, `chunk_validation.rs:382-401`);
* step 11: `RuntimeD1.applyNewChunkD1` (transactions, local receipts, then incoming receipts);
* outcome root over transaction and receipt outcomes with their statuses;
* step 17: `tx_root = merklize(new_transactions).root`; step 18: Reed–Solomon body
  `borsh((new_transactions, outgoing))`;
* `e.distinct_ids` covers incoming and local receipt ids.
-/

namespace NearSpecV3

open NearSpec NearSpec.TransferV1

structure StateWitnessD1 where
  epochId : Bytes
  innerBytes : Bytes
  inner : ChunkInner
  main : Transition
  entries : List ProofEntry
  appliedReceiptsHash : Bytes
  txs : List Tx
  implicit : List Transition
  newTxs : List Tx

def decodeStateWitnessD1 (bs : Bytes) : Except String StateWitnessD1 := do
  if lenT bs > MAX_WITNESS then throw "decode: witness larger than 64 MiB"
  let (t, bs) ← pU8 "ChunkStateWitness tag" bs
  if t != 1 then throw "decode: ChunkStateWitness tag"
  let (eid, bs) ← pHash "epoch_id" bs
  let ((ib, ci), bs) ← pChunkHeader bs
  let (main, bs) ← pTransition bs
  let (entries, bs) ← pVec "source_receipt_proofs" pEntry bs
  let (arh, bs) ← pHash "applied_receipts_hash" bs
  let (txs, bs) ← pVec "transactions" pTxD1 bs
  let (impl, bs) ← pVec "implicit_transitions" pTransition bs
  let (ntxs, bs) ← pVec "new_transactions" pTxD1 bs
  if !bs.isEmpty then throw "decode: Not all bytes read"
  pure ⟨eid, ib, ci, main, entries, arh, txs, impl, ntxs⟩

/-- **The D1 output record**, built from the values the main transition and the implicit loop computed.
The arguments are exactly the operands of the endorsed-header comparison at step 3.7: `root` (the
post-state root), `out.gasUsed`, `out.tokensBurnt`, `outgoingReceiptsRoot L out.outgoing`,
`merklizeBorsh (w.newTxs.map Tx.raw)`, the slot's own congestion with the allowed shard filled in, and
the Reed–Solomon `(emr, len)`. The three fields D1 does not compute are honest constants: `proposals`
and `bwRequests` are empty (the comparison's whole content is "the header's list is empty") and
`wasmGas` is `0` (no WASM in D1). -/
def d1Outputs (root : Bytes) (outcomes : List OutD1) (gasBurnt tokensBurnt : Nat)
    (layout : Layout) (outgoing : List Receipt) (txRoot : Bytes) (emr : Bytes) (len : Nat)
    (congestion : Congestion) : Observable :=
  { stateRoot := root
    outcomeRoot := outcomeRootD1 outcomes
    gasBurnt := gasBurnt
    balanceBurnt := tokensBurnt
    outgoingReceiptsRoot := outgoingReceiptsRoot layout outgoing
    proposals := []
    txRoot := txRoot
    encodedMerkleRoot := emr
    encodedLength := len
    congestion := congestion
    bwRequests := []
    logs := outcomes.map (fun o => o.logs) |>.flatten
    receiptCount := outgoing.length
    wasmGas := 0 }

/-- **The builder's fields are its computed arguments.** Every consensus field of `d1Outputs` is the
value passed in — so a report that compares the emitted record against the endorsed header is comparing
the same expressions the checker's comparison block tested. The list fields are the honest constants. -/
theorem d1Outputs_fields (root : Bytes) (outcomes : List OutD1) (gasBurnt tokensBurnt : Nat)
    (layout : Layout) (outgoing : List Receipt) (txRoot emr : Bytes) (len : Nat)
    (congestion : Congestion) :
    (d1Outputs root outcomes gasBurnt tokensBurnt layout outgoing txRoot emr len congestion).stateRoot = root ∧
    (d1Outputs root outcomes gasBurnt tokensBurnt layout outgoing txRoot emr len congestion).outcomeRoot =
      outcomeRootD1 outcomes ∧
    (d1Outputs root outcomes gasBurnt tokensBurnt layout outgoing txRoot emr len congestion).gasBurnt = gasBurnt ∧
    (d1Outputs root outcomes gasBurnt tokensBurnt layout outgoing txRoot emr len congestion).balanceBurnt = tokensBurnt ∧
    (d1Outputs root outcomes gasBurnt tokensBurnt layout outgoing txRoot emr len congestion).outgoingReceiptsRoot =
      outgoingReceiptsRoot layout outgoing ∧
    (d1Outputs root outcomes gasBurnt tokensBurnt layout outgoing txRoot emr len congestion).txRoot = txRoot ∧
    (d1Outputs root outcomes gasBurnt tokensBurnt layout outgoing txRoot emr len congestion).encodedMerkleRoot = emr ∧
    (d1Outputs root outcomes gasBurnt tokensBurnt layout outgoing txRoot emr len congestion).encodedLength = len ∧
    (d1Outputs root outcomes gasBurnt tokensBurnt layout outgoing txRoot emr len congestion).congestion = congestion ∧
    (d1Outputs root outcomes gasBurnt tokensBurnt layout outgoing txRoot emr len congestion).receiptCount =
      outgoing.length := by
  simp [d1Outputs]

/-- The three fields D1 does not compute are the honest constants: both list fields are empty and
`wasmGas` is zero. -/
theorem d1Outputs_not_computed (root : Bytes) (outcomes : List OutD1) (gasBurnt tokensBurnt : Nat)
    (layout : Layout) (outgoing : List Receipt) (txRoot emr : Bytes) (len : Nat)
    (congestion : Congestion) :
    (d1Outputs root outcomes gasBurnt tokensBurnt layout outgoing txRoot emr len congestion).proposals = [] ∧
    (d1Outputs root outcomes gasBurnt tokensBurnt layout outgoing txRoot emr len congestion).bwRequests = [] ∧
    (d1Outputs root outcomes gasBurnt tokensBurnt layout outgoing txRoot emr len congestion).wasmGas = 0 := by
  simp [d1Outputs]

/-- The D1 transition returning the consensus outputs it computed.

This runs the *same* pipeline as the signed `checkD1` (which is definitionally its projection to the
verdict, below) and returns the values the header comparison at step 3.7 tests. Every field is a
computed value, not a read-back of the endorsed header:

* `stateRoot` — `root` after the main and every implicit transition (`H.prevStateRoot`);
* `outcomeRoot` — `outcomeRootD1 out.outcomes` (`H.prevOutcomeRoot`);
* `gasBurnt` — `out.gasUsed` (`H.prevGasUsed`);
* `balanceBurnt` — `out.tokensBurnt` (`H.prevBalanceBurnt`);
* `outgoingReceiptsRoot` — `outgoingReceiptsRoot L out.outgoing` (`H.prevOutgoingReceiptsRoot`);
* `proposals` — `[]`: D1 computes no proposal list; the comparison checks the header's is empty
  (`H.proposals.isEmpty`), so the computed list is honestly empty;
* `txRoot` — `merklizeBorsh (w.newTxs.map Tx.raw)` (`H.txRoot`);
* `encodedMerkleRoot` / `encodedLength` — the Reed–Solomon encoded chunk body (`H.encodedMerkleRoot`,
  `H.encodedLength`);
* `congestion` — `ownCongestion` (the slot's own congestion with the allowed shard filled in)
  (`H.congestion`);
* `bwRequests` — `[]`: D1 computes no bandwidth requests; the comparison checks the header's is empty
  (`H.bwRequests.isEmpty`);
* `logs` — every executed outcome's logs in order (folded into `outcomeRoot`; D0–D1 outcomes carry
  none, so this is `[]` on the wire);
* `receiptCount` — `out.outgoing.length` (folded into `outgoingReceiptsRoot`);
* `wasmGas` — `0`: D1 has no WASM execution. -/
def checkD1CoreObs (claimBytes witnessBytes : Bytes) : Except String Observable := do
  -- 3.1 decoding, actor checks
  let c ← (decodeClaimE claimBytes).mapError (fun e => s!"invalid claim: {e}")
  let (swBytes, codes) ← decodeWitnessFile witnessBytes
  check codes.isEmpty "out of domain (w.no_code): contract code"
  check (lenT swBytes ≤ 8388608) "out of domain (w.size): witness larger than 8 MiB"
  let w ← decodeStateWitnessD1 swBytes
  check (w.innerBytes == c.chunkInner) "invalid: witness chunk header differs from the claim"
  check (w.epochId == c.epochId) "invalid: epoch id"
  let H ← (decodeChunkInner c.chunkInner).mapError (fun e => s!"invalid claim: {e}")
  -- claim-level conditions and trusted-fact consistency (as D0, minus c.no_tx_flags)
  check (c.protocolVersion == 86) "out of domain (c.pv86)"
  check (c.epochs.length == 1) "out of domain (c.single_epoch): more than one epoch"
  let ep := c.epochs.headD ⟨[], 0, 0, [], []⟩
  check (ep.epochId == c.epochId && ep.protocolVersion == c.protocolVersion)
    "invalid: epoch table does not match epoch_id / protocol_version"
  let L ← decodeLayout ep.shardLayout
  check (1 ≤ L.numShards && L.numShards ≤ 64) "out of domain (c.layout)"
  check (rsGenesisParamsOk c.rsDataParts c.rsTotalParts) "invalid: Reed-Solomon parameters"
  check (c.blocks.length ≤ 32) "out of domain (c.segment)"
  check (c.epochStartAfter.length == c.blocks.length) "invalid: epoch_start_after length"
  check (c.epochStartAfter.all (· == 0)) "out of domain (c.single_epoch): epoch start"
  check (c.applyFacts.all fun f => f.validatorUpdate.isNone && f.splitGate.isNone)
    "out of domain (c.no_split_gate)"
  -- step 6: check_valid_for_config on new_transactions (size gate; no signature check)
  check (w.newTxs.all Tx.sizeOk) "invalid: new transaction exceeds max_transaction_size"
  -- 3.2 chain segment: hashes, slots, walk
  let blks ← c.blocks.mapM decodeBlk
  check (!blks.isEmpty) "invalid: empty chain segment"
  check (blks.all fun b => b.hdr.epochId == c.epochId) "out of domain (c.single_epoch)"
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
  let implicitBlks := (blks.take b2i).reverse
  let sourceBlks := (blks.drop b2i).take (stop - b2i)
  check (c.applyFacts.length == 1 + implicitBlks.length) "invalid: apply_facts length"
  let prevB2 ← match blks[b2i + 1]? with | some b => pure b | none => throw "invalid: walk"
  let slotB2 ← match B2.slots[idx]? with | some p => pure p.2 | none => throw "invalid: slot"
  -- 3.3 / 3.4 pre-validation: source receipts
  let mut receipts : List Receipt := []
  let mut used : Nat := 0
  for S in sourceBlks do
    let mut proofs : List ProofEntry := []
    for (s, ci) in S.slots do
      if s.heightIncluded == S.hdr.height then
        let key := chunkHash s.inner ci.encodedMerkleRoot
        let e ← match lookupLast key w.entries with
          | some e => pure e
          | none => throw "invalid: missing source receipt proof"
        check (e.proof.fromShard == ci.shardId) "invalid: receipt proof from_shard_id"
        check (e.proof.toShard == H.shardId) "invalid: receipt proof to_shard_id"
        check (verifyReceiptProof ci.prevOutgoingReceiptsRoot e) "invalid: receipt proof merkle path"
        proofs := proofs ++ [e]
        used := used + 1
    let shuffled ← match shuffleWithSeed proofs S.hdr.prevHash with
      | some p => pure p
      | none => throw "invalid: shuffle fuel exhausted (probability < 2^-1024)"
    receipts := receipts ++
      (shuffled.map fun e => e.receipts.filter fun r => L.shardOf r.receiverId == H.shardId).flatten
  check ((distinctKeys w.entries).length == used) "invalid: source_receipt_proofs contains extra proofs"
  check (sha256 (encodeReceipts receipts) == w.appliedReceiptsHash) "invalid: applied receipts hash"
  -- steps 8, 9: transactions of the last new chunk and their validity flags
  check (merklizeBorsh (w.txs.map Tx.raw) == slotB2.txRoot) "invalid: transaction root of the last chunk"
  check (c.txValid.length == w.txs.length) "invalid: tx_valid length"
  -- witness-level domain conditions
  let baseBytes := (w.main.values.map List.length).foldl (· + ·) 0
  check (baseBytes ≤ 3000000) "out of domain (w.size): base_state larger than 3 MB"
  let own := slotB2.congestion
  check (own.delayedGas == 0 && own.bufferedGas == 0 && own.receiptBytes == 0)
    "out of domain (c.own_congestion_zero)"
  -- 3.5 main transition
  let ctxB2 := blockCtx L H.shardId slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  let t0 := partialTrie w.main.values slotB2.prevStateRoot [keyBufferedIdx]
  let bshards ← match t0.find keyBufferedIdx with
    | some v => (bufferedShards v).mapError id
    | none => throw "invalid: MissingTrieValue (BufferedReceiptIndices)"
  let tMain := partialTrie w.main.values slotB2.prevStateRoot
    (mainKeys receipts bshards ++ txKeys w.txs)
  check (tMain.hashOf == slotB2.prevStateRoot) "invalid: main base_state does not hash to prev_state_root"
  let out ← applyNewChunkD1 prims ctxB2 tMain receipts (w.txs.zip (c.txValid.map (· != 0)))
  check (decide (out.localIds ++ receipts.map Receipt.receiptId).Nodup) "out of domain (e.distinct_ids)"
  let mut root := out.trie.hashOf
  check (root == w.main.postStateRoot) "invalid: main transition post state root"
  -- 3.6 implicit transitions
  check (w.implicit.length == implicitBlks.length) "invalid: implicit transitions count"
  for (M, T) in implicitBlks.zip w.implicit do
    let ctxM := blockCtx L H.shardId slotB2.gasLimit M M.hdr.nextGasPrice
    let tM := partialTrie T.values root [keyDelayedIdx, keyBwState]
    let tM' ← applyMissingChunk prims ctxM tM
    root := tM'.hashOf
    check (root == T.postStateRoot) "invalid: implicit transition post state root"
  -- 3.7 comparison with the endorsed header
  let allowed := L.shardIds.getD ((B2.hdr.height + idx) % L.numShards) H.shardId
  let ownCongestion : Congestion := { own with allowedShard := allowed }
  check (H.prevStateRoot == root) "invalid: InvalidStateRoot"
  check (H.prevOutcomeRoot == outcomeRootD1 out.outcomes) "invalid: InvalidOutcomesProof"
  check H.proposals.isEmpty "invalid: InvalidValidatorProposals"
  check (H.gasLimit == slotB2.gasLimit) "invalid: InvalidGasLimit"
  check (H.prevGasUsed == out.gasUsed) "invalid: InvalidGasUsed"
  check (H.prevBalanceBurnt == out.tokensBurnt) "invalid: InvalidBalanceBurnt"
  check (H.prevOutgoingReceiptsRoot == outgoingReceiptsRoot L out.outgoing) "invalid: InvalidReceiptsProof"
  check (H.congestion == ownCongestion) "invalid: InvalidCongestionInfo"
  check H.bwRequests.isEmpty "invalid: InvalidBandwidthRequests"
  check H.proposedSplit.isNone "invalid: InvalidChunkHeaderShardSplit"
  check (H.txRoot == merklizeBorsh (w.newTxs.map Tx.raw)) "invalid: InvalidTxRoot"
  let body := u32 w.newTxs.length ++ concatAll (w.newTxs.map Tx.raw) ++ encodeReceipts out.outgoing
  match encodedMerkleRoot c.rsDataParts c.rsTotalParts body with
  | none => throw "invalid: Reed-Solomon parameters"
  | some (emr, len) =>
    check (H.encodedMerkleRoot == emr) "invalid: InvalidChunkEncodedMerkleRoot"
    check (H.encodedLength == len) "invalid: InvalidChunkEncodedLength"
    -- The consensus outputs this checker computed and compared against the endorsed header. The
    -- comparison block above tests exactly these expressions (`root`, `out.*`, `ownCongestion`,
    -- `merklizeBorsh …`, and this arm's `emr`/`len`); the two empty-list fields are what D1 verifies
    -- the header's lists to be. See `NearSpecV3.ChunkValidationD1Out` for the projection theorems.
    return d1Outputs root out.outcomes out.gasUsed out.tokensBurnt L out.outgoing
      (merklizeBorsh (w.newTxs.map Tx.raw)) emr len ownCongestion

/-- The signed D1 checker: the observable checker projected to its verdict. Definitionally the same
computation, so every downstream proof, verdict and relation is unchanged. -/
def checkD1 (claimBytes witnessBytes : Bytes) : Except String Unit :=
  (checkD1CoreObs claimBytes witnessBytes).map fun _ => ()

/-- The signed checker accepts iff the observable checker does. -/
theorem checkD1CoreObs_agrees (cb wb : Bytes) :
    (∃ o, checkD1CoreObs cb wb = .ok o) ↔ checkD1 cb wb = .ok () := by
  unfold checkD1
  rw [Except.map.eq_def]
  cases checkD1CoreObs cb wb <;> simp

/-- A rejection carries the signed checker's error string verbatim. -/
theorem checkD1CoreObs_reject (cb wb : Bytes) (e : String)
    (h : checkD1CoreObs cb wb = .error e) : checkD1 cb wb = .error e := by
  unfold checkD1
  rw [h]
  rfl

/-- **The D1 relation** on canonical bytes. -/
def acceptsD1 (claimBytes witnessBytes : Bytes) : Bool :=
  match checkD1 claimBytes witnessBytes with
  | .ok () => true
  | .error _ => false

def RelD1 (claimBytes witnessBytes : Bytes) : Prop := acceptsD1 claimBytes witnessBytes = true

instance (c w : Bytes) : Decidable (RelD1 c w) := by unfold RelD1; infer_instance

end NearSpecV3
