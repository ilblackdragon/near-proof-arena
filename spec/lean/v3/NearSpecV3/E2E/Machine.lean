import NearSpecV3.E2E.Engine
import NearSpecV3.Successor.Config

set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false

/-!
# E2E-M11, obligation 3 (part 2): the chunk machine `CM` and `checkSuccessor .allFeatures`

`CM` is the plan §3.1 small-step machine for the whole chunk check at the `allFeatures`
configuration (D-1). Its configurations (`Conf`) are:

* `init cb wb` — the claim and witness bytes (plan: claim and witness intake);
* `eng I c` — the main transition in progress: the intake record `I` (decoded claim, witness, walk,
  environment, receipts, …) and an engine configuration `c` (`Engine.lean`: position, receipt
  state, recorder state);
* `fin I out` — the main transition's result, before implicit transitions and outputs;
* `done H o` — the computed header outputs `o` and the claim's chunk header `H`;
* `doneG` — a segment that contains a genesis block, decided atomically (see below).

`step` (`CM.step`) is: `INTAKE` (`intakeK`, the verbatim prefix of `checkReshardCoreObs`), then the
engine's steps, then `FINAL` (`finK` + `tailNew`: implicit transitions, outgoing reassignment and
the computed header outputs). The acceptance condition `FinalOut` is `headerOk H o`: the ten
header-output comparisons and the gas-limit, split and transaction-root comparisons of the
checker's §3.7, all against the public chunk header.

`cm_iff` : `Tier.rel .allFeatures cb wb ↔ CMAccepts cb wb`. Equality lemmas `checkReshardCoreObs_split`
(`rfl`) show the intake and final slices are the checker's own code.

**Genesis segments.** `checkSuccessor` sends a claim whose segment contains a genesis block to
`checkD2CoreGWith`; `CM` decides it in one atomic step (`init → doneG`). This is exact, but such a
step is not cut further. Only chain segments that reach the genesis block take it (the first
blocks of a chain); refining it is listed as open in the plan §3.5.
-/

namespace NearSpecV3.E2E
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged NearSpecV3.Wasm
open NearSpecV3.Successor

/-- The intake record: everything the checker's prefix computes that its main transition and its
final part read. -/
structure Intake where
  c : Claim
  w : StateWitnessD2
  H : ChunkInner
  blks : List Blk
  ep : EpochRec
  L : Layout
  wk : Walk
  Lmain : Layout
  slotB2 : ChunkInner
  merged : List Bytes
  proposed : Option Bytes
  env : Env
  tMain : PTrie
  vu : Option ValidatorUpdateFacts
  lastProps : List (Bytes × Nat)
  receipts : List Rcpt
  txs : List (TxD2 × Bool)
  cong : Congestion

/-- `INTAKE`, part 3: the prefix of `checkReshardCoreObs` from the epoch-start checks to the split
gate (segment walk, receipt proofs, pre-state reveal), verbatim, followed by a continuation. -/
def intakeC {β : Type} (driver : ExecutionDriver) (allowCodes : Bool) (c : Claim) (codes : List Bytes)
    (w : StateWitnessD2) (H : ChunkInner) (blks : List Blk) (ep : EpochRec) (L : Layout)
    (k : Intake → Except String β) : Except String β := do
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
  check (w.newTxs.all TxD2.sizeOk) "invalid: new transaction exceeds max_transaction_size"
  let hashes := blks.map (·.hdr.hash)
  check (hashes.headD [] == H.prevBlockHash) "invalid: segment does not start at prev_block_hash"
  check ((blks.zip (hashes.drop 1)).all fun (b, h) => b.hdr.prevHash == h)
    "invalid: segment is not hash-linked"
  -- the shard must exist in the witness epoch's layout (chunk_validation.rs:172-175)
  let _ ← match L.index H.shardId with
    | some i => pure i
    | none => throw "invalid: shard not in layout"
  check (blks.all fun b => b.slots.all fun (sl, _) => sl.heightIncluded ≤ b.hdr.height)
    "invalid: height_included above block height (block_congestion_info panics)"
  -- the walk
  let wk ← walkSegment c blks afterEpochs H.shardId
  check (wk.stop + 1 == blks.length) "invalid: segment is not exactly the blocks the validator reads"
  let B2 ← match blks[wk.b2i]? with | some b => pure b | none => throw "invalid: walk"
  check (!B2.isGenesis) "out of domain (c.not_genesis)"
  check c.genesisChunkExtra.isNone "invalid: genesis_chunk_extra for a non-genesis main block"
  let Lmain ← decodeLayout wk.mainLayout
  let mainIdx ← match Lmain.index wk.mainShard with
    | some i => pure i
    | none => throw "invalid: shard not in layout"
  let oldIdx := wk.transitions.filterMap fun t => match t with | .old i _ => some i | _ => none
  check (c.applyFacts.length == 1 + oldIdx.length) "invalid: apply_facts length"
  let appliedIdx := wk.b2i :: oldIdx
  check ((appliedIdx.zip c.applyFacts).all fun (i, f) =>
      f.validatorUpdate.isSome == (c.epochStartAfter.getD (i + 1) 0 == 1))
    "invalid: validator_update does not match the epoch start"
  let prevB2 ← match blks[wk.b2i + 1]? with | some b => pure b | none => throw "invalid: walk"
  let slotB2 ← match B2.slots[mainIdx]? with | some p => pure p.2 | none => throw "invalid: slot"
  -- 3.3 / 3.4 source receipts (validate_source_receipt_proofs, chunk_validation.rs:457-524)
  let mut receipts : List Rcpt := []
  let mut used : Nat := 0
  for (j, target) in wk.sources do
    let S ← match blks[j]? with | some b => pure b | none => throw "invalid: walk"
    let mut proofs : List EntryD2 := []
    for (s, ci) in S.slots do
      if s.heightIncluded == S.hdr.height then
        let key := chunkHash s.inner ci.encodedMerkleRoot
        let e ← match lookupLastD2 key w.entries with
          | some e => pure e
          | none => throw "invalid: missing source receipt proof"
        driver.validateRouting Lmain e.receipts
        check (e.proof.fromShard == ci.shardId) "invalid: receipt proof from_shard_id"
        check (e.proof.toShard == target) "invalid: receipt proof to_shard_id"
        check (verifyReceiptProofD2 ci.prevOutgoingReceiptsRoot e) "invalid: receipt proof merkle path"
        proofs := proofs ++ [e]
        used := used + 1
    let shuffled ← match shuffleWithSeed proofs S.hdr.prevHash with
      | some p => pure p
      | none => throw "invalid: shuffle fuel exhausted (probability < 2^-1024)"
    receipts := receipts ++
      (shuffled.map fun e => e.receipts.filter fun r => driver.receiptShard Lmain r == wk.mainShard).flatten
  check ((distinctKeysD2 w.entries).length == used) "invalid: source_receipt_proofs contains extra proofs"
  check (sha256 (encodeRcpts receipts) == w.appliedReceiptsHash) "invalid: applied receipts hash"
  -- steps 8, 9: transactions of the last new chunk and their validity flags
  check (merklizeBorsh (w.txs.map TxD2.raw) == slotB2.txRoot) "invalid: transaction root of the last chunk"
  check (c.txValid.length == w.txs.length) "invalid: tx_valid length"
  -- 3.5 main transition, in the main block's layout and shard
  let schedOf (l : Layout) : Except String Scheduler.Params :=
    match Scheduler.Params.calculate Scheduler.Config.pv86 l.numShards with
    | some p => pure p
    | none => throw "invalid: bandwidth scheduler params (assert panics)"
  let sched ← schedOf Lmain
  let facts0 := c.applyFacts.headD ⟨none, 0, none⟩
  let ctxB2 := blockCtx Lmain wk.mainShard slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  let merged := w.main.values ++ codes
  let store := mkHStore merged
  let env : Env := { envOf c ctxB2 B2 facts0.minimumStake sched with
                     store := store, preRoot := slotB2.prevStateRoot }
  let tMain := revealAll store revealFuel slotB2.prevStateRoot
  check (tMain.hashOf == slotB2.prevStateRoot) "invalid: main base_state does not hash to prev_state_root"
  -- the split gate (compute_proposed_split runs on the pre-state trie, runtime/mod.rs:284-292)
  let proposed ← TrieSplit.expectedProposedSplit facts0.splitGate Lmain.numShards wk.mainShard tMain
    (slotB2.prevStateRoot == NearSpecV3.D2.emptyRoot)
  let lastProps := slotB2.proposals.filterMap decodeProposal
  k { c, w, H, blks, ep, L, wk, Lmain, slotB2, merged, proposed, env, tMain,
      vu := facts0.validatorUpdate, lastProps, receipts, txs := w.txs.zip (c.txValid.map (· != 0)),
      cong := slotB2.congestion }

/-- `INTAKE`, part 2: witness decoding, header decoding, epoch table, layouts, segment bound. -/
def intakeB {β : Type} (driver : ExecutionDriver) (allowCodes : Bool) (c : Claim) (swBytes : Bytes)
    (codes : List Bytes) (k : Intake → Except String β) : Except String β := do
  let w ← driver.decodeWitness swBytes
  check (w.innerBytes == c.chunkInner) "invalid: witness chunk header differs from the claim"
  check (w.epochId == c.epochId) "invalid: epoch id"
  let H ← (decodeChunkInner c.chunkInner).mapError (fun e => s!"invalid claim: {e}")
  check (c.protocolVersion == 86) "out of domain (c.pv86)"
  -- 3.2 chain segment and epoch table
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
  let L ← decodeLayout ep.shardLayout
  for e in c.epochs do
    let l ← decodeLayout e.shardLayout
    if !driver.layoutUnbounded then
      check (1 ≤ l.numShards && l.numShards ≤ 64) "out of domain (c.layout)"
    else
      check (1 ≤ l.numShards) "out of domain (c.layout)"
  check (rsGenesisParamsOk c.rsDataParts c.rsTotalParts) "invalid: Reed-Solomon parameters"
  if !driver.segmentUnbounded then
    check (c.blocks.length ≤ 32) "out of domain (c.segment)"
  intakeC driver allowCodes c codes w H blks ep L k

/-- `INTAKE`: the prefix of `checkReshardCoreObs` (decoding, segment walk, receipt proofs,
pre-state reveal, split gate), verbatim, followed by a continuation. Split into three definitions
only so that the naturality proofs stay linear. -/
def intakeK {β : Type} (driver : ExecutionDriver) (allowCodes : Bool) (claimBytes witnessBytes : Bytes)
    (k : Intake → Except String β) : Except String β := do
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
  intakeB driver allowCodes c swBytes codes k

/-- `FINAL`, first part: the checker's code after the main transition up to the header comparison
(storage bound, gas cap, main post-state root, implicit transitions, outgoing reassignment),
verbatim, followed by a continuation on `(root, congestion, outgoing)`. -/
def finK {β : Type} (driver : ExecutionDriver) (gasCap : Option Nat) (I : Intake) (out : MainOutD2)
    (k : Bytes × Congestion × List Rcpt → Except String β) : Except String β :=
  let c := I.c
  let w := I.w
  let H := I.H
  let blks := I.blks
  let ep := I.ep
  let L := I.L
  let wk := I.wk
  let Lmain := I.Lmain
  let slotB2 := I.slotB2
  let merged := I.merged
  let schedOf (l : Layout) : Except String Scheduler.Params :=
    match Scheduler.Params.calculate Scheduler.Config.pv86 l.numShards with
    | some p => pure p
    | none => throw "invalid: bandwidth scheduler params (assert panics)"
  do
    let baseBytes := (merged.map List.length).foldl (· + ·) 0
    check (driver.sizeOk baseBytes out.cdRemovals)
      "out of domain (w.size): storage-proof upper bound may exceed main_storage_proof_size_soft_limit"
    if let some cap := gasCap then
      check (out.wasmGas ≤ cap) s!"out of domain (e.g_alpha): chunk function-call gas {out.wasmGas} > G_α {cap}"
    let mut root := out.root
    let mut congestion := out.congestion
    check (driver.blindOutputs || root == w.main.postStateRoot) "invalid: main transition post state root"
    -- 3.6 implicit transitions, oldest first
    check (w.implicit.length == wk.transitions.length) "invalid: implicit transitions count"
    let mainProps := out.proposals.map fun p => (p.acct, p.stake)
    let mut facts := c.applyFacts.drop 1
    for (tr, T) in wk.transitions.zip w.implicit do
      let tT := revealTrie T.values root
      match tr with
      | .old i shard =>
        let f ← match facts with | f :: _ => pure f | [] => throw "invalid: apply_facts length"
        facts := facts.drop 1
        let M ← match blks[i]? with | some b => pure b | none => throw "invalid: walk"
        let lM ← layoutOf c M.hdr.epochId
        let ctxM := blockCtx lM shard slotB2.gasLimit M M.hdr.nextGasPrice
        let envM : Env := envOf c ctxM M f.minimumStake (← schedOf lM)
        root ← applyMissingChunkD2 prims envM tT f.validatorUpdate mainProps
      | .split bd mode shard =>
        -- parent layout: the main block's epoch; child layout: the witness epoch's
        -- (`chunk_validation.rs:711-727`)
        let totals ← match mode with
          | .left => pure (0, 0)
          | .right => parentBufferedTotals tT Lmain
        congestion ← childCongestion congestion mode totals shard
        let _ ← match L.index shard with
          | some x => pure x
          | none => throw "invalid: shard not in layout"
        root ← splitRootE tT bd mode
      check (driver.blindOutputs || root == T.postStateRoot) "invalid: implicit transition post state root"
    -- outgoing receipts, reassigned to the witness layout (chunk_validation.rs:620-640)
    let outgoing ← if wk.mainLayout == ep.shardLayout then pure out.outgoing else
      match L.childrenV3 wk.mainShard with
      | some ch =>
        if ch.foldl Nat.min (ch.headD 0) == H.shardId then pure out.outgoing else pure []
      | none => throw "invalid: InvalidSplitShardsIds"
    k (root, congestion, outgoing)

/-- The checker's §3.7 tail (header comparison and the observable), verbatim. -/
def tailOrig (driver : ExecutionDriver) (I : Intake) (out : MainOutD2)
    (t : Bytes × Congestion × List Rcpt) : Except String Observable :=
  let c := I.c
  let w := I.w
  let H := I.H
  let L := I.L
  let slotB2 := I.slotB2
  let proposed := I.proposed
  match t with
  | (root, congestion, outgoing) => do
      -- 3.7 comparison with the endorsed header
      check (driver.blindOutputs || H.prevStateRoot == root) "invalid: InvalidStateRoot"
      check (driver.blindOutputs || H.prevOutcomeRoot == outcomeRootD1 out.outcomes) "invalid: InvalidOutcomesProof"
      check (driver.blindOutputs || H.proposals == out.proposals.map Proposal.encode) "invalid: InvalidValidatorProposals"
      check (H.gasLimit == slotB2.gasLimit) "invalid: InvalidGasLimit"
      check (driver.blindOutputs || H.prevGasUsed == out.gasUsed) "invalid: InvalidGasUsed"
      check (driver.blindOutputs || H.prevBalanceBurnt == out.balanceBurnt) "invalid: InvalidBalanceBurnt"
      check (driver.blindOutputs || H.prevOutgoingReceiptsRoot == driver.outgoingRoot L outgoing) "invalid: InvalidReceiptsProof"
      check (driver.blindOutputs || H.congestion == congestion) "invalid: InvalidCongestionInfo"
      check (driver.blindOutputs || H.bwRequests == out.bwRequests) "invalid: InvalidBandwidthRequests"
      check (H.proposedSplit == proposed) "invalid: InvalidChunkHeaderShardSplit"
      check (H.txRoot == merklizeBorsh (w.newTxs.map TxD2.raw)) "invalid: InvalidTxRoot"
      let body := u32 w.newTxs.length ++ concatAll (w.newTxs.map TxD2.raw) ++ encodeRcpts outgoing
      match encodedMerkleRoot c.rsDataParts c.rsTotalParts body with
      | none => throw "invalid: Reed-Solomon parameters"
      | some (emr, len) =>
        check (driver.blindOutputs || H.encodedMerkleRoot == emr) "invalid: InvalidChunkEncodedMerkleRoot"
        check (driver.blindOutputs || H.encodedLength == len) "invalid: InvalidChunkEncodedLength"
        return { stateRoot := root
                 outcomeRoot := outcomeRootD1 out.outcomes
                 gasBurnt := out.gasUsed
                 balanceBurnt := out.balanceBurnt
                 outgoingReceiptsRoot := driver.outgoingRoot L outgoing
                 proposals := out.proposals.map Proposal.encode
                 txRoot := merklizeBorsh (w.newTxs.map TxD2.raw)
                 encodedMerkleRoot := emr
                 encodedLength := len
                 congestion := congestion
                 bwRequests := out.bwRequests
                 logs := out.outcomes.map (fun o => o.logs) |>.flatten
                 receiptCount := outgoing.length
                 wasmGas := out.wasmGas
                 outcomes := out.outcomes
                 outgoing := outgoing
                 stateChanges := out.committed
                 computeUsage := out.compute
                 detail := out.detail }

/-- **The header outputs** a chunk check computes: every value the checker compares with the
endorsed chunk header. -/
structure Outputs where
  stateRoot : Bytes
  outcomeRoot : Bytes
  proposals : List Bytes
  gasLimit : Nat
  gasUsed : Nat
  balanceBurnt : Nat
  outgoingRoot : Bytes
  congestion : Congestion
  bwRequests : List BwRequest
  proposedSplit : Option Bytes
  txRoot : Bytes
  encodedMerkleRoot : Bytes
  encodedLength : Nat

/-- `FINAL`, second part: compute the outputs (Reed–Solomon encoding of the chunk body included). -/
def tailNew (driver : ExecutionDriver) (I : Intake) (out : MainOutD2)
    (t : Bytes × Congestion × List Rcpt) : Except String Outputs :=
  match t with
  | (root, congestion, outgoing) =>
    let w := I.w
    let body := u32 w.newTxs.length ++ concatAll (w.newTxs.map TxD2.raw) ++ encodeRcpts outgoing
    match encodedMerkleRoot I.c.rsDataParts I.c.rsTotalParts body with
    | none => throw "invalid: Reed-Solomon parameters"
    | some (emr, len) =>
      pure { stateRoot := root, outcomeRoot := outcomeRootD1 out.outcomes,
             proposals := out.proposals.map Proposal.encode, gasLimit := I.slotB2.gasLimit,
             gasUsed := out.gasUsed, balanceBurnt := out.balanceBurnt,
             outgoingRoot := driver.outgoingRoot I.L outgoing, congestion, bwRequests := out.bwRequests,
             proposedSplit := I.proposed, txRoot := merklizeBorsh (w.newTxs.map TxD2.raw),
             encodedMerkleRoot := emr, encodedLength := len }

/-- **`FinalOut`: the public check.** The computed outputs equal the endorsed chunk header's fields.
`H` is the decoded `chunk_inner` of the public statement. -/
def headerOk (H : ChunkInner) (o : Outputs) : Bool :=
  (H.prevStateRoot == o.stateRoot) && (H.prevOutcomeRoot == o.outcomeRoot) &&
  (H.proposals == o.proposals) && (H.gasLimit == o.gasLimit) && (H.prevGasUsed == o.gasUsed) &&
  (H.prevBalanceBurnt == o.balanceBurnt) && (H.prevOutgoingReceiptsRoot == o.outgoingRoot) &&
  (H.congestion == o.congestion) && (H.bwRequests == o.bwRequests) &&
  (H.proposedSplit == o.proposedSplit) && (H.txRoot == o.txRoot) &&
  (H.encodedMerkleRoot == o.encodedMerkleRoot) && (H.encodedLength == o.encodedLength)

/-! ## The checker is intake, engine, final (verbatim) -/

/-- **`checkReshardCoreObs` is the composition of its slices**, by `rfl`: the intake and final
slices are the checker's own code. -/
theorem checkReshardCoreObs_split (driver : ExecutionDriver) (hooks : ActionHooks)
    (allowCodes : Bool) (cb wb : Bytes) (gasCap : Option Nat) :
    checkReshardCoreObs driver hooks allowCodes cb wb gasCap =
      intakeK driver allowCodes cb wb fun I =>
        driver.apply hooks prims I.env I.tMain I.vu I.lastProps I.receipts I.txs I.cong >>= fun out =>
          finK driver gasCap I out (tailOrig driver I out) := by
  rfl

theorem intakeC_nat {β γ : Type} (driver : ExecutionDriver) (allowCodes : Bool) (c : Claim)
    (codes : List Bytes) (w : StateWitnessD2) (H : ChunkInner) (blks : List Blk) (ep : EpochRec)
    (L : Layout) (k : Intake → Except String β) (g : β → Except String γ) :
    intakeC driver allowCodes c codes w H blks ep L k >>= g =
      intakeC driver allowCodes c codes w H blks ep L (fun I => k I >>= g) := by
  unfold intakeC
  nat_walk

theorem intakeB_nat {β γ : Type} (driver : ExecutionDriver) (allowCodes : Bool) (c : Claim)
    (swBytes : Bytes) (codes : List Bytes) (k : Intake → Except String β) (g : β → Except String γ) :
    intakeB driver allowCodes c swBytes codes k >>= g =
      intakeB driver allowCodes c swBytes codes (fun I => k I >>= g) := by
  unfold intakeB
  nat_walk
  all_goals exact intakeC_nat _ _ _ _ _ _ _ _ _ _ _

theorem intakeK_nat {β γ : Type} (driver : ExecutionDriver) (allowCodes : Bool) (cb wb : Bytes)
    (k : Intake → Except String β) (g : β → Except String γ) :
    intakeK driver allowCodes cb wb k >>= g = intakeK driver allowCodes cb wb (fun I => k I >>= g) := by
  unfold intakeK
  nat_walk
  all_goals exact intakeB_nat _ _ _ _ _ _ _

theorem finK_nat {β γ : Type} (driver : ExecutionDriver) (gasCap : Option Nat) (I : Intake)
    (out : MainOutD2) (k : Bytes × Congestion × List Rcpt → Except String β) (g : β → Except String γ) :
    finK driver gasCap I out k >>= g = finK driver gasCap I out (fun t => k t >>= g) := by
  unfold finK
  nat_walk

theorem except_bind_ok {α β : Type} (x : Except String α) (f : α → Except String β) (b : β) :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  rcases x with e | a
  · simp only [reduceCtorEq, false_and, exists_false, iff_false]; intro h; cases h
  · simp only [Except.ok.injEq, exists_eq_left']; rfl

theorem bind_pure_comp_ok {α : Type} (x : Except String α) :
    (x >>= fun a => (pure a : Except String α)) = x := by
  rcases x <;> rfl

theorem check_bind_ok {β : Type} (b : Bool) (m : String) (f : Unit → Except String β) (x : β) :
    (check b m >>= f) = .ok x ↔ b = true ∧ f () = .ok x := by
  cases b
  · simp only [check, Bool.false_eq_true, false_and, iff_false]; intro h; cases h
  · simp only [check, true_and]; rfl

/-- The header comparison of the checker accepts iff the computed outputs exist and match. -/
theorem tailOrig_ok_iff (driver : ExecutionDriver) (hb : driver.blindOutputs = false) (I : Intake)
    (out : MainOutD2) (t : Bytes × Congestion × List Rcpt) :
    (∃ obs, tailOrig driver I out t = .ok obs) ↔
      ∃ o, tailNew driver I out t = .ok o ∧ headerOk I.H o = true := by
  obtain ⟨root, congestion, outgoing⟩ := t
  simp only [tailOrig, tailNew, hb, Bool.false_or]
  split
  · simp only [check_bind_ok]
    constructor
    · rintro ⟨obs, -, -, -, -, -, -, -, -, -, -, -, h⟩; cases h
    · rintro ⟨o, h, -⟩; cases h
  · rename_i emr len _
    simp only [check_bind_ok, headerOk, Bool.and_eq_true]
    constructor
    · rintro ⟨obs, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -⟩
      exact ⟨_, rfl, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩⟩
    · rintro ⟨o, ho, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩⟩
      cases ho
      exact ⟨_, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, rfl⟩

/-! ## The chunk machine `CM` at the `allFeatures` configuration -/

/-- The `allFeatures` configuration (owner decision D-1). -/
abbrev afCfg : ProtocolCfg := Tier.cfg .allFeatures

/-- The whole-state driver `checkSuccessor` builds at `allFeatures`. -/
def afDriver : ExecutionDriver := successorDriver afCfg

/-- The action hooks `checkSuccessor` passes at `allFeatures`. -/
def afHooks : ActionHooks := D3.d3Hooks afCfg.wasm

/-- The engine program of an intake record. -/
def Intake.prog (I : Intake) : Prog :=
  Prog.ofRun afCfg.wasm prims I.env I.tMain I.vu I.lastProps I.receipts I.txs I.cong
    afCfg.globalActions (if afCfg.completeCodeWitness then .complete else .coldPartial)

/-- A configuration of `CM`. -/
inductive Conf where
  /-- Claim and witness bytes, before intake. -/
  | init (cb wb : Bytes)
  /-- Main transition in progress: intake record and engine configuration. -/
  | eng (I : Intake) (c : EConf)
  /-- Main transition finished with `out`. -/
  | fin (I : Intake) (out : MainOutD2)
  /-- Final: the endorsed header `H` (from the claim) and the computed outputs `o`. -/
  | done (H : ChunkInner) (o : Outputs)
  /-- Final: a genesis-containing segment, decided atomically and accepted. -/
  | doneG

/-- **The step relation of `CM`** (a function: `CM` is deterministic). -/
def CM.step : Conf → Except String Conf
  | .init cb wb =>
    if segmentHasGenesis cb then
      (checkD2CoreGWith afDriver afHooks true cb wb afCfg.gasCap).map fun _ => .doneG
    else intakeK afDriver true cb wb fun I => pure (.eng I ⟨.start, initRec afCfg.wasm I.env⟩)
  | .eng I c =>
    match c.pos with
    | .done out => pure (.fin I out)
    | _ => (estep I.prog c).map (.eng I)
  | .fin I out => (finK afDriver afCfg.gasCap I out (tailNew afDriver I out)).map (.done I.H)
  | .done H o => pure (.done H o)
  | .doneG => pure .doneG

/-- Runs of `CM` (reflexive-transitive closure of `step`). -/
inductive Steps : Conf → Conf → Prop
  | refl (c : Conf) : Steps c c
  | step {a b c : Conf} : CM.step a = .ok b → Steps b c → Steps a c

/-- Runs of `CM` with their length: the global clock. -/
inductive StepsN : Nat → Conf → Conf → Prop
  | refl (c : Conf) : StepsN 0 c c
  | step {n : Nat} {a b c : Conf} : CM.step a = .ok b → StepsN n b c → StepsN (n + 1) a c

/-- The accepting configurations: `FinalOut` holds (`headerOk`), or the atomic genesis path. -/
def Conf.accepting : Conf → Bool
  | .done H o => headerOk H o
  | .doneG => true
  | _ => false

/-- **`CM` accepts `(claim, witness)`**: a run from `init` reaches an accepting configuration. -/
def CMAccepts (cb wb : Bytes) : Prop := ∃ cf, Steps (.init cb wb) cf ∧ cf.accepting = true

/-! ### Chaining (segment composition) -/

theorem Steps.trans {a b c : Conf} (h1 : Steps a b) (h2 : Steps b c) : Steps a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact .step h (ih h2)

theorem StepsN.trans {n m : Nat} {a b c : Conf} (h1 : StepsN n a b) (h2 : StepsN m b c) :
    StepsN (n + m) a c := by
  induction h1 with
  | refl => simpa using h2
  | @step n a b c' h _ ih =>
    have := StepsN.step h (ih h2)
    rwa [show n + 1 + m = n + m + 1 by omega]

theorem steps_iff_stepsN {a b : Conf} : Steps a b ↔ ∃ n, StepsN n a b := by
  constructor
  · intro h
    induction h with
    | refl c => exact ⟨0, .refl c⟩
    | step h _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .step h hn⟩
  · rintro ⟨n, h⟩
    induction h with
    | refl c => exact .refl c
    | step h _ ih => exact .step h ih

/-- Boundaries of a list of segments match: segment `i` ends where segment `i+1` starts. -/
def Chained : Conf → List (Conf × Conf) → Conf → Prop
  | a, [], b => a = b
  | a, s :: rest, b => a = s.1 ∧ Chained s.2 rest b

/-- **Segment chaining.** Any list of runs whose boundaries match composes into one run. -/
theorem steps_of_chain : ∀ (segs : List (Conf × Conf)) (a b : Conf),
    (∀ s ∈ segs, Steps s.1 s.2) → Chained a segs b → Steps a b
  | [], a, b, _, h => by cases h; exact .refl _
  | s :: rest, a, b, hs, ⟨h1, h2⟩ => by
    subst h1
    exact (hs s (by simp)).trans
      (steps_of_chain rest s.2 b (fun x hx => hs x (by simp [hx])) h2)

/-- The clocked form: segment lengths add up. -/
theorem stepsN_of_chain : ∀ (segs : List (Nat × Conf × Conf)) (a b : Conf),
    (∀ s ∈ segs, StepsN s.1 s.2.1 s.2.2) →
    Chained a (segs.map (·.2)) b → StepsN (segs.map (·.1)).sum a b
  | [], a, b, _, h => by cases h; exact .refl _
  | s :: rest, a, b, hs, ⟨h1, h2⟩ => by
    simp only [List.map_cons, List.sum_cons] at h1 h2 ⊢
    subst h1
    exact (hs s (by simp)).trans
      (stepsN_of_chain rest s.2.2 b (fun x hx => hs x (by simp [hx])) h2)

/-! ### Run decomposition -/

theorem steps_done {H : ChunkInner} {o : Outputs} {cf : Conf} (h : Steps (.done H o) cf) :
    cf = .done H o := by
  generalize hx : Conf.done H o = x at h
  induction h with
  | refl => rfl
  | step hs _ ih => subst hx; simp only [CM.step] at hs; cases hs; exact ih rfl

theorem steps_doneG {cf : Conf} (h : Steps .doneG cf) : cf = .doneG := by
  generalize hx : Conf.doneG = x at h
  induction h with
  | refl => rfl
  | step hs _ ih => subst hx; simp only [CM.step] at hs; cases hs; exact ih rfl

/-- An engine run lifts to a `CM` run. -/
theorem steps_eng_of_esteps (I : Intake) {c c' : EConf} (h : ESteps I.prog c c') :
    Steps (.eng I c) (.eng I c') := by
  induction h with
  | refl => exact .refl _
  | @step a b c hs _ ih =>
    rcases a with ⟨pos, st⟩
    cases pos with
    | done out =>
      have : b = ⟨.done out, st⟩ := by
        unfold estep at hs; simp only [stepM] at hs; cases hs; rfl
      subst this; exact ih
    | _ =>
      exact .step (by simp only [CM.step, hs]; rfl) ih

/-- An accepting run from a main-transition configuration passes through the engine's `done`. -/
theorem eng_decomp (I : Intake) {c : EConf} {cf : Conf} (h : Steps (.eng I c) cf)
    (ha : cf.accepting = true) :
    ∃ out st, ESteps I.prog c ⟨.done out, st⟩ ∧ Steps (.fin I out) cf := by
  generalize hx : Conf.eng I c = x at h
  induction h generalizing c with
  | refl => subst hx; simp [Conf.accepting] at ha
  | @step a b d hs hrest ih =>
    subst hx
    rcases c with ⟨pos, st⟩
    cases pos with
    | done out =>
      simp only [CM.step] at hs; cases hs
      exact ⟨out, st, .refl _, hrest⟩
    | _ =>
      simp only [CM.step] at hs
      rcases he : estep I.prog _ with e | c1 <;> rw [he] at hs <;> simp [Except.map] at hs
      subst hs
      obtain ⟨out, st', h1, h2⟩ := ih ha rfl
      exact ⟨out, st', .step he h1, h2⟩

theorem fin_accepts_iff (I : Intake) (out : MainOutD2) :
    (∃ cf, Steps (.fin I out) cf ∧ cf.accepting = true) ↔
      ∃ o, (finK afDriver afCfg.gasCap I out (tailNew afDriver I out)) = .ok o ∧
        headerOk I.H o = true := by
  constructor
  · rintro ⟨cf, h, ha⟩
    cases h with
    | refl => simp [Conf.accepting] at ha
    | step hs hrest =>
      simp only [CM.step] at hs
      rcases he : finK afDriver afCfg.gasCap I out (tailNew afDriver I out) with e | o <;>
        rw [he] at hs <;> simp [Except.map] at hs
      subst hs
      have := steps_done hrest
      subst this
      exact ⟨o, rfl, ha⟩
  · rintro ⟨o, ho, hok⟩
    exact ⟨.done I.H o, .step (by simp only [CM.step, ho]; rfl) (.refl _), hok⟩

/-! ### `CM` is `checkSuccessor` at `allFeatures` -/

theorem except_map_eq_bind {α β : Type} (f : α → β) (x : Except String α) :
    x.map f = (x >>= fun a => pure (f a)) := by
  rcases x <;> rfl

theorem checkSuccessor_af (cb wb : Bytes) :
    checkSuccessor afCfg cb wb =
      if segmentHasGenesis cb then checkD2CoreGWith afDriver afHooks true cb wb afCfg.gasCap
      else checkReshardCore afDriver afHooks true cb wb afCfg.gasCap := by
  cases h : segmentHasGenesis cb <;> simp [checkSuccessor, h, afDriver, afHooks, successorDriver] <;> rfl

theorem afDriver_apply (h : ActionHooks) (p : Prims) (e : Env) (t : PTrie) (vu : Option ValidatorUpdateFacts)
    (ps : List (Bytes × Nat)) (rs : List Rcpt) (txs : List (TxD2 × Bool)) (cg : Congestion) :
    afDriver.apply h p e t vu ps rs txs cg =
      StorageExecution.run afCfg.wasm p e t vu ps rs txs cg afCfg.globalActions
        (if afCfg.completeCodeWitness then .complete else .coldPartial) := rfl

theorem afDriver_blind : afDriver.blindOutputs = false := rfl

/-- **Obligation 3 (the small-step factorisation), proved.** The `allFeatures` relation holds iff
the chunk machine, run from `init(claim, witness)`, reaches a configuration whose computed outputs
pass `FinalOut` (`headerOk`) against the claim's chunk header. -/
theorem cm_iff (cb wb : Bytes) : Tier.rel .allFeatures cb wb ↔ CMAccepts cb wb := by
  unfold Tier.rel Tier.checker CMAccepts
  rw [checkSuccessor_af]
  by_cases hg : segmentHasGenesis cb = true
  · -- atomic genesis path
    simp only [hg, ite_true]
    constructor
    · intro h
      exact ⟨.doneG, .step (by simp only [CM.step, hg, ite_true, h]; rfl) (.refl _), rfl⟩
    · rintro ⟨cf, hs, ha⟩
      cases hs with
      | refl => simp [Conf.accepting] at ha
      | step h1 _ =>
        simp only [CM.step, hg, ite_true] at h1
        rcases he : checkD2CoreGWith afDriver afHooks true cb wb afCfg.gasCap with e | u <;>
          rw [he] at h1 <;> simp [Except.map] at h1
        all_goals (cases u; exact he)
  · simp only [hg, Bool.false_eq_true, ite_false]
    have hg' : segmentHasGenesis cb = false := by simpa using hg
    unfold checkReshardCore
    rw [checkReshardCoreObs_split]
    -- the checker side
    have hL : (intakeK afDriver true cb wb fun I =>
        afDriver.apply afHooks prims I.env I.tMain I.vu I.lastProps I.receipts I.txs I.cong >>= fun out =>
          finK afDriver afCfg.gasCap I out (tailOrig afDriver I out)) =
        (intakeK afDriver true cb wb pure >>= fun I =>
          afDriver.apply afHooks prims I.env I.tMain I.vu I.lastProps I.receipts I.txs I.cong >>= fun out =>
            finK afDriver afCfg.gasCap I out pure >>= tailOrig afDriver I out) := by
      rw [intakeK_nat]
      simp only [pure_bind, finK_nat]
    -- the machine side: the first step is the intake
    have hR : CM.step (.init cb wb) =
        (intakeK afDriver true cb wb pure).map fun I => .eng I ⟨.start, initRec afCfg.wasm I.env⟩ := by
      simp only [CM.step, hg', Bool.false_eq_true, ite_false]
      rw [except_map_eq_bind, intakeK_nat]
      simp only [pure_bind]
    rw [hL]
    constructor
    · intro h
      rcases hx : (intakeK afDriver true cb wb pure >>= fun I =>
          afDriver.apply afHooks prims I.env I.tMain I.vu I.lastProps I.receipts I.txs I.cong >>= fun out =>
            finK afDriver afCfg.gasCap I out pure >>= tailOrig afDriver I out) with e | obs <;>
        rw [hx] at h <;> simp [Except.map] at h
      obtain ⟨I, hI, hrest⟩ := (except_bind_ok _ _ _).1 hx
      obtain ⟨out, hout, hfin⟩ := (except_bind_ok _ _ _).1 hrest
      obtain ⟨t, ht, htail⟩ := (except_bind_ok _ _ _).1 hfin
      obtain ⟨o, ho, hok⟩ := (tailOrig_ok_iff afDriver afDriver_blind I out t).1 ⟨obs, htail⟩
      rw [afDriver_apply, engine_run_ok_iff] at hout
      obtain ⟨st', hrun⟩ := hout
      have hfin' : finK afDriver afCfg.gasCap I out (tailNew afDriver I out) = .ok o := by
        rw [show tailNew afDriver I out = fun t => pure t >>= tailNew afDriver I out from
          funext fun _ => (pure_bind _ _).symm, ← finK_nat, ht]
        exact ho
      obtain ⟨cf, hcf, hacc⟩ := (fin_accepts_iff I out).2 ⟨o, hfin', hok⟩
      refine ⟨cf, .step (by rw [hR, hI]; rfl) ?_, hacc⟩
      exact (steps_eng_of_esteps I hrun).trans (.step (by simp only [CM.step]; rfl) hcf)
    · rintro ⟨cf, hs, ha⟩
      cases hs with
      | refl => simp [Conf.accepting] at ha
      | @step _ b _ h1 hrest =>
        rw [hR] at h1
        rcases hI : intakeK afDriver true cb wb pure with e | I <;> rw [hI] at h1 <;>
          simp [Except.map] at h1
        subst h1
        obtain ⟨out, st', hrun, hfin⟩ := eng_decomp I hrest ha
        obtain ⟨o, ho, hok⟩ := (fin_accepts_iff I out).1 ⟨cf, hfin, ha⟩
        have hout : afDriver.apply afHooks prims I.env I.tMain I.vu I.lastProps I.receipts I.txs I.cong
            = .ok out := by
          rw [afDriver_apply, engine_run_ok_iff]; exact ⟨st', hrun⟩
        rw [show tailNew afDriver I out = fun t => pure t >>= tailNew afDriver I out from
          funext fun _ => (pure_bind _ _).symm, ← finK_nat] at ho
        obtain ⟨t, ht, htn⟩ := (except_bind_ok _ _ _).1 ho
        obtain ⟨obs, hobs⟩ := (tailOrig_ok_iff afDriver afDriver_blind I out t).2 ⟨o, htn, hok⟩
        have hX := (except_bind_ok _ (fun out =>
            finK afDriver afCfg.gasCap I out pure >>= tailOrig afDriver I out) obs).2
          ⟨out, hout, (except_bind_ok _ _ obs).2 ⟨t, ht, hobs⟩⟩
        exact (congrArg (Except.map (fun _ => ())) hX).trans rfl

#print axioms cm_iff
#print axioms steps_of_chain
#print axioms stepsN_of_chain
end NearSpecV3.E2E
