import NearSpecV3.E2E.Engine
import NearSpecV3.Successor.Config

set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false

/-!
# E2E-M11c, part 1: the intake record and the slices of the genesis-capable checker

`CM` (`Machine.lean`) runs the checker as verbatim slices joined by continuations. M11 sliced the
non-genesis path (`checkReshardCoreObs`); this file slices the path `checkSuccessor` takes when the
claim's segment contains a genesis block, `checkD2CoreGWith`, so that it too is cut into `INTAKE`,
engine steps and `FINAL` instead of one atomic step.

`checkD2CoreGWith` has two branches after its prefix (`gPrefixK`, up to the main block `B2`):

* **`B2` is not genesis** (a genesis block is a source block further back). The checker delegates to
  `checkD2CoreWith`, i.e. `checkD2CoreWithObs`. That function is sliced like the non-genesis path:
  `d2IntakeK`/`d2IntakeB`/`d2IntakeC` (decoding, segment walk, receipt proofs, pre-state reveal)
  produce an `Intake` record whose main transition is the same engine program (`Intake.prog`), so
  the engine steps — and the mid-call cuts of `Refined.lean` — apply unchanged; `finD2K` (storage
  bound, gas cap, post-state root, implicit transitions) and `tailD2Orig` (the header comparison)
  are its `FINAL`. The record carries `d2 = some ⟨b2i, sched⟩`, which selects this `FINAL`.
* **`B2` is genesis.** There is no main transition: the stored genesis chunk extra is the main
  transition's result. `genAK` (the genesis intake: chunk extra, source blocks, receipt checks, the
  root) and `genB` (implicit transitions on the genesis root, the header comparison) are the two
  steps.

Each split is `rfl` (`checkD2CoreGWith_split`, `checkD2CoreWithObs_split`), so the slices are the
checker's own code. Naturality (`…_nat`) lets a continuation be pulled out of a slice.
-/

namespace NearSpecV3.E2E
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged NearSpecV3.Wasm
open NearSpecV3.Successor

/-- The data the D2 `FINAL` reads beyond the intake record: the main block's index (the implicit
transitions are the blocks before it) and the bandwidth-scheduler parameters. -/
structure D2Fin where
  b2i : Nat
  sched : Scheduler.Params

/-- The intake record: everything the checker's prefix computes that its main transition and its
final part read. `d2 = none` on the non-genesis path (`checkReshardCoreObs`'s `FINAL`), `some` on
the delegated genesis-segment path (`checkD2CoreWithObs`'s `FINAL`). -/
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
  d2 : Option D2Fin := none

/-! ## `checkD2CoreGWith`: the prefix

The slices are cut after each `if … then` without `else`: the do-notation turns the code after such
an `if` into a join point, and unfolding join points duplicates the rest of the block, so each slice
ends in a call to the next one (the same reason `Machine.lean` cuts `intakeK`). -/

/-- What the genesis-capable prefix computes. -/
structure GPre where
  c : Claim
  codes : List Bytes
  w : StateWitnessD2
  H : ChunkInner
  blks : List Blk
  ep : EpochRec
  L : Layout
  idx : Nat
  b2i : Nat
  B2 : Blk

/-- The prefix, part 3: epoch flags, hash links, the main block `B2`. -/
def gPrefixC {β : Type} (driver : ExecutionDriver) (c : Claim) (codes : List Bytes)
    (w : StateWitnessD2) (H : ChunkInner) (blks : List Blk) (ep : EpochRec) (L : Layout)
    (k : GPre → Except String β) : Except String β := do
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
  k { c, codes, w, H, blks, ep, L, idx, b2i, B2 }

/-- The prefix, part 2: witness, header, epoch table, layout, segment bound. -/
def gPrefixB {β : Type} (driver : ExecutionDriver) (c : Claim) (swBytes : Bytes)
    (codes : List Bytes) (k : GPre → Except String β) : Except String β := do
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
  gPrefixC driver c codes w H blks ep L k

/-- **The prefix of `checkD2CoreGWith`** (decoding, epoch table, segment, the main block `B2`),
verbatim, followed by a continuation. -/
def gPrefixK {β : Type} (driver : ExecutionDriver) (allowCodes : Bool) (claimBytes witnessBytes : Bytes)
    (k : GPre → Except String β) : Except String β := do
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
  gPrefixB driver c swBytes codes k

/-- What the genesis intake computes: the genesis chunk extra (`gen`), the root it sets, and what
the implicit transitions and the header comparison read. -/
structure GFin where
  c : Claim
  w : StateWitnessD2
  H : ChunkInner
  blks : List Blk
  L : Layout
  B2 : Blk
  slotB2 : ChunkInner
  sched : Scheduler.Params
  implicitIdx : List Nat
  gen : Option ChunkExtra
  root : Bytes

/-- The genesis intake, part 3: scheduler, environment, the root (the stored chunk extra's). -/
def genAC {β : Type} (driver : ExecutionDriver) (hooks : ActionHooks) (allowCodes : Bool)
    (gasCap : Option Nat) (g : GPre) (gen? : Option ChunkExtra) (implicitIdx : List Nat)
    (slotB2 : ChunkInner) (receipts : List Rcpt) (k : GFin → Except String β) : Except String β :=
  let c := g.c
  let codes := g.codes
  let w := g.w
  let H := g.H
  let blks := g.blks
  let ep := g.ep
  let L := g.L
  let idx := g.idx
  let b2i := g.b2i
  let B2 := g.B2
  let isNew := fun (b : Blk) => match b.slots[idx]? with
    | some (s, _) => s.heightIncluded == b.hdr.height
    | none => false
  do
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
  k { c, w, H, blks, L, B2, slotB2, sched, implicitIdx, gen := gen?, root }

/-- The genesis intake, part 2: the walk stop, source blocks and their receipts, transactions. -/
def genAB {β : Type} (driver : ExecutionDriver) (hooks : ActionHooks) (allowCodes : Bool)
    (gasCap : Option Nat) (g : GPre) (gen? : Option ChunkExtra) (k : GFin → Except String β) :
    Except String β :=
  let c := g.c
  let codes := g.codes
  let w := g.w
  let H := g.H
  let blks := g.blks
  let ep := g.ep
  let L := g.L
  let idx := g.idx
  let b2i := g.b2i
  let B2 := g.B2
  let isNew := fun (b : Blk) => match b.slots[idx]? with
    | some (s, _) => s.heightIncluded == b.hdr.height
    | none => false
  do
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
  genAC driver hooks allowCodes gasCap g gen? implicitIdx slotB2 receipts k

/-- **The genesis `INTAKE`** (`B2` genesis): the genesis chunk extra, the source blocks and their
receipt checks, the transactions, and the root the main transition leaves (the stored chunk
extra's), verbatim, followed by a continuation. -/
def genAK {β : Type} (driver : ExecutionDriver) (hooks : ActionHooks) (allowCodes : Bool)
    (gasCap : Option Nat) (g : GPre) (k : GFin → Except String β) : Except String β :=
  let c := g.c
  let codes := g.codes
  let w := g.w
  let H := g.H
  let blks := g.blks
  let ep := g.ep
  let L := g.L
  let idx := g.idx
  let b2i := g.b2i
  let B2 := g.B2
  let isNew := fun (b : Blk) => match b.slots[idx]? with
    | some (s, _) => s.heightIncluded == b.hdr.height
    | none => false
  do
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
  genAB driver hooks allowCodes gasCap g gen? k

/-- **The genesis `FINAL`**: implicit transitions on the genesis root and the header comparison,
verbatim. -/
def genB (g : GFin) : Except String Unit :=
  let c := g.c
  let w := g.w
  let H := g.H
  let blks := g.blks
  let L := g.L
  let B2 := g.B2
  let slotB2 := g.slotB2
  let sched := g.sched
  let implicitIdx := g.implicitIdx
  let gen? := g.gen
  do
  let mut root := g.root
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

/-- The rest of `checkD2CoreGWith` after its prefix, verbatim: the delegation to
`checkD2CoreWith` when `B2` is not genesis, else the genesis branch. -/
def gRest (driver : ExecutionDriver) (hooks : ActionHooks) (allowCodes : Bool)
    (claimBytes witnessBytes : Bytes) (gasCap : Option Nat) (g : GPre) : Except String Unit :=
  let c := g.c
  let codes := g.codes
  let w := g.w
  let H := g.H
  let blks := g.blks
  let ep := g.ep
  let L := g.L
  let idx := g.idx
  let b2i := g.b2i
  let B2 := g.B2
  let isNew := fun (b : Blk) => match b.slots[idx]? with
    | some (s, _) => s.heightIncluded == b.hdr.height
    | none => false
  do
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

/-! ## `checkD2CoreWithObs`: intake, `FINAL` -/

/-- `checkD2CoreWithObs`'s `INTAKE`, part 5: transactions, the walk, receipt proofs, pre-state
reveal, followed by a continuation on the intake record and the `FINAL` data. -/
def d2IntakeE {β : Type} (driver : ExecutionDriver) (c : Claim) (codes : List Bytes)
    (w : StateWitnessD2) (H : ChunkInner) (blks : List Blk) (ep : EpochRec) (L : Layout)
    (k : Intake → D2Fin → Except String β) : Except String β := do
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
  k { c, w, H, blks, ep, L, wk := ⟨b2i, H.shardId, ep.shardLayout, [], [], stop⟩, Lmain := L, slotB2,
      merged, proposed := none, env, tMain, vu := facts0.validatorUpdate, lastProps, receipts,
      txs := w.txs.zip (c.txValid.map (· != 0)), cong := slotB2.congestion,
      d2 := some ⟨b2i, sched⟩ } ⟨b2i, sched⟩

/-- `checkD2CoreWithObs`'s `INTAKE`, part 4: epoch flags, split gate. -/
def d2IntakeD {β : Type} (driver : ExecutionDriver) (c : Claim) (codes : List Bytes)
    (w : StateWitnessD2) (H : ChunkInner) (blks : List Blk) (ep : EpochRec) (L : Layout)
    (k : Intake → D2Fin → Except String β) : Except String β := do
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
  d2IntakeE driver c codes w H blks ep L k

/-- `checkD2CoreWithObs`'s `INTAKE`, part 3: epoch table, layout, segment bound. -/
def d2IntakeC {β : Type} (driver : ExecutionDriver) (c : Claim) (codes : List Bytes)
    (w : StateWitnessD2) (H : ChunkInner) (k : Intake → D2Fin → Except String β) :
    Except String β := do
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
  d2IntakeD driver c codes w H blks ep L k

/-- `checkD2CoreWithObs`'s `INTAKE`, part 2: witness and header decoding. -/
def d2IntakeB {β : Type} (driver : ExecutionDriver) (c : Claim) (swBytes : Bytes)
    (codes : List Bytes) (k : Intake → D2Fin → Except String β) : Except String β := do
  let w ← driver.decodeWitness swBytes
  check (w.innerBytes == c.chunkInner) "invalid: witness chunk header differs from the claim"
  check (w.epochId == c.epochId) "invalid: epoch id"
  let H ← (decodeChunkInner c.chunkInner).mapError (fun e => s!"invalid claim: {e}")
  d2IntakeC driver c codes w H k

/-- `checkD2CoreWithObs`'s `INTAKE`, part 1: claim and witness-file decoding. -/
def d2IntakeK {β : Type} (driver : ExecutionDriver) (allowCodes : Bool) (claimBytes witnessBytes : Bytes)
    (k : Intake → D2Fin → Except String β) : Except String β := do
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
  d2IntakeB driver c swBytes codes k

/-- `checkD2CoreWithObs`'s `FINAL`, first part: storage bound, gas cap, post-state root, implicit
transitions, verbatim, followed by a continuation on the root. -/
def finD2K {β : Type} (driver : ExecutionDriver) (gasCap : Option Nat) (I : Intake) (d : D2Fin)
    (out : MainOutD2) (k : Bytes → Except String β) : Except String β :=
  let c := I.c
  let w := I.w
  let H := I.H
  let blks := I.blks
  let L := I.L
  let slotB2 := I.slotB2
  let merged := I.merged
  let b2i := d.b2i
  let sched := d.sched
  let implicitIdx := (List.range b2i).reverse
  do
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
  k root

/-- `checkD2CoreWithObs`'s header comparison and observable, verbatim. -/
def tailD2Orig (driver : ExecutionDriver) (I : Intake) (out : MainOutD2) (root : Bytes) :
    Except String Observable :=
  let c := I.c
  let w := I.w
  let H := I.H
  let L := I.L
  let slotB2 := I.slotB2
  do
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

/-! ## The splits are the checker's code -/

/-- **`checkD2CoreGWith` is its prefix followed by the rest**, by `rfl`. -/
theorem checkD2CoreGWith_split (driver : ExecutionDriver) (hooks : ActionHooks) (allowCodes : Bool)
    (cb wb : Bytes) (gasCap : Option Nat) :
    checkD2CoreGWith driver hooks allowCodes cb wb gasCap =
      gPrefixK driver allowCodes cb wb (gRest driver hooks allowCodes cb wb gasCap) := by
  rfl

/-- **The rest is the delegation or the genesis branch** (`genAK` then `genB`). -/
theorem gRest_eq (driver : ExecutionDriver) (hooks : ActionHooks) (allowCodes : Bool)
    (cb wb : Bytes) (gasCap : Option Nat) (g : GPre) :
    gRest driver hooks allowCodes cb wb gasCap g =
      if !g.B2.isGenesis then checkD2CoreWith driver hooks allowCodes cb wb gasCap
      else genAK driver hooks allowCodes gasCap g genB := by
  rfl

/-- **`checkD2CoreWithObs` is intake, the engine run, and its `FINAL`**, by `rfl`. -/
theorem checkD2CoreWithObs_split (driver : ExecutionDriver) (hooks : ActionHooks) (allowCodes : Bool)
    (cb wb : Bytes) (gasCap : Option Nat) :
    checkD2CoreWithObs driver hooks allowCodes cb wb gasCap =
      d2IntakeK driver allowCodes cb wb fun I d =>
        driver.apply hooks prims I.env I.tMain I.vu I.lastProps I.receipts I.txs I.cong >>= fun out =>
          finD2K driver gasCap I d out (tailD2Orig driver I out) := by
  rfl

/-! ## Naturality: a continuation can be pulled out of a slice -/

theorem gPrefixC_nat {β γ : Type} (driver : ExecutionDriver) (c : Claim) (codes : List Bytes)
    (w : StateWitnessD2) (H : ChunkInner) (blks : List Blk) (ep : EpochRec) (L : Layout)
    (k : GPre → Except String β) (g : β → Except String γ) :
    gPrefixC driver c codes w H blks ep L k >>= g =
      gPrefixC driver c codes w H blks ep L (fun x => k x >>= g) := by
  unfold gPrefixC
  nat_walk

theorem gPrefixB_nat {β γ : Type} (driver : ExecutionDriver) (c : Claim) (swBytes : Bytes)
    (codes : List Bytes) (k : GPre → Except String β) (g : β → Except String γ) :
    gPrefixB driver c swBytes codes k >>= g = gPrefixB driver c swBytes codes (fun x => k x >>= g) := by
  unfold gPrefixB
  nat_walk
  all_goals exact gPrefixC_nat _ _ _ _ _ _ _ _ _ _

theorem gPrefixK_nat {β γ : Type} (driver : ExecutionDriver) (allowCodes : Bool) (cb wb : Bytes)
    (k : GPre → Except String β) (g : β → Except String γ) :
    gPrefixK driver allowCodes cb wb k >>= g = gPrefixK driver allowCodes cb wb (fun x => k x >>= g) := by
  unfold gPrefixK
  nat_walk
  all_goals exact gPrefixB_nat _ _ _ _ _ _

theorem genAC_nat {β γ : Type} (driver : ExecutionDriver) (hooks : ActionHooks) (allowCodes : Bool)
    (gasCap : Option Nat) (g0 : GPre) (gen? : Option ChunkExtra) (implicitIdx : List Nat)
    (slotB2 : ChunkInner) (receipts : List Rcpt) (k : GFin → Except String β)
    (g : β → Except String γ) :
    genAC driver hooks allowCodes gasCap g0 gen? implicitIdx slotB2 receipts k >>= g =
      genAC driver hooks allowCodes gasCap g0 gen? implicitIdx slotB2 receipts (fun x => k x >>= g) := by
  unfold genAC
  nat_walk

theorem genAB_nat {β γ : Type} (driver : ExecutionDriver) (hooks : ActionHooks) (allowCodes : Bool)
    (gasCap : Option Nat) (g0 : GPre) (gen? : Option ChunkExtra) (k : GFin → Except String β)
    (g : β → Except String γ) :
    genAB driver hooks allowCodes gasCap g0 gen? k >>= g =
      genAB driver hooks allowCodes gasCap g0 gen? (fun x => k x >>= g) := by
  unfold genAB
  nat_walk
  all_goals exact genAC_nat _ _ _ _ _ _ _ _ _ _ _

theorem genAK_nat {β γ : Type} (driver : ExecutionDriver) (hooks : ActionHooks) (allowCodes : Bool)
    (gasCap : Option Nat) (g0 : GPre) (k : GFin → Except String β) (g : β → Except String γ) :
    genAK driver hooks allowCodes gasCap g0 k >>= g =
      genAK driver hooks allowCodes gasCap g0 (fun x => k x >>= g) := by
  unfold genAK
  nat_walk
  all_goals exact genAB_nat _ _ _ _ _ _ _ _

theorem d2IntakeE_nat {β γ : Type} (driver : ExecutionDriver) (c : Claim) (codes : List Bytes)
    (w : StateWitnessD2) (H : ChunkInner) (blks : List Blk) (ep : EpochRec) (L : Layout)
    (k : Intake → D2Fin → Except String β) (g : β → Except String γ) :
    d2IntakeE driver c codes w H blks ep L k >>= g =
      d2IntakeE driver c codes w H blks ep L (fun I d => k I d >>= g) := by
  unfold d2IntakeE
  nat_walk

theorem d2IntakeD_nat {β γ : Type} (driver : ExecutionDriver) (c : Claim) (codes : List Bytes)
    (w : StateWitnessD2) (H : ChunkInner) (blks : List Blk) (ep : EpochRec) (L : Layout)
    (k : Intake → D2Fin → Except String β) (g : β → Except String γ) :
    d2IntakeD driver c codes w H blks ep L k >>= g =
      d2IntakeD driver c codes w H blks ep L (fun I d => k I d >>= g) := by
  unfold d2IntakeD
  nat_walk
  all_goals exact d2IntakeE_nat _ _ _ _ _ _ _ _ _ _

theorem d2IntakeC_nat {β γ : Type} (driver : ExecutionDriver) (c : Claim) (codes : List Bytes)
    (w : StateWitnessD2) (H : ChunkInner) (k : Intake → D2Fin → Except String β)
    (g : β → Except String γ) :
    d2IntakeC driver c codes w H k >>= g = d2IntakeC driver c codes w H (fun I d => k I d >>= g) := by
  unfold d2IntakeC
  nat_walk
  all_goals exact d2IntakeD_nat _ _ _ _ _ _ _ _ _ _

theorem d2IntakeB_nat {β γ : Type} (driver : ExecutionDriver) (c : Claim) (swBytes : Bytes)
    (codes : List Bytes) (k : Intake → D2Fin → Except String β) (g : β → Except String γ) :
    d2IntakeB driver c swBytes codes k >>= g =
      d2IntakeB driver c swBytes codes (fun I d => k I d >>= g) := by
  unfold d2IntakeB
  nat_walk
  all_goals exact d2IntakeC_nat _ _ _ _ _ _ _

theorem d2IntakeK_nat {β γ : Type} (driver : ExecutionDriver) (allowCodes : Bool) (cb wb : Bytes)
    (k : Intake → D2Fin → Except String β) (g : β → Except String γ) :
    d2IntakeK driver allowCodes cb wb k >>= g =
      d2IntakeK driver allowCodes cb wb (fun I d => k I d >>= g) := by
  unfold d2IntakeK
  nat_walk
  all_goals exact d2IntakeB_nat _ _ _ _ _ _

theorem finD2K_nat {β γ : Type} (driver : ExecutionDriver) (gasCap : Option Nat) (I : Intake)
    (d : D2Fin) (out : MainOutD2) (k : Bytes → Except String β) (g : β → Except String γ) :
    finD2K driver gasCap I d out k >>= g = finD2K driver gasCap I d out (fun r => k r >>= g) := by
  unfold finD2K
  nat_walk

theorem gPrefixK_pull {β : Type} (driver : ExecutionDriver) (allowCodes : Bool) (cb wb : Bytes)
    (k : GPre → Except String β) :
    gPrefixK driver allowCodes cb wb k = gPrefixK driver allowCodes cb wb pure >>= k := by
  rw [gPrefixK_nat]; simp only [pure_bind]

theorem genAK_pull {β : Type} (driver : ExecutionDriver) (hooks : ActionHooks) (allowCodes : Bool)
    (gasCap : Option Nat) (g0 : GPre) (k : GFin → Except String β) :
    genAK driver hooks allowCodes gasCap g0 k = genAK driver hooks allowCodes gasCap g0 pure >>= k := by
  rw [genAK_nat]; simp only [pure_bind]

theorem d2IntakeK_pull {β : Type} (driver : ExecutionDriver) (allowCodes : Bool) (cb wb : Bytes)
    (k : Intake → D2Fin → Except String β) :
    d2IntakeK driver allowCodes cb wb k =
      d2IntakeK driver allowCodes cb wb (fun I d => pure (I, d)) >>= fun p => k p.1 p.2 := by
  rw [d2IntakeK_nat]; simp only [pure_bind]

theorem finD2K_pull {β : Type} (driver : ExecutionDriver) (gasCap : Option Nat) (I : Intake)
    (d : D2Fin) (out : MainOutD2) (k : Bytes → Except String β) :
    finD2K driver gasCap I d out k = finD2K driver gasCap I d out pure >>= k := by
  rw [finD2K_nat]; simp only [pure_bind]

end NearSpecV3.E2E
