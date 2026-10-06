import NearSpecV3.ChunkValidationV0

/-!
# `prepD0`: the native, claim-side part of the D0 verifier (V3-D0-DESIGN §1, §2.1, §6.1)

`prepD0 cb h` runs every check of `checkD0` that is a function of the claim alone (class
**C** of V3-D0-DESIGN §1) or of the claim plus a small proof-carried hint `h` (class **H**),
and emits the *prepared statement* `Prep` whose bytes `Prep.encode` are the public input of
the witness-only STARK (class **W**: tries, receipts, Merkle paths, tokens, outcomes).

It is built **only from existing `NearSpecV3` functions**, in `checkD0`'s order:
`decodeClaimE`, `decodeChunkInner`, `decodeLayout`, `rsGenesisParamsOk`, `decodeBlk`
(block hashes, `chunk_headers_root`), the backward walk, `chunkHash`, `shuffleWithSeed`,
`blockCtx`, `prims` (= `Scheduler.run` with `Congestion`), `queueEmpty`, `bufferedShards`,
`tryForward`, `Limit`, `outgoingReceiptsRoot`, `encodedMerkleRoot`, `encodeReceipts`,
`proofRoutes`' `Layout.shardOf`. Its error messages are `checkD0`'s.

## The hint (`Hint`) and a deviation from the design's table

* `n` — number of applied receipts (fixes `e.compute` and `H.prev_gas_used = n·G`);
* `refunds` — the generated refund receipts in order (`out.outgoing`). The design (§2.3)
  carries the body bytes `B` and decodes refunds with `pReceipt`; that is **not exact**:
  `pReceipt` rejects non-named receivers (`r.shape`), but a gas refund goes to the *signer*,
  which may be an implicit account (in D0: `refundCongestionGas` prices exactly that case).
  The hint therefore carries the refund receipts themselves and `prepD0` computes
  `B = u32 0 ‖ encodeReceipts refunds` (so `B` and the refunds agree by construction; the AIR
  binds `B` bytewise as in §1);
* the values read at the fixed keys of the main pre-state: `[7]`, `0x0f` (`s0`), `[13]`,
  `[16]‖u64 s` for every buffered shard `s`, `[10]` (`none` = proven absent);
* per implicit transition: the `[7]` value and the `0x0f` value read, where `sched = none`
  means "the value the previous transition wrote" (the A3 case, always the honest one).

Every hint value is checked by the AIR as a touched trie value (walk to the public key ending
at that value, by digest), `refunds` through `B`, `n` through `mrk`/`rcpt` — a wrong hint is
never accepted; `prepD0` itself only needs the hint to be well-formed.

## The prepared statement (`Prep`)

Header (`PrepHdr`): τ count `K + 1`, `n`, own shard id / index / shard count, B2 height, gas
price and gas limit, `prev_state_root` of B2's slot (τ = 0 root), `H.prev_state_root` (final
root), `H.prev_outcome_root`, `H.prev_balance_burnt`. Segments: the source receipt lists in
**applied order** (`(key, from_shard, root)`, after the ChaCha20 shuffle), the own shard's
routing intervals, `B`, the fixed-key walks per τ (key, expected terminal), the `0x0f` states
written per τ. `Prep.encode` puts values in as `(len, sha256)` digests.

Routing intervals (`ownIntervals`): `Layout.shardOf a = shard_ids[partition_point(b ≤ a)]`;
for each position `k` with `shard_ids[k] = own` the accounts with partition point `k` are
`[max(boundaries[0..k)), boundaries[k])` (open ends = `none`). For a well-formed layout this
is the single interval `[boundaries[i−1], boundaries[i])`; the general form keeps `prepD0`
exact for any trusted layout bytes. `inIntervals_iff_shardOf` is **tested**
(`nearspec-v3-test-prep`), not proved.

## Open (recorded for the AIR lanes)
* Two used source chunks with the same `chunk_hash` share one witness entry (last-wins
  lookup) and `distinctKeys = used` then needs an extra unused entry; the prepared lists keep
  the key so the AIR can enforce equal lists for equal keys (§3.5 `srcp`).
-/

namespace NearSpecV3

open NearSpec NearSpec.TransferV1

/-! ## Hint -/

structure ImplicitHint where
  /-- value read at `[7]` (`DelayedReceiptIndices`, determinacy only) -/
  delayed : Option Bytes
  /-- `0x0f` read: `none` = the value the previous transition wrote; `some v` = explicit -/
  sched : Option (Option Bytes)
  deriving DecidableEq, Repr

structure Hint where
  n : Nat
  refunds : List Receipt
  s0 : Option Bytes
  delayed : Option Bytes
  buffered : Option Bytes
  groups : List (Option Bytes)
  yield : Option Bytes
  implicit : List ImplicitHint
  deriving DecidableEq, Repr

def Hint.empty : Hint := ⟨0, [], none, none, none, [], none, []⟩

/-! ## Prepared statement -/

structure PrepHdr where
  K : Nat
  n : Nat
  own : Nat
  ownIdx : Nat
  numShards : Nat
  height : Nat
  gasPrice : Nat
  gasLimit : Nat
  prevStateRoot : Bytes
  postStateRoot : Bytes
  outcomeRoot : Bytes
  balanceBurnt : Nat
  deriving DecidableEq, Repr

/-- One source receipt list in applied order. -/
structure SrcList where
  key : Bytes          -- chunk_hash (witness map key)
  fromShard : Nat
  root : Bytes         -- prev_outgoing_receipts_root of the source chunk
  deriving DecidableEq, Repr

/-- A fixed-key read of transition `tau`: the walk to `key` must end at `value`
(`none` = proven absent). -/
structure PubWalk where
  tau : Nat
  key : List Nat
  value : Option Bytes
  deriving DecidableEq, Repr

structure Prep where
  hdr : PrepHdr
  lists : List SrcList
  bnds : List (Option Bytes × Option Bytes)
  body : Bytes
  walks : List PubWalk
  states : List Bytes
  deriving DecidableEq, Repr

/-! ## Routing intervals -/

def lexMax (a b : Bytes) : Bytes := if lexLe a b then b else a

def lexMaxOpt (l : List Bytes) : Option Bytes :=
  l.foldl (fun acc b => some (match acc with | none => b | some a => lexMax a b)) none

/-- The accounts routed to `own` by `l.shardOf`, as half-open lexicographic intervals. -/
def ownIntervals (l : Layout) (own : Nat) : List (Option Bytes × Option Bytes) :=
  (List.range (l.boundaries.length + 1)).filterMap fun k =>
    if l.shardIds.getD k 0 == own then some (lexMaxOpt (l.boundaries.take k), l.boundaries[k]?)
    else none

def inInterval (a : Bytes) (iv : Option Bytes × Option Bytes) : Bool :=
  (match iv.1 with | none => true | some lo => lexLe lo a) &&
  (match iv.2 with | none => true | some hi => !lexLe hi a)

def inIntervals (ivs : List (Option Bytes × Option Bytes)) (a : Bytes) : Bool := ivs.any (inInterval a)

/-! ## `prepD0` -/

def prepD0 (cb : Bytes) (h : Hint) : Except String Prep := do
  -- 3.1 decoding (claim part)
  let c ← (decodeClaimE cb).mapError (fun e => s!"invalid claim: {e}")
  let H ← (decodeChunkInner c.chunkInner).mapError (fun e => s!"invalid claim: {e}")
  -- claim-level D0 conditions and trusted-fact consistency
  check (c.protocolVersion == 86) "out of domain (c.pv86)"
  check (c.epochs.length == 1) "out of domain (c.single_epoch): more than one epoch"
  let ep := c.epochs.headD ⟨[], 0, 0, [], []⟩
  check (ep.epochId == c.epochId && ep.protocolVersion == c.protocolVersion)
    "invalid: epoch table does not match epoch_id / protocol_version"
  let L ← decodeLayout ep.shardLayout
  check (1 ≤ L.numShards && L.numShards ≤ 64) "out of domain (c.layout)"
  check (rsGenesisParamsOk c.rsDataParts c.rsTotalParts) "invalid: Reed-Solomon parameters"
  check (c.blocks.length ≤ 32) "out of domain (c.segment)"
  check (c.txValid.isEmpty) "out of domain (c.no_tx_flags)"
  check (c.epochStartAfter.length == c.blocks.length) "invalid: epoch_start_after length"
  check (c.epochStartAfter.all (· == 0)) "out of domain (c.single_epoch): epoch start"
  check (c.applyFacts.all fun f => f.validatorUpdate.isNone && f.splitGate.isNone)
    "out of domain (c.no_split_gate)"
  -- 3.2 chain segment
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
  check (slotB2.gasLimit ≤ maxGasLimitD0) "out of domain (c.gas_limit): chunk gas_limit above 10^15"
  -- 3.3 / 3.4: source lists in applied order (keys, from shards, roots, ChaCha20 shuffle)
  let mut lists : List SrcList := []
  for S in sourceBlks do
    let mut srcs : List SrcList := []
    for (s, ci) in S.slots do
      if s.heightIncluded == S.hdr.height then
        srcs := srcs ++ [⟨chunkHash s.inner ci.encodedMerkleRoot, ci.shardId, ci.prevOutgoingReceiptsRoot⟩]
    let shuffled ← match shuffleWithSeed srcs S.hdr.prevHash with
      | some p => pure p
      | none => throw "invalid: shuffle fuel exhausted (probability < 2^-1024)"
    lists := lists ++ shuffled
  check (slotB2.txRoot == zeroHash32) "invalid: transaction root of the last chunk"
  let own := slotB2.congestion
  check (own.delayedGas == 0 && own.bufferedGas == 0 && own.receiptBytes == 0)
    "out of domain (c.own_congestion_zero)"
  -- 3.5 main transition, claim/hint part
  let ctxB2 := blockCtx L H.shardId slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  let bshards ← (bufferedShards h.buffered).mapError id
  check (h.groups.length == bshards.length) "invalid: hint (buffered group values)"
  queueEmpty h.delayed "delayed receipt queue"
  let so ← match prims.sched ⟨ctxB2.layout.shardIds, ctxB2.own, h.s0, ctxB2.statuses,
                               ctxB2.requests, ctxB2.prevBlockHash⟩ with
    | some o => pure o
    | none => throw "invalid: bandwidth scheduler aborted (StorageInconsistentState)"
  let limits : List Limit := ctxB2.statuses.map fun (s, ci, missed) =>
    ⟨s, (if s == ctxB2.own then GASMAX else prims.outGas ci missed ctxB2.own), so.grant ctxB2.own s⟩
  let _ ← h.refunds.foldlM (fun ls rf =>
      match tryForward ctxB2 ls rf with
      | some ls' => .ok ls'
      | none => .error "out of domain (e.forwarded): generated receipt buffered") limits
  check (h.n == 0 || (h.n - 1) * Params.G < ctxB2.gasLimit)
    "out of domain (e.compute): receipt delayed by the compute limit"
  queueEmpty h.yield "promise yield queue"
  -- 3.6 implicit transitions: scheduler runs on the hinted / previously written 0x0f
  check (h.implicit.length == implicitBlks.length) "invalid: implicit transitions count"
  let mut prevState : Bytes := so.state
  let mut states : List Bytes := [so.state]
  let mut walks : List PubWalk :=
    [⟨0, keyDelayedIdx, h.delayed⟩, ⟨0, keyBwState, h.s0⟩, ⟨0, keyBufferedIdx, h.buffered⟩] ++
    (bshards.zip h.groups).map (fun (s, v) => ⟨0, keyGroupsData s, v⟩) ++
    [⟨0, keyYieldIdx, h.yield⟩]
  let mut tau := 1
  for (M, ih) in implicitBlks.zip h.implicit do
    let ctxM := blockCtx L H.shardId slotB2.gasLimit M M.hdr.nextGasPrice
    let read : Option Bytes := match ih.sched with
      | none => some prevState
      | some v => v
    let o ← match prims.sched ⟨ctxM.layout.shardIds, ctxM.own, read, ctxM.statuses,
                                ctxM.requests, ctxM.prevBlockHash⟩ with
      | some o => pure o
      | none => throw "invalid: bandwidth scheduler aborted (StorageInconsistentState)"
    walks := walks ++ [⟨tau, keyDelayedIdx, ih.delayed⟩, ⟨tau, keyBwState, read⟩]
    states := states ++ [o.state]
    prevState := o.state
    tau := tau + 1
  -- 3.7 header comparison, claim/hint part
  let allowed := L.shardIds.getD ((B2.hdr.height + idx) % L.numShards) H.shardId
  let ownCongestion : Congestion := { own with allowedShard := allowed }
  check H.proposals.isEmpty "invalid: InvalidValidatorProposals"
  check (H.gasLimit == slotB2.gasLimit) "invalid: InvalidGasLimit"
  check (H.prevGasUsed == h.n * Params.G) "invalid: InvalidGasUsed"
  check (H.prevOutgoingReceiptsRoot == outgoingReceiptsRoot L h.refunds) "invalid: InvalidReceiptsProof"
  check (H.congestion == ownCongestion) "invalid: InvalidCongestionInfo"
  check H.bwRequests.isEmpty "invalid: InvalidBandwidthRequests"
  check H.proposedSplit.isNone "invalid: InvalidChunkHeaderShardSplit"
  check (H.txRoot == zeroHash32) "invalid: InvalidTxRoot"
  let body := u32 0 ++ encodeReceipts h.refunds
  match encodedMerkleRoot c.rsDataParts c.rsTotalParts body with
  | none => throw "invalid: Reed-Solomon parameters"
  | some (emr, len) =>
    check (H.encodedMerkleRoot == emr) "invalid: InvalidChunkEncodedMerkleRoot"
    check (H.encodedLength == len) "invalid: InvalidChunkEncodedLength"
  pure {
    hdr := { K := implicitBlks.length, n := h.n, own := H.shardId, ownIdx := idx,
             numShards := L.numShards, height := B2.hdr.height, gasPrice := prevB2.hdr.nextGasPrice,
             gasLimit := slotB2.gasLimit, prevStateRoot := slotB2.prevStateRoot,
             postStateRoot := H.prevStateRoot, outcomeRoot := H.prevOutcomeRoot,
             balanceBurnt := H.prevBalanceBurnt }
    lists, bnds := ownIntervals L H.shardId, body, walks, states }

/-! ## Encoding of the prepared statement (the STARK's public input) -/

/-- `"near-arena-prep-d0-v0"` -/
def prepTag : Bytes := "near-arena-prep-d0-v0".toUTF8.toList

def encDigestOpt : Option Bytes → Bytes
  | none => [0]
  | some v => [1] ++ u32 v.length ++ sha256 v

def PrepHdr.encode (h : PrepHdr) : Bytes :=
  u32 h.K ++ u32 h.n ++ u64 h.own ++ u32 h.ownIdx ++ u32 h.numShards ++ u64 h.height ++
  u128 h.gasPrice ++ u64 h.gasLimit ++ h.prevStateRoot ++ h.postStateRoot ++ h.outcomeRoot ++
  u128 h.balanceBurnt

def SrcList.encode (s : SrcList) : Bytes := s.key ++ u64 s.fromShard ++ s.root

def PubWalk.encode (w : PubWalk) : Bytes :=
  u32 w.tau ++ encList u8 w.key ++ encDigestOpt w.value

def Prep.encode (p : Prep) : Bytes :=
  borshBytes prepTag ++ p.hdr.encode ++ encList SrcList.encode p.lists ++
  encList (fun (lo, hi) => encOpt borshBytes lo ++ encOpt borshBytes hi) p.bnds ++
  borshBytes p.body ++ encList PubWalk.encode p.walks ++
  encList (fun v => u32 v.length ++ sha256 v) p.states

/-! ## `hintOf`: the hint read off the relation's own execution

Mirrors `checkD0` without its checks (lenient: a missing piece leaves a default), so that on
every `RelD0` case it returns exactly the values `checkD0` reads. Refunds: `out.outgoing` of
the main application; if that application fails (e.g. a refund would be buffered), the
refunds generated up to the failing receipt, so `prepD0` reports the same D0 exclusion. -/

/-- Refunds generated by applying `rs` in order, up to the first failing receipt. -/
def refundsUpTo (ctx : ApplyCtx) : Acc → List Receipt → List Receipt
  | acc, [] => acc.refunds
  | acc, r :: rs =>
    if r.predecessorId == AccountId.system then
      match applySystemReceipt acc r with
      | .ok acc' => refundsUpTo ctx acc' rs
      | .error _ => acc.refunds
    else
      match applyReceipt ⟨ctx.height, ctx.gasPrice⟩ acc r with
      | some acc' => refundsUpTo ctx acc' rs
      | none => acc.refunds

def findD (t : PTrie) (k : List Nat) : Option Bytes := (t.find k).getD none

def hintOfE (cb wb : Bytes) : Except String Hint := do
  let c ← decodeClaimE cb
  let (swBytes, _) ← decodeWitnessFile wb
  let w ← decodeStateWitness swBytes
  let H ← decodeChunkInner c.chunkInner
  let ep := c.epochs.headD ⟨[], 0, 0, [], []⟩
  let L ← decodeLayout ep.shardLayout
  let blks ← c.blocks.mapM decodeBlk
  let idx ← match L.index H.shardId with | some i => pure i | none => throw "layout"
  let isNew := fun (b : Blk) => match b.slots[idx]? with
    | some (s, _) => s.heightIncluded == b.hdr.height
    | none => false
  let b2i ← match blks.findIdx? isNew with | some i => pure i | none => throw "walk"
  let B2 ← match blks[b2i]? with | some b => pure b | none => throw "walk"
  let stop := match (blks.drop (b2i + 1)).findIdx? isNew with
    | some j => b2i + 1 + j
    | none => blks.length
  let implicitBlks := (blks.take b2i).reverse
  let sourceBlks := (blks.drop b2i).take (stop - b2i)
  let prevB2 ← match blks[b2i + 1]? with | some b => pure b | none => throw "walk"
  let slotB2 ← match B2.slots[idx]? with | some p => pure p.2 | none => throw "slot"
  -- applied receipts (as checkD0)
  let mut receipts : List Receipt := []
  for S in sourceBlks do
    let proofs := S.slots.filterMap fun (s, ci) =>
      if s.heightIncluded == S.hdr.height then lookupLast (chunkHash s.inner ci.encodedMerkleRoot) w.entries
      else none
    let shuffled := (shuffleWithSeed proofs S.hdr.prevHash).getD proofs
    receipts := receipts ++
      (shuffled.map fun e => e.receipts.filter fun r => L.shardOf r.receiverId == H.shardId).flatten
  let ctxB2 := blockCtx L H.shardId slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  let t0 := partialTrie w.main.values slotB2.prevStateRoot [keyBufferedIdx]
  let buffered := findD t0 keyBufferedIdx
  let bshards := match bufferedShards buffered with | .ok s => s | .error _ => []
  let tMain := partialTrie w.main.values slotB2.prevStateRoot (mainKeys receipts bshards)
  let s0 := findD tMain keyBwState
  let (refunds, root0) := match applyNewChunk prims ctxB2 tMain receipts with
    | .ok out => (out.outgoing, out.trie.hashOf)
    | .error _ => (refundsUpTo ctxB2 ⟨tMain, [], [], 0, 0⟩ receipts, w.main.postStateRoot)
  let so := prims.sched ⟨ctxB2.layout.shardIds, ctxB2.own, s0, ctxB2.statuses, ctxB2.requests,
                         ctxB2.prevBlockHash⟩
  let mut prevState : Option Bytes := so.map (·.state)
  let mut root := root0
  let mut imps : List ImplicitHint := []
  for (M, T) in implicitBlks.zip w.implicit do
    let ctxM := blockCtx L H.shardId slotB2.gasLimit M M.hdr.nextGasPrice
    let tM := partialTrie T.values root [keyDelayedIdx, keyBwState]
    let v := findD tM keyBwState
    imps := imps ++ [⟨findD tM keyDelayedIdx, if prevState.isSome && v == prevState then none else some v⟩]
    let o := prims.sched ⟨ctxM.layout.shardIds, ctxM.own, v, ctxM.statuses, ctxM.requests,
                          ctxM.prevBlockHash⟩
    prevState := o.map (·.state)
    root := match applyMissingChunk prims ctxM tM with
      | .ok t => t.hashOf
      | .error _ => T.postStateRoot
  pure { n := receipts.length, refunds, s0, delayed := findD tMain keyDelayedIdx, buffered,
         groups := bshards.map fun s => findD tMain (keyGroupsData s),
         yield := findD tMain keyYieldIdx, implicit := imps }

/-- The hint for `(claim, witness)` (`Hint.empty` if the pair does not even decode). -/
def hintOf (cb w : Bytes) : Hint :=
  match hintOfE cb w with
  | .ok h => h
  | .error _ => Hint.empty

end NearSpecV3
