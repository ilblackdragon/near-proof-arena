import NearSpecV3.ChunkValidationV0a

/-!
# `prepD0`: the native, claim-side part of a `RelD0a` verifier (V3-D0-DESIGN §1, §2.1, §6.1, §11)

`prepD0 cb h` runs every check of `checkD0a` that is a function of the claim alone (class
**C**) or of the claim plus the proof-carried hint `h = {n, refunds}` (class **H**), and
emits the *prepared statement* `Prep` (`Prep.encode` = the STARK's public input). Everything
else is the AIR's (class **W**: tries, receipts, Merkle paths, tokens, outcomes, and — after
the round-2 decision §11 (c) — the fixed-key value parses `[7] [10] [13] [16]‖s`, Canon0f /
the `0x0f` state decode and the scheduler's state-dependent core).

Built **only from existing `NearSpecV3` functions** in `checkD0`'s order: `decodeClaimE`,
`decodeChunkInner`, `decodeLayout`, `rsGenesisParamsOk`, `decodeBlk` (block hashes,
`chunk_headers_root`), the backward walk, `chunkHash`, `shuffleWithSeed`, `blockCtx`,
`toCI`, `Scheduler.statuses` / `linkAllowed` / `Params.calculate` / `convertRequests`
(`Congestion` f64 inside), `Congestion.outgoingGasLimit` (`prims.outGas`), `Limit`,
`refundCongestionGas`, `outgoingReceiptsRoot`, `encodedMerkleRoot`, `encodeReceipts`,
`Layout.shardOf`.

It is modular (§11): `prepClaim cb` is the claim-only part; `prepBody pc h` the `{n, B}` part;
`prepD0 cb h := prepClaim cb >>= (prepBody · h)`.

## Hint
* `n` — number of applied receipts (`e.compute`, `H.prev_gas_used = n·G`);
* `refunds` — the generated refund receipts in order (`out.outgoing`); the body is
  `B = u32 0 ‖ encodeReceipts refunds`. (On the wire the hint is `n` and `B`. Parsing `B`
  needs a refund-receipt parser: `pReceipt` is **not** exact for it — it rejects non-named
  receivers, but a gas refund goes to the signer, which may be an implicit account, and
  `refundCongestionGas` prices exactly that case in D0. The in-memory hint therefore keeps the
  receipts and `B` is computed from them; a `B` parser is an open item for the verifier.)

## Scheduler public data (`SchedPub`, per applied block τ: B2 then implicit oldest first)
The claim-only inputs of `Scheduler.run`: shard ids, `Params` (base bandwidth, budgets,
max allowance), the link-allowed matrix (from `statuses`: f64 congestion level, missed
chunks, allowed shard), the converted requests (`Req`: link index `s·n+r` and increase list,
senders ascending, list order), the ChaCha20 seed `prev_block_hash`, and
`sha256(borsh(all_shards))`. `Scheduler.runCore pub prev` is the state-dependent remainder;
`Scheduler.run_eq_core` (**proved**) : `run cfg cc ids prev cong req seed =
(pubOf cfg cc ids cong req seed).bind (runCore · prev)`. The in-AIR scheduler is therefore
specified by `runCore` on public `SchedPub` and the AIR-decoded previous state.

## Forwarding (`e.forwarded`) split
`tryForward` checks per refund `limit.gas ≥ min(gas, 10^15) ∧ limit.size ≥ size` and then
subtracts both. The gas limits are claim-only (`outGas` of each slot's congestion, `GASMAX`
for the own shard) and the size limits are the main scheduler run's grants `grant(own, s)`
(AIR-computed). Since the size check is a running subtraction, *every refund forwards* iff
(i) the gas-only simulation passes (native, here), (ii) every refund routes to a shard with a
status entry (native; otherwise the default limit has size 0), and (iii) for every such shard
`s`, `Σ size of refunds to s ≤ grant(own, s)` — (iii) is emitted as `Prep.fwd` for the AIR.
(Equivalence **tested** on every case, `nearspec-v3-test-prep`; not proved.)

## Routing intervals
`ownIntervals` as before: for each position `k` with `shard_ids[k] = own`, the accounts with
partition point `k` are `[max(boundaries[0..k)), boundaries[k])`. **Tested**, not proved.

## Open (recorded for the AIR lanes)
* Two used source chunks with the same `chunk_hash` share one witness entry; the lists keep
  the key so the AIR can enforce equal lists for equal keys (§3.5 `srcp`).
-/

namespace NearSpecV3

open NearSpec NearSpec.TransferV1

/-! ## Hint -/

structure Hint where
  n : Nat
  refunds : List Receipt
  deriving DecidableEq, Repr

def Hint.empty : Hint := ⟨0, []⟩

/-- `B` = borsh `(Vec<SignedTransaction> = [], outgoing)` (`checkD0` step 18). -/
def Hint.body (h : Hint) : Bytes := u32 0 ++ encodeReceipts h.refunds

/-! ## Scheduler: public (claim-only) part and state-dependent core -/

namespace Scheduler

structure SchedPub where
  ids : List Nat
  params : Params
  allowed : Array Bool
  reqs : List Req
  seed : Bytes
  allShardsHash : Bytes
  deriving Repr

/-- Claim-only inputs of `run` (`none` = a claim-only abort: no shards, bad config). -/
def pubOf (cfg : Config) (cc : CongestionConfig) (ids : List Nat)
    (congestion : List (Nat × CongestionInfo × Nat))
    (requests : List (Nat × List BandwidthRequest)) (prevBlockHash : Bytes) : Option SchedPub := do
  let n := ids.length
  if n = 0 then none
  let p ← Params.calculate cfg n
  let status := statuses cc ids congestion
  let links := List.range (n * n)
  let allowed : Array Bool := (links.map fun l => linkAllowed status (l / n) (l % n)).toArray
  some ⟨ids, p, allowed, convertRequests p ids requests, prevBlockHash,
        sha256 (u32 n ++ concatAll (ids.map u64))⟩

/-- The state-dependent remainder of `run` (in-AIR after §11 (c)). -/
def runCore (pub : SchedPub) (prevState : Option Bytes) : Option Output := do
  let prev ← match prevState with
    | none => some NearSpec.Bandwidth.State.initial
    | some b => NearSpec.Bandwidth.State.decode b
  let ids := pub.ids
  let n := ids.length
  let p := pub.params
  let links := List.range (n * n)
  let allowed := pub.allowed
  let allow0 := prev.links.foldl (fun (a : Array Nat) la =>
      match indexOf ids la.sender, indexOf ids la.receiver with
      | some s, some r => a.set! (s * n + r) la.allowance
      | _, _ => a) (Array.replicate (n * n) 0)
  let reqs := pub.reqs
  let st : St := ⟨Array.replicate n p.maxShardBandwidth, Array.replicate n p.maxShardBandwidth,
    allow0, Array.replicate (n * n) 0, Rng.ofSeed pub.seed⟩
  let fair := p.maxShardBandwidth / n
  let st := { st with allowance := st.allowance.map fun a => Nat.min (Nat.min (a + fair) u64Max) p.maxAllowance }
  let st := links.foldl (fun st l => (tryGrant n allowed st l p.base).2) st
  let st ← processRequests n allowed st reqs
  let st := distribute n allowed st
  let sid (i : Nat) : Nat := ids.getD i 0
  let newLinks : List NearSpec.Bandwidth.LinkAllowance :=
    links.map fun l => ⟨sid (l / n), sid (l % n), st.allowance[l]!⟩
  let newState : NearSpec.Bandwidth.State := ⟨newLinks, sha256 (prev.sanityHash ++ pub.allShardsHash)⟩
  some ⟨newState.encode, links.map fun l => ((sid (l / n), sid (l % n)), st.granted[l]!), p⟩

/-- `run` = claim-only public part, then the state-dependent core. -/
theorem run_eq_core (cfg : Config) (cc : CongestionConfig) (ids : List Nat) (prev : Option Bytes)
    (cong : List (Nat × CongestionInfo × Nat)) (req : List (Nat × List BandwidthRequest))
    (seed : Bytes) :
    run cfg cc ids prev cong req seed = (pubOf cfg cc ids cong req seed).bind (runCore · prev) := by
  unfold run pubOf runCore
  by_cases hn : ids.length = 0
  · cases prev with
    | none => simp [hn]
    | some b => cases NearSpec.Bandwidth.State.decode b <;> simp [hn]
  · cases hp : Params.calculate cfg ids.length with
    | none =>
      cases prev with
      | none => simp [hn, hp]
      | some b => cases NearSpec.Bandwidth.State.decode b <;> simp [hn, hp]
    | some p =>
      cases prev with
      | none => simp only [hn, hp, Option.bind, ↓reduceIte, bind, Option.bind_some]; rfl
      | some b =>
        cases hd : NearSpec.Bandwidth.State.decode b with
        | none => simp only [hn, hp, hd, Option.bind, ↓reduceIte, bind]
        | some st => simp only [hn, hp, hd, Option.bind, ↓reduceIte, bind]; rfl

end Scheduler

/-- The scheduler's public data for one apply context (the `prims.sched` mapping). -/
def schedPub (ctx : ApplyCtx) : Option Scheduler.SchedPub :=
  Scheduler.pubOf Scheduler.Config.pv86 CongestionConfig.pv86 ctx.layout.shardIds
    (ctx.statuses.map fun (s, c, m) => (s, toCI c, m))
    (ctx.requests.map fun (s, rs) => (s, rs.map fun r => ⟨r.toShard, r.bitmap⟩))
    ctx.prevBlockHash

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
  key : Bytes
  fromShard : Nat
  root : Bytes
  deriving DecidableEq, Repr

/-- Claim-only part of the prepared statement. -/
structure PrepC where
  hdr : PrepHdr                -- `n` filled by `prepBody`
  lists : List SrcList
  bnds : List (Option Bytes × Option Bytes)
  sched : List Scheduler.SchedPub
  -- kept for `prepBody`
  L : Layout
  H : ChunkInner
  ctxB2 : ApplyCtx
  rsData : Nat
  rsTotal : Nat
  allowed : Nat
  ownCongestion : Congestion

structure Prep where
  hdr : PrepHdr
  lists : List SrcList
  bnds : List (Option Bytes × Option Bytes)
  sched : List Scheduler.SchedPub
  body : Bytes
  /-- `(shard, Σ refund sizes)`: the AIR checks `≤ grant(own, shard)` of the τ = 0 run -/
  fwd : List (Nat × Nat)

/-! ## Routing intervals -/

def lexMax (a b : Bytes) : Bytes := if lexLe a b then b else a

def lexMaxOpt (l : List Bytes) : Option Bytes :=
  l.foldl (fun acc b => some (match acc with | none => b | some a => lexMax a b)) none

def ownIntervals (l : Layout) (own : Nat) : List (Option Bytes × Option Bytes) :=
  (List.range (l.boundaries.length + 1)).filterMap fun k =>
    if l.shardIds.getD k 0 == own then some (lexMaxOpt (l.boundaries.take k), l.boundaries[k]?)
    else none

def inInterval (a : Bytes) (iv : Option Bytes × Option Bytes) : Bool :=
  (match iv.1 with | none => true | some lo => lexLe lo a) &&
  (match iv.2 with | none => true | some hi => !lexLe hi a)

def inIntervals (ivs : List (Option Bytes × Option Bytes)) (a : Bytes) : Bool := ivs.any (inInterval a)

/-! ## Forwarding split -/

/-- Status shards in first-occurrence order (`Limit.get` uses the first entry). -/
def statusShards (ctx : ApplyCtx) : List Nat :=
  ctx.statuses.foldl (fun acc (s, _, _) => if acc.contains s then acc else acc ++ [s]) []

/-- Gas-only part of `tryForward` over all refunds (claim-only limits). -/
def fwdGasOk (ctx : ApplyCtx) (refunds : List Receipt) : Bool :=
  let gas0 : List (Nat × Nat) := ctx.statuses.map fun (s, ci, missed) =>
    (s, if s == ctx.own then GASMAX else prims.outGas ci missed ctx.own)
  let get (ls : List (Nat × Nat)) (s : Nat) : Nat := ((ls.find? (·.1 == s)).map (·.2)).getD GASMAX
  let step (acc : Option (List (Nat × Nat))) (r : Receipt) : Option (List (Nat × Nat)) := do
    let ls ← acc
    let s := ctx.layout.shardOf r.receiverId
    let gas := refundCongestionGas r.receiverId
    let g := get ls s
    if g ≥ min gas allowedShardOutgoingGas then
      some (ls.map fun (x, y) => if x == s then (x, g - gas) else (x, y))
    else none
  (refunds.foldl step (some gas0)).isSome

/-- Per status shard, the total (capped) size of the refunds routed to it. -/
def fwdSizes (ctx : ApplyCtx) (refunds : List Receipt) : List (Nat × Nat) :=
  (statusShards ctx).map fun s =>
    (s, ((refunds.filter fun r => ctx.layout.shardOf r.receiverId == s).map
          fun r => min r.encode.length maxReceiptSize).sum)

/-! ## `prepD0` -/

def prepClaim (cb : Bytes) : Except String PrepC := do
  -- 3.1 decoding (claim part)
  let c ← (decodeClaimE cb).mapError (fun e => s!"invalid claim: {e}")
  let H ← (decodeChunkInner c.chunkInner).mapError (fun e => s!"invalid claim: {e}")
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
  -- A1
  check (slotB2.gasLimit ≤ maxGasLimitD0) "out of domain (c.gas_limit): chunk gas_limit above 10^15"
  -- 3.3 / 3.4: source lists in applied order
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
  -- scheduler public data per applied block (B2, then implicit oldest first)
  let ctxB2 := blockCtx L H.shardId slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  let ctxs := ctxB2 :: implicitBlks.map fun M => blockCtx L H.shardId slotB2.gasLimit M M.hdr.nextGasPrice
  let sched ← ctxs.mapM fun ctx => match schedPub ctx with
    | some p => pure p
    | none => throw "invalid: bandwidth scheduler aborted (StorageInconsistentState)"
  -- `allowed_shard` of the own congestion info (3.7); the header comparison itself runs in
  -- `prepBody`, after the execution-time conditions, in `checkD0`'s order
  let allowed := L.shardIds.getD ((B2.hdr.height + idx) % L.numShards) H.shardId
  pure {
    hdr := { K := implicitBlks.length, n := 0, own := H.shardId, ownIdx := idx,
             numShards := L.numShards, height := B2.hdr.height, gasPrice := prevB2.hdr.nextGasPrice,
             gasLimit := slotB2.gasLimit, prevStateRoot := slotB2.prevStateRoot,
             postStateRoot := H.prevStateRoot, outcomeRoot := H.prevOutcomeRoot,
             balanceBurnt := H.prevBalanceBurnt }
    lists, bnds := ownIntervals L H.shardId, sched, L, H, ctxB2,
    rsData := c.rsDataParts, rsTotal := c.rsTotalParts, allowed, ownCongestion := own }

def prepBody (pc : PrepC) (h : Hint) : Except String Prep := do
  let ctx := pc.ctxB2
  check (h.refunds.all fun r => (statusShards ctx).contains (ctx.layout.shardOf r.receiverId))
    "out of domain (e.forwarded): generated receipt buffered"
  check (fwdGasOk ctx h.refunds) "out of domain (e.forwarded): generated receipt buffered"
  check (h.n == 0 || (h.n - 1) * Params.G < ctx.gasLimit)
    "out of domain (e.compute): receipt delayed by the compute limit"
  -- 3.7 header comparison (claim/hint part), in `checkD0`'s order
  let H := pc.H
  check H.proposals.isEmpty "invalid: InvalidValidatorProposals"
  check (H.gasLimit == pc.hdr.gasLimit) "invalid: InvalidGasLimit"
  check (H.prevGasUsed == h.n * Params.G) "invalid: InvalidGasUsed"
  check (H.prevOutgoingReceiptsRoot == outgoingReceiptsRoot pc.L h.refunds) "invalid: InvalidReceiptsProof"
  check (H.congestion == { pc.ownCongestion with allowedShard := pc.allowed }) "invalid: InvalidCongestionInfo"
  check H.bwRequests.isEmpty "invalid: InvalidBandwidthRequests"
  check H.proposedSplit.isNone "invalid: InvalidChunkHeaderShardSplit"
  check (H.txRoot == zeroHash32) "invalid: InvalidTxRoot"
  let body := h.body
  match encodedMerkleRoot pc.rsData pc.rsTotal body with
  | none => throw "invalid: Reed-Solomon parameters"
  | some (emr, len) =>
    check (pc.H.encodedMerkleRoot == emr) "invalid: InvalidChunkEncodedMerkleRoot"
    check (pc.H.encodedLength == len) "invalid: InvalidChunkEncodedLength"
  pure { hdr := { pc.hdr with n := h.n }, lists := pc.lists, bnds := pc.bnds, sched := pc.sched,
         body, fwd := fwdSizes ctx h.refunds }

def prepD0 (cb : Bytes) (h : Hint) : Except String Prep := do
  let pc ← prepClaim cb
  prepBody pc h

/-! ## Encoding of the prepared statement (the STARK's public input) -/

/-- `"near-arena-prep-d0a-v0"` -/
def prepTag : Bytes := "near-arena-prep-d0a-v0".toUTF8.toList

def PrepHdr.encode (h : PrepHdr) : Bytes :=
  u32 h.K ++ u32 h.n ++ u64 h.own ++ u32 h.ownIdx ++ u32 h.numShards ++ u64 h.height ++
  u128 h.gasPrice ++ u64 h.gasLimit ++ h.prevStateRoot ++ h.postStateRoot ++ h.outcomeRoot ++
  u128 h.balanceBurnt

def SrcList.encode (s : SrcList) : Bytes := s.key ++ u64 s.fromShard ++ s.root

def Scheduler.SchedPub.encode (p : Scheduler.SchedPub) : Bytes :=
  encList u64 p.ids ++
  u64 p.params.base ++ u64 p.params.maxShardBandwidth ++ u64 p.params.maxSingleGrant ++
  u64 p.params.maxReceiptSize ++ u64 p.params.maxAllowance ++
  encList (fun b => u8 (if b then 1 else 0)) p.allowed.toList ++
  encList (fun q => u32 q.link ++ encList u64 q.incs) p.reqs ++
  p.seed ++ p.allShardsHash

def Prep.encode (p : Prep) : Bytes :=
  borshBytes prepTag ++ p.hdr.encode ++ encList SrcList.encode p.lists ++
  encList (fun (lo, hi) => encOpt borshBytes lo ++ encOpt borshBytes hi) p.bnds ++
  encList Scheduler.SchedPub.encode p.sched ++
  borshBytes p.body ++ encList (fun (s, t) => u64 s ++ u64 t) p.fwd

/-! ## `hintOf`: the hint read off the relation's own execution -/

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

/-- Applied receipts as `checkD0` builds them (lenient: missing proofs are skipped). -/
def appliedReceipts (k : WalkD0) (w : StateWitness) : List Receipt := Id.run do
  let mut receipts : List Receipt := []
  for S in k.sourceBlks do
    let proofs := S.slots.filterMap fun (s, ci) =>
      if s.heightIncluded == S.hdr.height then lookupLast (chunkHash s.inner ci.encodedMerkleRoot) w.entries
      else none
    let shuffled := (shuffleWithSeed proofs S.hdr.prevHash).getD proofs
    receipts := receipts ++
      (shuffled.map fun e => e.receipts.filter fun r => k.L.shardOf r.receiverId == k.H.shardId).flatten
  return receipts

def hintOfE (cb wb : Bytes) : Except String Hint := do
  let k ← walkD0 cb
  let w ← decodeW wb
  let B2 ← match k.blks[k.b2i]? with | some b => pure b | none => throw "walk"
  let prevB2 ← match k.blks[k.b2i + 1]? with | some b => pure b | none => throw "walk"
  let receipts := appliedReceipts k w
  let ctxB2 := blockCtx k.L k.H.shardId k.slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  let t0 := partialTrie w.main.values k.slotB2.prevStateRoot [keyBufferedIdx]
  let bshards := match (t0.find keyBufferedIdx).getD none |> bufferedShards with
    | .ok s => s | .error _ => []
  let tMain := partialTrie w.main.values k.slotB2.prevStateRoot (mainKeys receipts bshards)
  let refunds := match applyNewChunk prims ctxB2 tMain receipts with
    | .ok out => out.outgoing
    | .error _ => refundsUpTo ctxB2 ⟨tMain, [], [], 0, 0⟩ receipts
  pure ⟨receipts.length, refunds⟩

/-- The hint for `(claim, witness)` (`Hint.empty` if the pair does not decode). -/
def hintOf (cb w : Bytes) : Hint :=
  match hintOfE cb w with
  | .ok h => h
  | .error _ => Hint.empty

end NearSpecV3
