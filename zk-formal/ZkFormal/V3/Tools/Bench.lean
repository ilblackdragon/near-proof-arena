import ZkFormal.V3.Fast.Prep

/-!
`nearspec-v3-bench` — per-component timing of the native (claim/hint) part of a D0 verifier
(`prepD0`, V3-D0-DESIGN §5.4, §10 item 1). Compiled code, i.e. with every `@[csimp]` fast path
in force. Modes:

* `fixtures DIR...` — every accepted case: `prepD0 cb (hintOf cb wb)` total, and its components;
* `synthetic` — a valid 64-shard / 32-block claim (30 implicit transitions, B2 with 64 new
  source chunks, every shard requesting the full bitmap from every other shard in every block,
  Reed–Solomon (33,100)); `prepD0` succeeds on it; components timed;
* `rs N` — `encodedMerkleRoot` on an `N`-byte body for (33,100) and (85,256), and
  `outgoingReceiptsRoot` for 4481 refunds over 64 shards.

Components: (1) claim decode + header chain (`decodeClaimE`, `decodeLayout`, `decodeBlk`:
block hashes, chunk inners, `chunk_headers_root`); (2) shuffles (`shuffleWithSeed`); (3)
congestion (`Congestion.isFullyCongested` per status entry, `outGas` per slot); (4) scheduler public data
(`schedPub` per τ: link permissions, params, converted requests; the state-dependent core
is in-AIR after V3-D0-DESIGN §11); (5) Reed–Solomon (`encodedMerkleRoot`); (6) outgoing-receipts root.
-/

open NearSpec NearSpecV3
open NearSpec.TransferV1 (Acc)

instance : Inhabited Blk := ⟨⟨⟨0, [], [], [], []⟩, ⟨0, [], 0, [], [], 0, [], [], 0, []⟩, []⟩⟩

def nowNs : IO Nat := IO.monoNanosNow

def timeNs {α} (f : Unit → α) (force : α → Nat) : IO (Nat × Nat) := do
  let t0 ← nowNs
  let a ← IO.lazyPure f
  let k := force a
  let t1 ← nowNs
  return (t1 - t0, k)

def ms (ns : Nat) : String :=
  let x := ns / 10000
  s!"{x / 100}.{if x % 100 < 10 then "0" else ""}{x % 100}"

/-! ## Inputs extracted from a claim (mirrors `prepD0`'s own steps) -/

structure Parts where
  c : Claim
  L : Layout
  H : ChunkInner
  blks : List Blk
  b2i : Nat
  stop : Nat
  slotGas : Nat

def parts (cb : Bytes) : Except String Parts := do
  let c ← decodeClaimE cb
  let H ← decodeChunkInner c.chunkInner
  let L ← decodeLayout (c.epochs.headD ⟨[], 0, 0, [], []⟩).shardLayout
  let blks ← c.blocks.mapM decodeBlk
  let idx ← match L.index H.shardId with | some i => pure i | none => throw "layout"
  let isNew := fun (b : Blk) => match b.slots[idx]? with
    | some (s, _) => s.heightIncluded == b.hdr.height
    | none => false
  let b2i ← match blks.findIdx? isNew with | some i => pure i | none => throw "walk"
  let stop ← match (blks.drop (b2i + 1)).findIdx? isNew with
    | some j => pure (b2i + 1 + j) | none => throw "walk"
  let slot ← match (blks[b2i]?.bind (·.slots[idx]?)) with | some p => pure p.2 | none => throw "slot"
  pure ⟨c, L, H, blks, b2i, stop, slot.gasLimit⟩

/-- Components of `prepD0` timed separately (ns): decode, shuffles, congestion, scheduler, RS,
outgoing root. -/
def components (cb : Bytes) (h : Hint) : IO (List Nat) := do
  let (tDec, _) ← timeNs (fun _ => match decodeClaimE cb with
      | .ok c => (decodeLayout (c.epochs.headD ⟨[], 0, 0, [], []⟩).shardLayout).toOption.isSome.toNat +
          (c.blocks.map decodeBlk).length + ((decodeChunkInner c.chunkInner).toOption.map (·.tag)).getD 0
      | .error _ => 0) id
  let p ← IO.ofExcept (parts cb)
  let _ := h
  let srcBlks := (p.blks.drop p.b2i).take (p.stop - p.b2i)
  let (tShuf, _) ← timeNs (fun _ => (srcBlks.map fun S =>
      ((shuffleWithSeed (S.slots.filter fun (s, _) => s.heightIncluded == S.hdr.height) S.hdr.prevHash).map
        List.length).getD 0).sum) id
  let applied := p.blks[p.b2i]! :: (p.blks.take p.b2i)
  let ctxs := applied.zipIdx.map fun (M, i) =>
    blockCtx p.L p.H.shardId p.slotGas M (if i == 0 then (p.blks[p.b2i + 1]!).hdr.nextGasPrice else M.hdr.nextGasPrice)
  let (tCong, _) ← timeNs (fun _ => (ctxs.map fun ctx => (ctx.statuses.map fun (_, ci, missed) =>
      (Congestion.isFullyCongested CongestionConfig.pv86 (toCI ci) missed).toNat +
      prims.outGas ci missed ctx.own).sum).sum) id
  let (tSched, _) ← timeNs (fun _ => (ctxs.map fun ctx =>
      ((schedPub ctx).map fun p => p.reqs.length + p.allowed.size).getD 0).sum) id
  let body := u32 0 ++ encodeReceipts h.refunds
  let (tRS, _) ← timeNs (fun _ => ((encodedMerkleRoot p.c.rsDataParts p.c.rsTotalParts body).map (·.2)).getD 0) id
  let (tOut, _) ← timeNs (fun _ => (outgoingReceiptsRoot p.L h.refunds).length) id
  return [tDec, tShuf, tCong, tSched, tRS, tOut]

def header : String := "decode+chain  shuffles  congestion  schedPub  RS  outgoing_root  | prepD0 total (ms)"

def report (label : String) (cs : List Nat) (total : Nat) : IO Unit :=
  IO.println s!"{label}: {" ".intercalate (cs.map ms)} | {ms total}"

def benchFixtures (dirs : List String) : IO Unit := do
  IO.println header
  let mut sums := List.replicate 6 0
  let mut tot := 0
  let mut maxTot := 0
  let mut n := 0
  for dir in dirs do
    let cb := (← IO.FS.readBinFile (dir ++ "/claim.bin")).toList
    let wb := (← IO.FS.readBinFile (dir ++ "/witness.bin")).toList
    if checkD0a cb wb matches .error _ then continue
    let h := hintOf cb wb
    let (t, ok) ← timeNs (fun _ => match prepD0 cb h with
      | .ok p => p.sched.length + p.lists.length + p.body.length + 1 | .error _ => 0) id
    if ok == 0 then IO.println s!"{dir}: prepD0 failed"; continue
    let cs ← components cb h
    sums := (sums.zip cs).map fun (a, b) => a + b
    tot := tot + t
    maxTot := Nat.max maxTot t
    n := n + 1
  if n > 0 then
    report s!"mean over {n} accepted cases" (sums.map (· / n)) (tot / n)
    IO.println s!"max prepD0 total: {ms maxTot} ms"

/-! ## Synthetic 64-shard / 32-block claim -/

def encInner (ci : ChunkInner) : Bytes :=
  [UInt8.ofNat ci.tag] ++ ci.prevBlockHash ++ ci.prevStateRoot ++ ci.prevOutcomeRoot ++
  ci.encodedMerkleRoot ++ u64 ci.encodedLength ++ u64 ci.heightCreated ++ u64 ci.shardId ++
  u64 ci.prevGasUsed ++ u64 ci.gasLimit ++ u128 ci.prevBalanceBurnt ++
  ci.prevOutgoingReceiptsRoot ++ ci.txRoot ++ u32 0 ++
  [0] ++ u128 ci.congestion.delayedGas ++ u128 ci.congestion.bufferedGas ++
  u64 ci.congestion.receiptBytes ++ u16 ci.congestion.allowedShard ++
  [0] ++ u32 ci.bwRequests.length ++ concatAll (ci.bwRequests.map fun r => u16 r.toShard ++ r.bitmap) ++
  (if ci.tag == 4 then [0] else [])

def strB (s : String) : Bytes := s.toUTF8.toList

def pad2 (k : Nat) : String := if k < 10 then s!"0{k}" else s!"{k}"

/-- ShardLayout::V2 with `n` shards, ids `0..n-1`, boundaries `b01 … b(n-1)`. -/
def layoutV2 (n : Nat) : Bytes :=
  let ids := List.range n
  let pairs := ids.map fun i => u64 i ++ u64 i
  [2] ++ u32 (n - 1) ++ concatAll ((List.range' 1 (n - 1)).map fun k => borshBytes (strB s!"b{pad2 k}")) ++
  u32 n ++ concatAll (ids.map u64) ++ u32 n ++ concatAll pairs ++ u32 n ++ concatAll pairs ++
  [0] ++ [0] ++ u32 2

def setRange (b : Bytes) (off : Nat) (x : Bytes) : Bytes := b.take off ++ x ++ b.drop (off + x.length)

/-- Build the synthetic claim from a template (header byte layout, epoch id, chain id) and
`seed` (a runtime value, so nothing is precomputed at initialization). -/
def synthetic (tmpl : Claim) (seed : Nat) : Except String (Bytes × Hint) := do
  let n := 64
  let own := 5
  let nb := 32
  let b2i := 30
  let tb ← match tmpl.blocks.head? with | some b => pure b | none => throw "template"
  let lay := layoutV2 n
  let L ← decodeLayout lay
  let mkInner (sid h : Nat) (pbh : Bytes) : ChunkInner :=
    { tag := 3, prevBlockHash := pbh, prevStateRoot := sha256 (u64 (sid + seed)),
      prevOutcomeRoot := zeros 32, encodedMerkleRoot := sha256 (u64 (h * 100 + sid)),
      encodedLength := 8, heightCreated := h, shardId := sid, prevGasUsed := 0,
      gasLimit := 1000000000000000, prevBalanceBurnt := 0,
      prevOutgoingReceiptsRoot := sha256 (u64 (h * 1000 + sid + 7)), txRoot := zeros 32,
      proposals := [], congestion := ⟨0, 0, 0, sid⟩,
      bwRequests := ((List.range n).filter (· != sid)).map fun r => ⟨r, [255, 255, 255, 255, 255]⟩,
      proposedSplit := none }
  let heights := (List.range nb).map fun k => 100000 - k        -- newest first
  -- build oldest → newest
  let mut prev : Bytes := sha256 (u64 (seed + 42))
  let mut recs : List BlockRec := []
  let mut hashes : List Bytes := []
  for k in (List.range nb).reverse do
    let h := heights[k]!
    let slots : List ChunkSlot := (List.range n).map fun s =>
      let hi := if s != own then h else if k ≥ b2i then h else heights[b2i]!
      ⟨encInner (mkInner s hi prev), hi⟩
    let cis ← slots.mapM fun s => decodeChunkInner s.inner
    let chr := merklizeBorsh ((slots.zip cis).map fun (s, ci) => slotLeaf s ci)
    let lite := setRange tb.innerLite 0 (u64 h)
    let rest := setRange tb.innerRest 64 chr
    recs := ⟨5, prev, lite, rest, slots⟩ :: recs
    prev := blockHash prev lite rest
    hashes := prev :: hashes
  -- recs / hashes are now newest first
  let B2h := heights[b2i]!
  let idx := own
  let refundsEmpty : List Receipt := []
  let body := u32 0 ++ encodeReceipts refundsEmpty
  let (emr, len) ← match encodedMerkleRoot 33 100 body with | some r => pure r | none => throw "rs"
  let H : ChunkInner :=
    { mkInner own (heights[0]! + 1) hashes[0]! with
      encodedMerkleRoot := emr, encodedLength := len, bwRequests := [],
      prevOutgoingReceiptsRoot := outgoingReceiptsRoot L refundsEmpty,
      congestion := ⟨0, 0, 0, L.shardIds.getD ((B2h + idx) % n) own⟩ }
  let c : Claim :=
    { tmpl with chunkInner := encInner H, blocks := recs, rsDataParts := 33, rsTotalParts := 100,
                epochs := [⟨tmpl.epochId, 86, 1, lay, []⟩],
                epochStartAfter := List.replicate nb 0,
                applyFacts := List.replicate (1 + b2i) ⟨none, 0, none⟩, txValid := [],
                genesisChunkExtra := none }
  let hint : Hint := Hint.empty
  pure (c.encode, hint)

def decodeDetail (cb : Bytes) : IO Unit := do
  let (t1, _) ← timeNs (fun _ => match decodeClaimE cb with | .ok c => c.blocks.length | .error _ => 0) id
  let c ← IO.ofExcept (decodeClaimE cb)
  let (t2, _) ← timeNs (fun _ => (c.blocks.map fun r =>
      ((decodeBlockV6 r.headerVersion r.prevHash r.innerLite r.innerRest).toOption.map (·.height)).getD 0).sum) id
  let (t3, _) ← timeNs (fun _ => (c.blocks.map fun r =>
      (r.slots.map fun s => ((decodeChunkInner s.inner).toOption.map (·.shardId)).getD 0).sum).sum) id
  let cis := c.blocks.map fun r => r.slots.filterMap fun s => (decodeChunkInner s.inner).toOption.map (s, ·)
  let (t4, _) ← timeNs (fun _ => (cis.map fun l => (l.map fun (s, ci) => (slotLeaf s ci).length).sum).sum) id
  let (t5, _) ← timeNs (fun _ => (cis.map fun l => (merklizeBorsh (l.map fun (s, ci) => slotLeaf s ci)).length).sum) id
  IO.println s!"  detail: decodeClaimE {ms t1}, decodeBlockV6 {ms t2}, decodeChunkInner {ms t3}, slotLeaf (chunk hashes) {ms t4}, leaves+merklize {ms t5}"

def benchSynthetic (tmplDir : String) (seed : Nat) : IO Unit := do
  let tmpl ← IO.ofExcept (decodeClaimE (← IO.FS.readBinFile (tmplDir ++ "/claim.bin")).toList)
  let (cb, h) ← IO.ofExcept (synthetic tmpl seed)
  IO.println s!"synthetic claim: {cb.length} bytes"
  decodeDetail cb
  let (t, k) ← timeNs (fun _ => match prepD0 cb h with
      | .ok p => p.sched.length + p.lists.length + p.body.length | .error e => e.length * 1000000000) id
  let (te, len) ← timeNs (fun _ => match prepD0 cb h with | .ok p => p.encode.length | .error _ => 0) id
  IO.println s!"prepD0 (no encode) {ms t} ms; prepD0 + Prep.encode {ms te} ms, |Prep.encode| = {len} B"
  if k ≥ 1000000000 then
    IO.println s!"prepD0 FAILED: {(prepD0 cb h).toOption.isSome} {match prepD0 cb h with | .error e => e | .ok _ => ""}"
  IO.println header
  let cs ← components cb h
  report "synthetic 64 shards / 32 blocks / 31 scheduler runs" cs t

/-! ## Reed–Solomon and outgoing root at the A1 maximum -/

def benchRS (nBytes seed : Nat) : IO Unit := do
  let M := (List.range (1 <<< 20)).map fun i => UInt8.ofNat (i + seed)
  let (ts, _) ← timeNs (fun _ => (sha256 M).length) id
  IO.println s!"sha256 of 1 MiB: {ms ts} ms"
  let B := (List.range nBytes).map fun i => UInt8.ofNat ((i * 7 + seed) * 2654435761 / 65536)
  for (d, t) in [(33, 100), (85, 256)] do
    let (tm, _) ← timeNs (fun _ => (RSCode.new d t).map (·.parityTables.length) |>.getD 0) id
    let (te, _) ← timeNs (fun _ => ((encodedMerkleRoot d t B).map (·.2)).getD 0) id
    IO.println s!"RS ({d},{t}) body {nBytes} B: RSCode.new {ms tm} ms; encodedMerkleRoot total {ms te} ms"
  -- 4481 refunds (A1 maximum), receivers spread over 64 shards
  let L ← IO.ofExcept (decodeLayout (layoutV2 64))
  let refunds : List Receipt := (List.range 4481).map fun i =>
    { predecessorId := strB "system", receiverId := strB s!"b{pad2 (i % 64)}x{i + seed}",
      receiptId := sha256 (u64 (i + seed)), signerId := strB s!"b{pad2 (i % 64)}x{i}",
      signerPk := ⟨0, zeros 32⟩, gasPrice := 1000000000, deposit := 1000000000000 }
  let (to, _) ← timeNs (fun _ => (outgoingReceiptsRoot L refunds).length) id
  let body := u32 0 ++ encodeReceipts refunds
  let (tb, _) ← timeNs (fun _ => ((encodedMerkleRoot 33 100 body).map (·.2)).getD 0) id
  IO.println s!"outgoing root, 4481 refunds / 64 shards: {ms to} ms; body {body.length} B, RS (33,100) {ms tb} ms"

def main (args : List String) : IO UInt32 := do
  match args with
  | "fixtures" :: dirs => benchFixtures dirs
  | ["synthetic", tmpl] => benchSynthetic tmpl args.length
  | ["rs", n] => benchRS n.toNat! args.length
  | _ => IO.println "usage: nearspec-v3-bench fixtures DIR... | synthetic TEMPLATE_CASE_DIR | rs NBYTES"
  return 0
