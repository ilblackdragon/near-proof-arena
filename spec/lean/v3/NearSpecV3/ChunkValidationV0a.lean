import NearSpecV3.ChunkValidationV0

/-!
# `NearSpecV3.ChunkValidationV0a` — `RelD0a`: D0 with amendments A1, A2, Canon0f, A7–A10

Additive successor of `NearSpecV3.ChunkValidationV0` (which is pinned by the signed
challenge `near-chunk-validation-d0-1` and is not modified). The amended relation is a pure
restriction of `RelD0` (spec/near-chunk-validation-v0a.md, V3-D0-DESIGN §4, §10, §11):

  `RelD0a B cb w W Dp := RelD0 cb w ∧ A1 cb ∧ A2 cb w ∧ Canon0f cb w ∧ A7 B cb w ∧ A8 cb ∧
    A9 W cb w ∧ A10 Dp cb w`   (`W`, `Dp` default to the challenge's `W0 = 770,000`, `Dp0 = 32`)

* **A1** (`c.gas_limit`): the chunk `gas_limit` in the last-new-chunk block's (B2) slot of the
  validated shard is at most `10^15` (mainnet genesis, 1000 Tgas). nearcore never changes a
  chunk gas limit after genesis (V3-D0-DESIGN §10.1).
* **A2** (`w.proof_routing`): every receipt of every *used* source receipt proof (the entry the
  last-wins lookup selects for a new source chunk) routes, under the epoch's layout, to the
  validated shard. Holds on every honest single-epoch witness (§10.1).
* **A7** (`w.unfolded`, round-2 lead decision): `unfoldBytes cb w ≤ B` (below).
* **A8** (`c.bw_requests`, lead decision): in every block of the claim's segment, every chunk
  slot's `BandwidthRequests` has at most one request per `to_shard`. nearcore builds the list
  with one `generate_bandwidth_request` per layout shard id
  (`runtime/runtime/src/congestion_control.rs:503-523`) and rejects a chunk header whose
  requests differ from the chunk extra's (`chain/chain/src/validate.rs:280-298`), so every
  chunk header of a valid chain satisfies it. Claim-only.
* **A9** (`e.chacha_words`, user decision 2026-10-09): the scheduler runs of all applied
  transitions draw at most `W` ChaCha20 words in total (`chachaWords cb w ≤ W`, below). Not a
  nearcore invariant (the count depends on hash outputs); it bounds the in-AIR ChaCha lane.
* **A10** (`w.path_depth`, user decision 2026-10-09): every used source receipt proof's Merkle
  path has at most `Dp` items. nearcore produces `⌈log₂ #shards⌉ ≤ 6`; it bounds the in-AIR
  source-proof table.
* **Canon0f** (`e.sched_canonical`): every `BandwidthSchedulerState` value the D0 run reads at
  `0x0f` — in the main pre-state and in each implicit transition's pre-state — is absent or
  decodes as `V1` whose links are exactly the layout's `n²` links `(sender, receiver)` in
  sender-major order (any allowances, any sanity hash): what `update_scheduler_state`
  writes for this layout (`runtime/runtime/src/bandwidth_scheduler/scheduler.rs:548-562`,
  links from `iter_links`, sender-major, every link has an allowance after
  `increase_allowances`), and nothing else writes the key (spec/near-chunk-validation-v0a.md
  §2.3 has the source check).

The predicates are total `Bool` functions of `(cb, w)`; where the pair does not even
decode they return `false` (irrelevant: `RelD0` is false there). They read the trie through
the witness's own declared roots (`main.post_state_root`, `implicit[k].post_state_root`),
which `RelD0` checks against the relation's computed roots.

`checkD0a B` is the executable verdict (`.ok ()` ⇔ `RelD0a B`, by `relD0a_iff`).
-/

namespace NearSpecV3

open NearSpec

/-- A1 bound: mainnet genesis chunk gas limit (1000 Tgas). -/
def maxGasLimitD0 : Nat := 1000000000000000

/-- The claim-side walk of `checkD0` (same functions, same order, no checks beyond what is
needed to compute): segment blocks, B2, implicit and source blocks, B2's own slot. -/
structure WalkD0 where
  c : Claim
  H : ChunkInner
  L : Layout
  idx : Nat
  blks : List Blk
  b2i : Nat
  stop : Nat
  slotB2 : ChunkInner
  implicitBlks : List Blk
  sourceBlks : List Blk

def walkD0 (cb : Bytes) : Except String WalkD0 := do
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
  let slotB2 ← match (blks[b2i]?.bind (·.slots[idx]?)) with
    | some p => pure p.2 | none => throw "slot"
  pure ⟨c, H, L, idx, blks, b2i, stop, slotB2, (blks.take b2i).reverse,
        (blks.drop b2i).take (stop - b2i)⟩

def decodeW (w : Bytes) : Except String StateWitness := do
  let (sw, _) ← decodeWitnessFile w
  decodeStateWitness sw

/-- A1 (`c.gas_limit`). -/
def a1 (cb : Bytes) : Bool :=
  match walkD0 cb with
  | .ok k => decide (k.slotB2.gasLimit ≤ maxGasLimitD0)
  | .error _ => false

/-- The used source proofs, in walk order (block newest first, slot order). -/
def usedProofs (k : WalkD0) (w : StateWitness) : List ProofEntry :=
  k.sourceBlks.flatMap fun S => S.slots.filterMap fun (s, ci) =>
    if s.heightIncluded == S.hdr.height then lookupLast (chunkHash s.inner ci.encodedMerkleRoot) w.entries
    else none

/-- A2 (`w.proof_routing`). -/
def a2 (cb w : Bytes) : Bool :=
  match walkD0 cb, decodeW w with
  | .ok k, .ok sw => (usedProofs k sw).all fun e => e.receipts.all fun r => k.L.shardOf r.receiverId == k.H.shardId
  | _, _ => false

/-- The layout's links, sender-major (`iter_links`). -/
def layoutLinks (L : Layout) : List (Nat × Nat) :=
  L.shardIds.flatMap fun s => L.shardIds.map fun r => (s, r)

/-- A `0x0f` value is canonical for the layout. -/
def canonical0f (L : Layout) : Option Bytes → Bool
  | none => true
  | some v => match NearSpec.Bandwidth.State.decode v with
    | some st => st.links.map (fun la => (la.sender, la.receiver)) == layoutLinks L
    | none => false

/-- The `0x0f` values read by the D0 run: main pre-state, then each implicit pre-state. -/
def reads0f (k : WalkD0) (w : StateWitness) : List (Option Bytes) :=
  let find (vals : List Bytes) (root : Bytes) : Option Bytes :=
    ((partialTrie vals root [keyBwState]).find keyBwState).getD none
  let roots := w.main.postStateRoot :: w.implicit.map (·.postStateRoot)
  find w.main.values k.slotB2.prevStateRoot :: (w.implicit.zip roots).map fun (T, r) => find T.values r

/-- Canon0f (`e.sched_canonical`). -/
def canon0f (cb w : Bytes) : Bool :=
  match walkD0 cb, decodeW w with
  | .ok k, .ok sw => (reads0f k sw).all (canonical0f k.L)
  | _, _ => false

/-! ## A7 `w.unfolded`: revealed bytes of the built tries, unfolded per path copy

Mirrors what the AIR hashes (STATUS-V3-TRIE §1.3/§1.4, `UnfoldBound`): tree-shaped records,
one per *occurrence* of a revealed node in the partial trie `partialTrie ws root keys`
(a subtree shared by several slots is revealed — and hashed — once per path copy).
For each applied transition τ (main, then each implicit one, as `checkD0` runs them):

* `unfoldedBytesT pre_τ` = Σ `|nodeEnc o|` over the revealed node occurrences `o` of the
  pre-trie plus Σ `|v|` over its revealed values (`occs`, `nodeEnc`, `valsOf`: identical to
  `ZkFormal.NearV3.Spec` on lane v3-trie, so `UnfoldBound e ws root keys ↔
  unfoldedBytesT (partialTrie ws root keys) ≤ e` by `rfl`);
* `diffT pre_τ post_τ` = the post-write path copies: the bytes of every revealed node
  occurrence of the post-trie whose encoding differs from the pre-trie's at the same
  position, plus every changed revealed value. The post-trie is rebuilt from the store
  (`ws` plus the post nodes and values) along the same keys (`rebuildPost`), i.e. the
  post-state as a store would present it.

`unfoldBytes cb w = Σ_τ (unfoldedBytesT pre_τ + diffT pre_τ post_τ)` (0 if the run fails;
then `RelD0` is false anyway). -/

mutual
def occs : PTrie → List PTrie
  | .hash _ => []
  | .leaf k v m => [.leaf k v m]
  | .ext k c m => .ext k c m :: occs c
  | .branch v cs m => .branch v cs m :: kOccs cs
def kOccs : Kids → List PTrie
  | .nil => []
  | .none r => kOccs r
  | .some c r => occs c ++ kOccs r
end

def slotVal : Slot → List Bytes
  | .val v => [v]
  | .ref _ _ => []

def optSlotVal : Option Slot → List Bytes
  | some s => slotVal s
  | none => []

def ownVals : PTrie → List Bytes
  | .leaf _ s _ => slotVal s
  | .branch v _ _ => optSlotVal v
  | _ => []

def valsOf (t : PTrie) : List Bytes := (occs t).flatMap ownVals

def nodeEnc : PTrie → Bytes
  | .hash _ => []
  | .leaf k v mem => [0] ++ u32 (hexPrefix k true).length ++ hexPrefix k true ++ v.valueRef ++ u64 mem
  | .ext k c mem => [3] ++ u32 (hexPrefix k false).length ++ hexPrefix k false ++ c.hashOf ++ u64 mem
  | .branch none cs mem => [1] ++ u16 (kidsBitmap cs 0) ++ Kids.hashes cs ++ u64 mem
  | .branch (some v) cs mem => [2] ++ v.valueRef ++ u16 (kidsBitmap cs 0) ++ Kids.hashes cs ++ u64 mem

def unfoldedBytesT (t : PTrie) : Nat :=
  ((occs t).map fun o => (nodeEnc o).length).sum + ((valsOf t).map List.length).sum

def isRevealed : PTrie → Bool
  | .hash _ => false
  | _ => true

/-- Child `i` of a pre-trie branch (`.hash []` = no revealed counterpart). -/
def kidAt : Kids → Nat → PTrie
  | .nil, _ => .hash []
  | .none _, 0 => .hash []
  | .some c _, 0 => c
  | .none r, i + 1 => kidAt r i
  | .some _ r, i + 1 => kidAt r i

def preKids : PTrie → Kids
  | .branch _ cs _ => cs
  | _ => .nil

def preExtChild (k : List Nat) : PTrie → PTrie
  | .ext k' c _ => if k' == k then c else .hash []
  | _ => .hash []

def preLeafSlot (k : List Nat) : PTrie → Option Slot
  | .leaf k' v _ => if k' == k then some v else none
  | _ => none

def preBranchSlot : PTrie → Option Slot
  | .branch v _ _ => v
  | _ => none

/-- Bytes of a post value slot that is revealed and changed. -/
def slotDiff (pre post : Option Slot) : Nat :=
  match post with
  | some s =>
    if (pre.map Slot.valueRef) == some s.valueRef then 0 else ((slotVal s).map List.length).sum
  | none => 0

mutual
def diffT : PTrie → PTrie → Nat
  | _, .hash _ => 0
  | pre, .leaf k v m =>
    if isRevealed pre && nodeEnc pre == nodeEnc (.leaf k v m) then 0 else
    (nodeEnc (.leaf k v m)).length + slotDiff (preLeafSlot k pre) (some v)
  | pre, .ext k c m =>
    if isRevealed pre && nodeEnc pre == nodeEnc (.ext k c m) then 0 else
    (nodeEnc (.ext k c m)).length + diffT (preExtChild k pre) c
  | pre, .branch v cs m =>
    if isRevealed pre && nodeEnc pre == nodeEnc (.branch v cs m) then 0 else
    (nodeEnc (.branch v cs m)).length + slotDiff (preBranchSlot pre) v + kDiff (preKids pre) 0 cs
def kDiff : Kids → Nat → Kids → Nat
  | _, _, .nil => 0
  | pk, i, .none r => kDiff pk (i + 1) r
  | pk, i, .some c r => diffT (kidAt pk i) c + kDiff pk (i + 1) r
end

/-- The post-trie as a store presents it: rebuilt from `ws` and the post nodes/values along `keys`. -/
def rebuildPost (ws : List Bytes) (post : PTrie) (keys : List (List Nat)) : PTrie :=
  partialTrie (ws ++ (occs post).map nodeEnc ++ valsOf post) post.hashOf keys

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

/-- `(pre_τ, post_τ)` for every applied transition, as `checkD0` builds and runs them. -/
def triesD0 (cb wb : Bytes) : Except String (List (PTrie × PTrie)) := do
  let k ← walkD0 cb
  let w ← decodeW wb
  let B2 ← match k.blks[k.b2i]? with | some b => pure b | none => throw "walk"
  let prevB2 ← match k.blks[k.b2i + 1]? with | some b => pure b | none => throw "walk"
  let receipts := appliedReceipts k w
  let ctxB2 := blockCtx k.L k.H.shardId k.slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  let t0 := partialTrie w.main.values k.slotB2.prevStateRoot [keyBufferedIdx]
  let bshards ← match t0.find keyBufferedIdx with
    | some v => bufferedShards v | none => throw "missing"
  let keys := mainKeys receipts bshards
  let tMain := partialTrie w.main.values k.slotB2.prevStateRoot keys
  let out ← applyNewChunk prims ctxB2 tMain receipts
  let mut acc : List (PTrie × PTrie) := [(tMain, rebuildPost w.main.values out.trie keys)]
  let mut root := out.trie.hashOf
  for (M, T) in k.implicitBlks.zip w.implicit do
    let ctxM := blockCtx k.L k.H.shardId k.slotB2.gasLimit M M.hdr.nextGasPrice
    let ks := [keyDelayedIdx, keyBwState]
    let tM := partialTrie T.values root ks
    let tM' ← applyMissingChunk prims ctxM tM
    acc := acc ++ [(tM, rebuildPost T.values tM' ks)]
    root := tM'.hashOf
  pure acc

def unfoldBytes (cb w : Bytes) : Nat :=
  match triesD0 cb w with
  | .ok l => (l.map fun (pre, post) => unfoldedBytesT pre + diffT pre post).sum
  | .error _ => 0

/-- A7 (`w.unfolded`). -/
def a7 (B : Nat) (cb w : Bytes) : Bool := decide (unfoldBytes cb w ≤ B)

/-- A8 (`c.bw_requests`): per block slot of the segment, distinct `to_shard`s. -/
def a8 (cb : Bytes) : Bool :=
  match walkD0 cb with
  | .ok k => k.blks.all fun b => b.slots.all fun (_, ci) => decide (ci.bwRequests.map (·.toShard)).Nodup
  | .error _ => false

/-! ## A9 `e.chacha_words`: ChaCha20 words drawn by the scheduler runs

Every applied transition τ (main, then each implicit one) runs `Scheduler.run` once, with a
fresh `Rng.ofSeed prev_block_hash`; the only RNG use is the bucket shuffle of
`processRequests` (`requests.shuffle(&mut self.rng)`, scheduler.rs:362). The words a run
draws are its RNG's stream position afterwards, `16·ctr − |buf|` (`Scheduler.rngWords`; nearcore
`ChaCha20Rng::get_word_pos`). `chachaWords cb w` = Σ_τ words drawn by τ's run (0 if the run
fails; then `RelD0` is false anyway). The run's inputs are exactly `prims.sched`'s
(`schedInsD0` rebuilds them from `triesD0`'s pre-tries and the walk's block contexts), and
`Scheduler.run_eq_mid` (**proved**) shows that `run` continues from the very state whose RNG
is counted.

The fuel bound alone does not bound the total (`ZkFormal…Sched.Complete.worstK`: ≈ 9.9 M
words); `W0 = 770,000` (user decision 2026-10-09) keeps the in-AIR ChaCha lane at
`86·⌈K/16⌉ ≤ 4,141,410 < 2^22` rows (`lane_770k_22`). -/

namespace Scheduler

/-- Stream position of an RNG that started at `Rng.ofSeed` (`ctr = 0`, `buf = []`): the
number of 32-bit words drawn so far. -/
def rngWords (r : NearSpecV3.Rng) : Nat := 16 * r.ctr - r.buf.length

/-- `run`'s intermediate result after `process_bandwidth_requests` (the last RNG use). -/
structure Mid where
  prev : NearSpec.Bandwidth.State
  p : Params
  allowed : Array Bool
  st : St

/-- `run` up to and including `processRequests` (the same steps, verbatim). -/
def runMid (cfg : Config) (cc : CongestionConfig) (ids : List Nat) (prevState : Option Bytes)
    (congestion : List (Nat × CongestionInfo × Nat))
    (requests : List (Nat × List BandwidthRequest)) (prevBlockHash : Bytes) : Option Mid := do
  let prev ← match prevState with
    | none => some NearSpec.Bandwidth.State.initial
    | some b => NearSpec.Bandwidth.State.decode b
  let n := ids.length
  if n = 0 then none
  let p ← Params.calculate cfg n
  let status := statuses cc ids congestion
  let links := List.range (n * n)
  let allowed : Array Bool := (links.map fun l => linkAllowed status (l / n) (l % n)).toArray
  let allow0 := prev.links.foldl (fun (a : Array Nat) la =>
      match indexOf ids la.sender, indexOf ids la.receiver with
      | some s, some r => a.set! (s * n + r) la.allowance
      | _, _ => a) (Array.replicate (n * n) 0)
  let reqs := convertRequests p ids requests
  let st : St := ⟨Array.replicate n p.maxShardBandwidth, Array.replicate n p.maxShardBandwidth,
    allow0, Array.replicate (n * n) 0, Rng.ofSeed prevBlockHash⟩
  let fair := p.maxShardBandwidth / n
  let st := { st with allowance := st.allowance.map fun a => Nat.min (Nat.min (a + fair) u64Max) p.maxAllowance }
  let st := links.foldl (fun st l => (tryGrant n allowed st l p.base).2) st
  let st ← processRequests n allowed st reqs
  some ⟨prev, p, allowed, st⟩

/-- The rest of `run` (no RNG use). -/
def finish (ids : List Nat) (m : Mid) : Output :=
  let n := ids.length
  let links := List.range (n * n)
  let st := distribute n m.allowed m.st
  let sid (i : Nat) : Nat := ids.getD i 0
  let newLinks : List NearSpec.Bandwidth.LinkAllowance :=
    links.map fun l => ⟨sid (l / n), sid (l % n), st.allowance[l]!⟩
  let allShards := u32 n ++ concatAll (ids.map u64)
  let newState : NearSpec.Bandwidth.State :=
    ⟨newLinks, sha256 (m.prev.sanityHash ++ sha256 allShards)⟩
  ⟨newState.encode, links.map fun l => ((sid (l / n), sid (l % n)), st.granted[l]!), m.p⟩

/-- **`run` factors through `runMid`**: the counted RNG is the run's own. -/
theorem run_eq_mid (cfg : Config) (cc : CongestionConfig) (ids : List Nat) (prev : Option Bytes)
    (cong : List (Nat × CongestionInfo × Nat)) (req : List (Nat × List BandwidthRequest))
    (seed : Bytes) :
    run cfg cc ids prev cong req seed = (runMid cfg cc ids prev cong req seed).map (finish ids) := by
  unfold run runMid finish
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
      | none =>
        simp only [hn, hp, Option.bind, ↓reduceIte, bind]
        generalize processRequests _ _ _ _ = r
        cases r <;> rfl
      | some b =>
        cases hd : NearSpec.Bandwidth.State.decode b with
        | none => simp only [hn, hp, hd, Option.bind, ↓reduceIte, bind]; rfl
        | some st =>
          simp only [hn, hp, hd, Option.bind, ↓reduceIte, bind]
          generalize processRequests _ _ _ _ = r
          cases r <;> rfl

/-- Words drawn by one run (`0` if the run aborts). -/
def wordsDrawn (cfg : Config) (cc : CongestionConfig) (ids : List Nat) (prevState : Option Bytes)
    (congestion : List (Nat × CongestionInfo × Nat))
    (requests : List (Nat × List BandwidthRequest)) (prevBlockHash : Bytes) : Nat :=
  match runMid cfg cc ids prevState congestion requests prevBlockHash with
  | some m => rngWords m.st.rng
  | none => 0

end Scheduler

/-- Words drawn by the run `prims.sched i` (same argument conversion as `prims`). -/
def schedWords (i : SchedIn) : Nat :=
  Scheduler.wordsDrawn Scheduler.Config.pv86 CongestionConfig.pv86 i.shardIds i.prev
    (i.statuses.map fun (s, c, m) => (s, toCI c, m))
    (i.requests.map fun (s, rs) => (s, rs.map fun r => ⟨r.toShard, r.bitmap⟩))
    i.prevBlockHash

/-- `prims.sched i` is `runMid` on the counted arguments, then `finish`. -/
theorem prims_sched_eq_mid (i : SchedIn) :
    prims.sched i =
      ((Scheduler.runMid Scheduler.Config.pv86 CongestionConfig.pv86 i.shardIds i.prev
        (i.statuses.map fun (s, c, m) => (s, toCI c, m))
        (i.requests.map fun (s, rs) => (s, rs.map fun r => ⟨r.toShard, r.bitmap⟩))
        i.prevBlockHash).map (Scheduler.finish i.shardIds)).map fun o =>
          ⟨o.state, fun a b => ((o.granted.find? (·.1 == (a, b))).map (·.2)).getD 0⟩ := by
  show (Scheduler.run _ _ _ _ _ _ _).map _ = _
  rw [Scheduler.run_eq_mid]

/-- The scheduler inputs of every applied transition, in `checkD0`'s order (main at B2, then
each implicit block oldest first): the block context's layout, own shard, slot statuses,
requests and `prev_hash`, and the `0x0f` value of the transition's pre-trie
(`schedStep` reads it with `readKey t keyBwState`). -/
def schedInsD0 (cb wb : Bytes) : Except String (List SchedIn) := do
  let k ← walkD0 cb
  let w ← decodeW wb
  let B2 ← match k.blks[k.b2i]? with | some b => pure b | none => throw "walk"
  let prevB2 ← match k.blks[k.b2i + 1]? with | some b => pure b | none => throw "walk"
  let ts ← triesD0 cb wb
  let ctxs := blockCtx k.L k.H.shardId k.slotB2.gasLimit B2 prevB2.hdr.nextGasPrice ::
    (k.implicitBlks.zip w.implicit).map fun (M, _) =>
      blockCtx k.L k.H.shardId k.slotB2.gasLimit M M.hdr.nextGasPrice
  pure ((ctxs.zip ts).map fun (ctx, pre, _) =>
    ⟨ctx.layout.shardIds, ctx.own, (pre.find keyBwState).getD none, ctx.statuses, ctx.requests,
     ctx.prevBlockHash⟩)

/-- Σ ChaCha20 words drawn by all scheduler runs of the claim. -/
def chachaWords (cb w : Bytes) : Nat :=
  match schedInsD0 cb w with
  | .ok l => (l.map schedWords).sum
  | .error _ => 0

/-- A9 (`e.chacha_words`). -/
def a9 (W : Nat) (cb w : Bytes) : Bool := decide (chachaWords cb w ≤ W)

/-- A9 bound of the challenge instance (user decision 2026-10-09; derivation
spec/near-chunk-validation-v0a.md §2.6). -/
def W0 : Nat := 770000

/-! ## A10 `w.path_depth`: Merkle-path length of the used source receipt proofs

`verifyReceiptProof` accepts a path of any length (`rootFromPath`); nearcore's producer
emits `⌈log₂ #shards⌉ ≤ 6` items. The in-AIR source table (`srcpV3`) spends
`33 + 64·|path|` rows per used proof, so a per-proof bound `Dp` bounds its height:
`1984 · (33 + 64·32) = 4,128,704 ≤ 2^22` and `1984 · (33 + 64·33) > 2^22`
(`ZkFormal.NearV3.Rcpt.SrcpDepth`). `Dp0 = 32` (user decision 2026-10-09; the largest depth
that fits; spec v0a §2.7). -/

/-- Longest Merkle path of a used source proof (`0` if none / undecodable). -/
def maxPathDepth (cb w : Bytes) : Nat :=
  match walkD0 cb, decodeW w with
  | .ok k, .ok sw => ((usedProofs k sw).map fun e => e.proof.path.length).foldr max 0
  | _, _ => 0

/-- A10 (`w.path_depth`). -/
def a10 (Dp : Nat) (cb w : Bytes) : Bool :=
  match walkD0 cb, decodeW w with
  | .ok k, .ok sw => (usedProofs k sw).all fun e => decide (e.proof.path.length ≤ Dp)
  | _, _ => false

/-- A10 bound of the challenge instance. -/
def Dp0 : Nat := 32

/-- **The D0a relation**, with the unfolded-size bound `B` a parameter (the challenge
instance is `B0`, `ChallengeD0a`), and the A9 word bound `W` and A10 depth bound `Dp`
defaulting to the challenge's `W0`, `Dp0`. -/
def RelD0a (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0) : Prop :=
  RelD0 cb w ∧ a1 cb = true ∧ a2 cb w = true ∧ canon0f cb w = true ∧ a7 B cb w = true ∧
    a8 cb = true ∧ a9 W cb w = true ∧ a10 Dp cb w = true

instance (B : Nat) (cb w : Bytes) (W Dp : Nat) : Decidable (RelD0a B cb w W Dp) := by
  unfold RelD0a; infer_instance

/-- Executable verdict: `checkD0`, then the amendments (each reported as out of domain). -/
def checkD0a (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0) : Except String Unit := do
  checkD0 cb w
  check (a1 cb) "out of domain (c.gas_limit): chunk gas_limit above 10^15"
  check (a2 cb w) "out of domain (w.proof_routing): a used receipt proof holds a receipt routed to another shard"
  check (canon0f cb w) "out of domain (e.sched_canonical): 0x0f value is not the layout's canonical link list"
  check (a7 B cb w) "out of domain (w.unfolded): unfolded trie bytes above the bound"
  check (a8 cb) "out of domain (c.bw_requests): a chunk's bandwidth requests repeat a to_shard"
  check (a9 W cb w) "out of domain (e.chacha_words): scheduler runs draw more ChaCha20 words than the bound"
  check (a10 Dp cb w) "out of domain (w.path_depth): a used receipt proof's Merkle path is longer than the bound"

theorem relD0a_iff (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0) :
    RelD0a B cb w W Dp ↔ checkD0a B cb w W Dp = .ok () := by
  unfold RelD0a RelD0 acceptsD0 checkD0a check
  cases h : checkD0 cb w with
  | error e => simp [bind, Except.bind]
  | ok u =>
    cases a1 cb <;> cases a2 cb w <;> cases canon0f cb w <;> cases a7 B cb w <;> cases a8 cb <;>
      cases a9 W cb w <;> cases a10 Dp cb w <;>
      simp [bind, Except.bind]

/-- A7 bound of the challenge instance: unfolded trie bytes (pre + post-write copies, all
transitions); `B0 = 2,000,000` (lead decision, user-approved; derivation
spec/near-chunk-validation-v0a.md §2.4: 1.25 SHA rows/byte · 2 M = 2.5 M of 2^22 rows). -/
def B0 : Nat := 2000000

/-- The D0a domain conditions at bound `B` (Bool form). -/
def inD0a (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0) : Bool :=
  a1 cb && a2 cb w && canon0f cb w && a7 B cb w && a8 cb && a9 W cb w && a10 Dp cb w

/-- The D0a domain conditions at bound `B`. -/
def InD0a (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0) : Prop :=
  a1 cb = true ∧ a2 cb w = true ∧ canon0f cb w = true ∧ a7 B cb w = true ∧ a8 cb = true ∧
    a9 W cb w = true ∧ a10 Dp cb w = true

/-- The D0a domain at the challenge bounds `B0`, `W0`, `Dp0`. -/
def InD0a0 (cb w : Bytes) : Prop := InD0a B0 cb w

theorem inD0a_iff (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0) :
    inD0a B cb w W Dp = true ↔ InD0a B cb w W Dp := by
  unfold inD0a InD0a
  simp only [Bool.and_eq_true, and_assoc]

instance (B : Nat) (cb w : Bytes) (W Dp : Nat) : Decidable (InD0a B cb w W Dp) :=
  decidable_of_iff _ (inD0a_iff B cb w W Dp)

instance (cb w : Bytes) : Decidable (InD0a0 cb w) := by unfold InD0a0; infer_instance

/-- `RelD0a B` is `RelD0` restricted to the domain `InD0a B`. -/
theorem relD0a_iff_inD0a (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0) :
    RelD0a B cb w W Dp ↔ RelD0 cb w ∧ InD0a B cb w W Dp :=
  Iff.rfl

/-- Same at the challenge bounds. -/
theorem relD0a_iff_in (cb w : Bytes) : RelD0a B0 cb w ↔ RelD0 cb w ∧ InD0a0 cb w := Iff.rfl

/-- Soundness direction: every D0a witness is a D0 witness (for all bounds). -/
theorem relD0a_relD0 {B : Nat} {cb w : Bytes} {W Dp : Nat} (h : RelD0a B cb w W Dp) :
    RelD0 cb w := h.1

/-- The bounds are monotone (each of `B`, `W`, `Dp`). -/
theorem relD0a_mono_all {B B' W W' Dp Dp' : Nat} (hB : B ≤ B') (hW : W ≤ W') (hD : Dp ≤ Dp')
    {cb w : Bytes} (h : RelD0a B cb w W Dp) : RelD0a B' cb w W' Dp' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h0, h1, h2, h3, ?_, h5, ?_, ?_⟩
  · unfold a7 at *
    simp only [decide_eq_true_eq] at *
    omega
  · unfold a9 at *
    simp only [decide_eq_true_eq] at *
    omega
  · unfold a10 at *
    revert h7
    split
    · simp only [List.all_eq_true, decide_eq_true_eq]
      exact fun h e he => Nat.le_trans (h e he) hD
    · exact id

/-- The A7 bound is monotone (at any fixed `W`, `Dp`). -/
theorem relD0a_mono {B B' : Nat} (hB : B ≤ B') {cb w : Bytes} {W Dp : Nat}
    (h : RelD0a B cb w W Dp) : RelD0a B' cb w W Dp :=
  relD0a_mono_all hB (Nat.le_refl W) (Nat.le_refl Dp) h

end NearSpecV3
