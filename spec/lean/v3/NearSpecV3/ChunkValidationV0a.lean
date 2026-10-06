import NearSpecV3.ChunkValidationV0

/-!
# `NearSpecV3.ChunkValidationV0a` — `RelD0a`: D0 with amendments A1, A2, Canon0f

Additive successor of `NearSpecV3.ChunkValidationV0` (which is pinned by the signed
challenge `near-chunk-validation-d0-1` and is not modified). The amended relation is a pure
restriction of `RelD0` (spec/near-chunk-validation-v0a.md, V3-D0-DESIGN §4, §10, §11):

  `RelD0a cb w := RelD0 cb w ∧ A1 cb ∧ A2 cb w ∧ Canon0f cb w`

* **A1** (`c.gas_limit`): the chunk `gas_limit` in the last-new-chunk block's (B2) slot of the
  validated shard is at most `10^15` (mainnet genesis, 1000 Tgas). nearcore never changes a
  chunk gas limit after genesis (V3-D0-DESIGN §10.1).
* **A2** (`w.proof_routing`): every receipt of every *used* source receipt proof (the entry the
  last-wins lookup selects for a new source chunk) routes, under the epoch's layout, to the
  validated shard. Holds on every honest single-epoch witness (§10.1).
* **Canon0f** (`e.sched_canonical`): every `BandwidthSchedulerState` value the D0 run reads at
  `0x0f` — in the main pre-state and in each implicit transition's pre-state — is absent or
  decodes as `V1` whose links are exactly the layout's `n²` links `(sender, receiver)` in
  sender-major order (any allowances, any sanity hash): what `update_scheduler_state`
  writes for this layout (`runtime/runtime/src/bandwidth_scheduler/scheduler.rs:548-562`,
  links from `iter_links`, sender-major, every link has an allowance after
  `increase_allowances`), and nothing else writes the key (spec/near-chunk-validation-v0a.md
  §2.3 has the source check).

The three predicates are total `Bool` functions of `(cb, w)`; where the pair does not even
decode they return `false` (irrelevant: `RelD0` is false there). They read the trie through
the witness's own declared roots (`main.post_state_root`, `implicit[k].post_state_root`),
which `RelD0` checks against the relation's computed roots.

`checkD0a` is the executable verdict (`.ok ()` ⇔ `RelD0a`, by `relD0a_iff`).
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

def RelD0a (cb w : Bytes) : Prop :=
  RelD0 cb w ∧ a1 cb = true ∧ a2 cb w = true ∧ canon0f cb w = true

instance (cb w : Bytes) : Decidable (RelD0a cb w) := by unfold RelD0a; infer_instance

/-- Executable verdict: `checkD0`, then the amendments (each reported as out of domain). -/
def checkD0a (cb w : Bytes) : Except String Unit := do
  checkD0 cb w
  check (a1 cb) "out of domain (c.gas_limit): chunk gas_limit above 10^15"
  check (a2 cb w) "out of domain (w.proof_routing): a used receipt proof holds a receipt routed to another shard"
  check (canon0f cb w) "out of domain (e.sched_canonical): 0x0f value is not the layout's canonical link list"

theorem relD0a_iff (cb w : Bytes) : RelD0a cb w ↔ checkD0a cb w = .ok () := by
  unfold RelD0a RelD0 acceptsD0 checkD0a check
  cases h : checkD0 cb w with
  | error e => simp [bind, Except.bind]
  | ok u =>
    cases a1 cb <;> cases a2 cb w <;> cases canon0f cb w <;> simp [bind, Except.bind, pure, Except.pure]

end NearSpecV3
