import NearSpec.TransferV1
import NearSpec.TrieUpsert
import NearSpec.Bandwidth

/-!
# `near/pv86/receipt-transfer-batch/v1` — the real post-state root

Trusted root of challenge `near-transfer-receipt-v2` (claim format
`near-arena-claim-v2`, `spec/claim-v2.md`; semantics
`spec/near-transfer-receipt-v2.md`). Same receipt semantics as v1
(`NearSpec.TransferV1.applyReceipt`, reused unchanged), plus the
bandwidth-scheduler state write that `Runtime::apply` performs on every chunk,
for a shard layout with exactly one shard. Hence `postStateRoot` IS nearcore's
`ApplyResult.state_root` (= `ChunkExtra.state_root` = the next chunk header's
`prev_state_root`) for a chunk in the domain — not a projection.

Order inside `Runtime::apply` (`runtime/runtime/src/lib.rs:1740-1810`):
validator updates (none) → load delayed queue (empty) → **bandwidth scheduler**
(`run_bandwidth_scheduler`, writes `0x0f`) → receipt sink (forwards buffered
receipts: none) → transactions (none) → incoming receipts (the batch). Key
`0x0f` is disjoint from every `Account` key, so the two writes commute; the
relation follows nearcore's order anyway.
-/

namespace NearSpec.TransferV2

open NearSpec

/-! ## Claim -/

structure Claim where
  protocolVersion : Nat
  chainId : Bytes
  shardId : Nat
  blockHeight : Nat
  blockGasPrice : Nat
  gasLimit : Nat
  /-- `CongestionInfoV1` of the shard in the block (`apply_state.congestion_info[S]`). -/
  delayedReceiptsGas : Nat
  bufferedReceiptsGas : Nat
  receiptBytes : Nat
  allowedShard : Nat
  /-- `ExtendedCongestionInfo::missed_chunks_count` of the shard. -/
  missedChunksCount : Nat
  preStateRoot : Bytes
  receiptCount : Nat
  receiptsCommitment : Bytes
  /-- The real `Runtime::apply` post-state root. -/
  postStateRoot : Bytes
  outcomeRoot : Bytes
  refundCount : Nat
  refundsCommitment : Bytes
  gasBurntTotal : Nat
  tokensBurntTotal : Nat
  deriving DecidableEq, Repr

/-- `"near-arena-claim-v2"` -/
def claimFormat : Bytes :=
  [110, 101, 97, 114, 45, 97, 114, 101, 110, 97, 45, 99, 108, 97, 105, 109, 45, 118, 50]
/-- `"near/pv86/receipt-transfer-batch/v1"` -/
def statementId : Bytes :=
  [110, 101, 97, 114, 47, 112, 118, 56, 54, 47, 114, 101, 99, 101, 105, 112, 116, 45, 116,
   114, 97, 110, 115, 102, 101, 114, 45, 98, 97, 116, 99, 104, 47, 118, 49]

def Claim.encode (c : Claim) : Bytes :=
  borshBytes claimFormat ++ borshBytes statementId ++
  u32 c.protocolVersion ++ borshBytes c.chainId ++ u64 c.shardId ++ u64 c.blockHeight ++
  u128 c.blockGasPrice ++ u64 c.gasLimit ++
  u128 c.delayedReceiptsGas ++ u128 c.bufferedReceiptsGas ++ u64 c.receiptBytes ++
  u16 c.allowedShard ++ u64 c.missedChunksCount ++ c.preStateRoot ++
  u32 c.receiptCount ++ c.receiptsCommitment ++ c.postStateRoot ++ c.outcomeRoot ++
  u32 c.refundCount ++ c.refundsCommitment ++ u64 c.gasBurntTotal ++ u128 c.tokensBurntTotal

def Claim.wf (c : Claim) : Bool :=
  c.protocolVersion < 4294967296 && 1 ≤ c.chainId.length && c.chainId.length ≤ 64 &&
  c.chainId.all (fun b => 33 ≤ b.toNat && b.toNat ≤ 126) &&
  c.shardId < Params.two64 && c.blockHeight < Params.two64 &&
  c.blockGasPrice < Params.two128 && c.gasLimit < Params.two64 &&
  c.delayedReceiptsGas < Params.two128 && c.bufferedReceiptsGas < Params.two128 &&
  c.receiptBytes < Params.two64 && c.allowedShard < 65536 && c.missedChunksCount < Params.two64 &&
  c.preStateRoot.length == 32 && c.receiptCount < 4294967296 &&
  c.receiptsCommitment.length == 32 && c.postStateRoot.length == 32 &&
  c.outcomeRoot.length == 32 && c.refundCount < 4294967296 &&
  c.refundsCommitment.length == 32 && c.gasBurntTotal < Params.two64 &&
  c.tokensBurntTotal < Params.two128

/-! ## Witness -/

/-- The receipts (bound by `receiptsCommitment`) and the partial pre-state trie
(bound by `preStateRoot`); the trie must reveal the receivers' Account paths
and the path to `0x0f` (its value if present, or a proof of absence). -/
structure Witness where
  receipts : List Receipt
  trie : PTrie

/-! ## Semantics -/

/-- Block/chunk context the transition depends on. -/
structure Ctx where
  shardId : Nat
  missedChunksCount : Nat
  blockHeight : Nat
  blockGasPrice : Nat
  deriving DecidableEq, Repr

def Claim.ctx (c : Claim) : Ctx := ⟨c.shardId, c.missedChunksCount, c.blockHeight, c.blockGasPrice⟩

/-- `TrieKey::BandwidthSchedulerState` = `[0x0f]` (`trie_key.rs:65,532`), as nibbles. -/
def bwKeyPath : List Nat := nibbles [15]

/-- `run_bandwidth_scheduler` on the partial trie: read the previous state
(absent ⇒ `State.initial`; present ⇒ must decode, else nearcore aborts), write
`Bandwidth.step`. `none` if the witness does not determine the previous value
or the path, or the previous value does not decode. -/
def bandwidthStep (ctx : Ctx) (t : PTrie) : Option PTrie :=
  match t.find bwKeyPath with
  | none => none
  | some prev =>
    let st? : Option Bandwidth.State :=
      match prev with
      | none => some Bandwidth.State.initial
      | some b => Bandwidth.State.decode b
    match st? with
    | none => none
    | some st =>
      t.upsert bwKeyPath (Bandwidth.step ctx.shardId (Bandwidth.linkAllowed ctx.missedChunksCount) st).encode

/-- The whole chunk: scheduler, then the v1 receipt batch (unchanged semantics).
`none` also when a gas refund would need bandwidth the scheduler did not grant
(link (S,S) not allowed ⇒ the refund would be buffered, not forwarded). -/
def runChunk (ctx : Ctx) (w : Witness) : Option TransferV1.Acc :=
  match bandwidthStep ctx w.trie with
  | none => none
  | some t =>
    match TransferV1.runBatch ⟨ctx.blockHeight, ctx.blockGasPrice⟩ t w.receipts with
    | none => none
    | some acc =>
      if !acc.refunds.isEmpty && !Bandwidth.linkAllowed ctx.missedChunksCount then none
      else some acc

structure Outputs where
  postStateRoot : Bytes
  outcomeRoot : Bytes
  refundCount : Nat
  refundsCommitment : Bytes
  gasBurntTotal : Nat
  tokensBurntTotal : Nat
  deriving DecidableEq, Repr

def Outputs.ofAcc (a : TransferV1.Acc) : Outputs :=
  ⟨a.trie.hashOf, NearSpec.outcomeRoot a.outcomes, a.refunds.length,
   NearSpec.refundsCommitment a.refunds, a.gasBurnt, a.tokensBurnt⟩

def Outputs.ofClaim (c : Claim) : Outputs :=
  ⟨c.postStateRoot, c.outcomeRoot, c.refundCount, c.refundsCommitment, c.gasBurntTotal,
   c.tokensBurntTotal⟩

/-! ## Domain and relation -/

/-- `ShardUId` stores the shard id as `u32` (`shard_layout/mod.rs:485-487`). -/
def maxShardIdExcl : Nat := 4294967296

/-- State-independent restrictions (spec doc §3 lists every id). -/
def DomainStatic (c : Claim) (w : Witness) : Prop :=
  c.wf = true ∧
  c.protocolVersion = Params.protocolVersion ∧
  c.chainId = Params.chainId ∧
  w.receipts.length = c.receiptCount ∧
  1 ≤ c.receiptCount ∧ c.receiptCount ≤ Params.maxBatch ∧
  (c.receiptCount - 1) * Params.G < c.gasLimit ∧
  w.receipts.all Receipt.inSlice = true ∧
  (w.receipts.map Receipt.receiptId).Nodup ∧
  w.trie.wf = true ∧
  w.trie.revealedBytes ≤ Params.maxWitnessBytes ∧
  c.shardId < maxShardIdExcl ∧
  c.delayedReceiptsGas = 0 ∧ c.bufferedReceiptsGas = 0 ∧ c.receiptBytes = 0

def Domain (c : Claim) (w : Witness) : Prop :=
  DomainStatic c w ∧ (runChunk c.ctx w).isSome = true

/-- **The relation.** -/
def NearRelation (c : Claim) (w : Witness) : Prop :=
  DomainStatic c w ∧
  receiptsCommitment c.shardId w.receipts = c.receiptsCommitment ∧
  w.trie.hashOf = c.preStateRoot ∧
  (runChunk c.ctx w).map Outputs.ofAcc = some (Outputs.ofClaim c)

def NearRelationBytes (cb : Bytes) (w : Witness) : Prop :=
  ∃ c : Claim, c.encode = cb ∧ NearRelation c w

instance (c : Claim) (w : Witness) : Decidable (DomainStatic c w) := by
  unfold DomainStatic; infer_instance
instance (c : Claim) (w : Witness) : Decidable (Domain c w) := by
  unfold Domain; infer_instance
instance (c : Claim) (w : Witness) : Decidable (NearRelation c w) := by
  unfold NearRelation; infer_instance

theorem NearRelation.domain {c : Claim} {w : Witness} (h : NearRelation c w) : Domain c w := by
  obtain ⟨hs, -, -, hr⟩ := h
  refine ⟨hs, ?_⟩
  cases hrun : runChunk c.ctx w with
  | none => rw [hrun] at hr; simp at hr
  | some _ => rfl

theorem NearRelation.outputs_unique {c₁ c₂ : Claim} {w : Witness}
    (h₁ : NearRelation c₁ w) (h₂ : NearRelation c₂ w) (hctx : c₁.ctx = c₂.ctx) :
    Outputs.ofClaim c₁ = Outputs.ofClaim c₂ := by
  have e1 := h₁.2.2.2
  have e2 := h₂.2.2.2
  rw [hctx] at e1
  rw [e1] at e2
  exact Option.some.inj e2

end NearSpec.TransferV2
