import NearSpec.Trie
import NearSpec.Outcome

/-!
# `near/pv86/receipt-transfer-batch/v0` — semantics, claim, relation

Trusted root of the challenge. Statement: applying the ordered batch of
single-Transfer action receipts (the incoming receipts of a chunk that has no
transactions, no local/delayed/yield receipts and no validator updates) to the
shard state with root `preStateRoot` yields

* `slicePostRoot` — the state root after writing ONLY the slice's `Account`
  values. This is a projection: nearcore's `Runtime::apply` additionally writes
  `TrieKey::BandwidthSchedulerState` on every chunk, so `slicePostRoot` is NOT the
  on-chain `ChunkExtra.state_root` (see spec doc §Projection);
* `outcomeRoot` — exactly nearcore's chunk outcome root for these receipts;
* the generated gas-refund receipts (commitment + count);
* `gasBurntTotal` (= chunk `gas_used`) and `tokensBurntTotal`
  (= `stats.balance.tx_burnt_amount`).

Per-receipt semantics (nearcore 2.13.4, `runtime/runtime/src/lib.rs`):
`apply_action_receipt` (776-1156) → `apply_action` (523-773) →
`action_transfer_or_implicit_account_creation` (2887-2935) →
`action_transfer` (`actions.rs:148-153`); storage check `check_storage_stake`
(`verifier.rs:48-90`); burn price `min(purchase, block)` under
`AccountCostIncrease` (lib.rs:913-922); refunds `refund_unspent_gas_and_deposits`
(lib.rs:1166-1301).
-/

namespace NearSpec.TransferV1

open NearSpec

/-! ## Claim (public statement) -/

/-- The decoded public claim. Encoding: `Claim.encode` (= `spec/claim-v1.md`). -/
structure Claim where
  protocolVersion : Nat
  chainId : Bytes
  shardId : Nat
  blockHeight : Nat
  blockGasPrice : Nat
  gasLimit : Nat
  preStateRoot : Bytes
  receiptCount : Nat
  receiptsCommitment : Bytes
  slicePostRoot : Bytes
  outcomeRoot : Bytes
  refundCount : Nat
  refundsCommitment : Bytes
  gasBurntTotal : Nat
  tokensBurntTotal : Nat
  deriving DecidableEq, Repr

/-- `"near-arena-claim-v1"` -/
def claimFormat : Bytes :=
  [110, 101, 97, 114, 45, 97, 114, 101, 110, 97, 45, 99, 108, 97, 105, 109, 45, 118, 49]
/-- `"near/pv86/receipt-transfer-batch/v0"` -/
def statementId : Bytes :=
  [110, 101, 97, 114, 47, 112, 118, 56, 54, 47, 114, 101, 99, 101, 105, 112, 116, 45, 116,
   114, 97, 110, 115, 102, 101, 114, 45, 98, 97, 116, 99, 104, 47, 118, 48]

def Claim.encode (c : Claim) : Bytes :=
  borshBytes claimFormat ++ borshBytes statementId ++
  u32 c.protocolVersion ++ borshBytes c.chainId ++ u64 c.shardId ++ u64 c.blockHeight ++
  u128 c.blockGasPrice ++ u64 c.gasLimit ++ c.preStateRoot ++
  u32 c.receiptCount ++ c.receiptsCommitment ++ c.slicePostRoot ++ c.outcomeRoot ++
  u32 c.refundCount ++ c.refundsCommitment ++ u64 c.gasBurntTotal ++ u128 c.tokensBurntTotal

/-- Field widths (so that `Claim.encode` is injective). -/
def Claim.wf (c : Claim) : Bool :=
  c.protocolVersion < 4294967296 && 1 ≤ c.chainId.length && c.chainId.length ≤ 64 &&
  c.chainId.all (fun b => 33 ≤ b.toNat && b.toNat ≤ 126) &&
  c.shardId < Params.two64 && c.blockHeight < Params.two64 &&
  c.blockGasPrice < Params.two128 && c.gasLimit < Params.two64 &&
  c.preStateRoot.length == 32 && c.receiptCount < 4294967296 &&
  c.receiptsCommitment.length == 32 && c.slicePostRoot.length == 32 &&
  c.outcomeRoot.length == 32 && c.refundCount < 4294967296 &&
  c.refundsCommitment.length == 32 && c.gasBurntTotal < Params.two64 &&
  c.tokensBurntTotal < Params.two128

/-! ## Witness -/

/-- Prover witness: the receipts (bound by `receiptsCommitment`) and the partial
pre-state trie (bound by `preStateRoot`). -/
structure Witness where
  receipts : List Receipt
  trie : PTrie

/-! ## Semantics -/

structure Ctx where
  blockHeight : Nat
  blockGasPrice : Nat

structure Acc where
  trie : PTrie
  outcomes : List Outcome
  refunds : List Receipt
  gasBurnt : Nat
  tokensBurnt : Nat

/-- Apply one in-slice Transfer receipt. `none` ⇔ the receipt leaves the slice
domain at this point (receiver missing or not revealed, not AccountV1,
balance overflow, V2 sentinel, storage stake not covered, burn/refund overflow).
Each `none` corresponds to a different nearcore behaviour (failure outcome,
rollback, deposit refund, or `apply` abort) that the slice does not model. -/
def applyReceipt (ctx : Ctx) (st : Acc) (r : Receipt) : Option Acc :=
  let key := accountKeyPath r.receiverId
  match st.trie.get key with
  | none => none
  | some raw =>
  match Account.decode raw with
  | none => none
  | some a =>
    let amount' := a.amount + r.deposit
    -- action_transfer: checked_add; result must not be the V2 sentinel
    if amount' ≥ Params.u128Max then none else
    -- check_storage_stake: amount' + locked must not overflow and must cover storage
    if amount' + a.locked ≥ Params.two128 then none else
    if !(amount' + a.locked ≥ Params.storageAmountPerByte * a.storageUsage ||
         a.storageUsage ≤ Params.zeroBalanceStorageLimit) then none else
    let p := min r.gasPrice ctx.blockGasPrice          -- gas_burn_price
    let burnt := Params.G * p                          -- safe_gas_to_balance
    let surplus := Params.G * (r.gasPrice - p)         -- price_surplus = refund
    if burnt ≥ Params.two128 || surplus ≥ Params.two128 then none else
    let tokens' := st.tokensBurnt + burnt              -- stats.balance.tx_burnt_amount
    if tokens' ≥ Params.two128 then none else
    match st.trie.set key (Account.encode { a with amount := amount' }) with
    | none => none
    | some t' =>
      let refund : List Receipt :=
        if surplus = 0 then [] else [gasRefundReceipt r ctx.blockHeight surplus]
      some { trie := t'
             outcomes := st.outcomes ++
               [{ id := r.receiptId, receiptIds := refund.map Receipt.receiptId,
                  gasBurnt := Params.G, tokensBurnt := burnt, executorId := r.receiverId }]
             refunds := st.refunds ++ refund
             gasBurnt := st.gasBurnt + Params.G
             tokensBurnt := tokens' }

def applyAll (ctx : Ctx) : Acc → List Receipt → Option Acc
  | st, [] => some st
  | st, r :: rs =>
    match applyReceipt ctx st r with
    | none => none
    | some st' => applyAll ctx st' rs

def runBatch (ctx : Ctx) (t : PTrie) (rs : List Receipt) : Option Acc :=
  applyAll ctx ⟨t, [], [], 0, 0⟩ rs

/-- The public outputs a run determines. -/
structure Outputs where
  slicePostRoot : Bytes
  outcomeRoot : Bytes
  refundCount : Nat
  refundsCommitment : Bytes
  gasBurntTotal : Nat
  tokensBurntTotal : Nat
  deriving DecidableEq, Repr

def Outputs.ofAcc (a : Acc) : Outputs :=
  ⟨a.trie.hashOf, NearSpec.outcomeRoot a.outcomes, a.refunds.length,
   NearSpec.refundsCommitment a.refunds,
   a.gasBurnt, a.tokensBurnt⟩

def Outputs.ofClaim (c : Claim) : Outputs :=
  ⟨c.slicePostRoot, c.outcomeRoot, c.refundCount, c.refundsCommitment, c.gasBurntTotal,
   c.tokensBurntTotal⟩

def Claim.ctx (c : Claim) : Ctx := ⟨c.blockHeight, c.blockGasPrice⟩

/-! ## Domain and relation -/

/-- State-independent domain restrictions (see spec doc §Domain for each id). -/
def DomainStatic (c : Claim) (w : Witness) : Prop :=
  c.wf = true ∧                                              -- R0 widths
  c.protocolVersion = Params.protocolVersion ∧               -- R1 PV 86
  c.chainId = Params.chainId ∧                               -- R2 mainnet params
  w.receipts.length = c.receiptCount ∧
  1 ≤ c.receiptCount ∧ c.receiptCount ≤ Params.maxBatch ∧    -- R3 batch size
  (c.receiptCount - 1) * Params.G < c.gasLimit ∧             -- R4 compute limit never hit
  w.receipts.all Receipt.inSlice = true ∧                    -- R5..R8 receipt shape
  (w.receipts.map Receipt.receiptId).Nodup ∧                 -- R9 distinct ids
  w.trie.wf = true ∧
  w.trie.revealedBytes ≤ Params.maxWitnessBytes              -- R10 storage-proof limit

/-- Full domain: static restrictions and every receipt stays in the slice when
applied in order (R11..R15: receiver exists as AccountV1, no overflow, storage
stake covered, burn/refund/total fit u128). -/
def Domain (c : Claim) (w : Witness) : Prop :=
  DomainStatic c w ∧ (runBatch c.ctx w.trie w.receipts).isSome = true

/-- **The relation.** `w` witnesses that claim `c` is the result of applying
`w.receipts` (committed in `c`) to the state with root `c.preStateRoot`. -/
def NearRelation (c : Claim) (w : Witness) : Prop :=
  DomainStatic c w ∧
  receiptsCommitment c.shardId w.receipts = c.receiptsCommitment ∧
  w.trie.hashOf = c.preStateRoot ∧
  (runBatch c.ctx w.trie w.receipts).map Outputs.ofAcc = some (Outputs.ofClaim c)

/-- Relation on canonical claim bytes. -/
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
  cases hrun : runBatch c.ctx w.trie w.receipts with
  | none => rw [hrun] at hr; simp at hr
  | some _ => rfl

/-- The relation is a function of the witness: the claim is determined by
`(context fields of c, w)`. -/
theorem NearRelation.outputs_unique {c₁ c₂ : Claim} {w : Witness}
    (h₁ : NearRelation c₁ w) (h₂ : NearRelation c₂ w) (hctx : c₁.ctx = c₂.ctx) :
    Outputs.ofClaim c₁ = Outputs.ofClaim c₂ := by
  have e1 := h₁.2.2.2
  have e2 := h₂.2.2.2
  rw [hctx] at e1
  rw [e1] at e2
  exact Option.some.inj e2

end NearSpec.TransferV1
