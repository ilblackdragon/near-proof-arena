import NearSpecV3.RuntimeD0
import NearSpecV3.TxD1

/-!
# `Runtime::apply` restricted to domain D1 (new chunk with Transfer transactions)

Extends `RuntimeD0.applyNewChunk` by step 2 of `Runtime::apply` (`runtime/runtime/src/lib.rs:1797`),
`process_transactions` (`lib.rs:1882-2278`), and by the local receipts it creates, processed
first by `process_receipts` (`lib.rs:2658-2721`, `process_local_receipts` 2357-2433).
spec/near-chunk-validation-d1.md §3 is the prose version; every step cites nearcore.

## `process_transactions`, per transaction `t` with validity flag `f` (in chunk order)

1. `UniqueChunkTransactions` (PV 85): a transaction whose hash was already seen in this chunk is
   skipped — no outcome, no reads, nothing (`lib.rs:2004-2012`). The hash is recorded for every
   transaction, expired or not.
2. `f = 0` ⇒ failed outcome (`Expired`, `lib.rs:1904-1907, 2014-2022`).
3. `validate_transaction` fails (signature, size) ⇒ failed outcome.
4. `tx_cost` overflows ⇒ failed outcome (`CostOverflow`, `lib.rs:2030-2047`).
5. The signer's account is looked up (the value prefetched for every non-expired transaction,
   `lib.rs:1925-1985`; a storage error is surfaced only here, `lib.rs:2066`): absent ⇒ failed
   outcome (`InvalidSignerId`); a V2 account is out of D1 (`t.signer_v1`); undecodable ⇒ reject.
6. The access key `(signer, public key)` is looked up likewise: absent ⇒ failed outcome
   (`AccessKeyNotFound`); undecodable ⇒ reject.
7. `verify_and_charge_tx_ephemeral` (`TxD1.verifyAndCharge`): failure ⇒ failed outcome.
8. Success: receipt `Receipt::from_tx` (`receipt.rs:344-365`) with id
   `create_receipt_id_from_transaction(tx_hash, height)` = `sha256(tx_hash ‖ u64 height ‖ u64 0)`
   (`core/primitives/src/utils.rs:270-275`) and gas price `max(gas_price, min_gas_purchase_price)`;
   it is a local receipt iff `receiver = signer` (`lib.rs:2184-2192`), else it goes through
   `ReceiptSink::forward_or_buffer_receipt` (buffering is out of D1, `e.forwarded`). If
   `tx_burnt_amount + burnt` overflows u128 the transaction gets no outcome and no state change
   (the receipt is already emitted; `lib.rs:2224-2244`). Otherwise: outcome
   `SuccessReceiptId(rid)` with `gas_burnt = burnt gas`, `tokens_burnt = burnt amount`; chunk gas
   and compute += burnt gas (u64 overflow panics); account amount and access-key nonce are
   written (`lib.rs:2253-2275`).

A failed outcome is `{id: tx_hash, receipt_ids: [], gas_burnt: 0, tokens_burnt: 0, executor:
signer, status: Failure}` (`transaction.rs:723-744`); `PartialExecutionStatus::Failure` carries
no error (`transaction.rs:597-612`), so every failure reason hashes alike.

Reads: the account / access key of transaction `t` must be determined by the witness exactly
when nearcore uses the prefetched value (steps 5/6 are reached) — a missing value that is only
prefetched (e.g. the signer of a transaction with an invalid signature) is not an error.
-/

namespace NearSpecV3

open NearSpec NearSpec.TransferV1

/-! ## Outcomes with a status -/

inductive OStatus where
  | value                  -- SuccessValue(vec![])
  | receipt (rid : Bytes)  -- SuccessReceiptId
  | failure                -- Failure(_)
  deriving Repr, DecidableEq

structure OutD1 where
  o : Outcome
  status : OStatus
  deriving Repr

def OStatus.encode : OStatus → Bytes
  | .value => [2] ++ u32 0
  | .receipt rid => [3] ++ rid
  | .failure => [1]

def OutD1.partialEncode (x : OutD1) : Bytes :=
  u32 x.o.receiptIds.length ++ concatAll x.o.receiptIds ++ u64 x.o.gasBurnt ++
  u128 x.o.tokensBurnt ++ borshBytes x.o.executorId ++ x.status.encode

def OutD1.leaf (x : OutD1) : Bytes := sha256 (u32 2 ++ x.o.id ++ sha256 x.partialEncode)

def outcomeRootD1 (os : List OutD1) : Bytes := merkleRoot (os.map OutD1.leaf)

def failedOutcome (t : Tx) : OutD1 :=
  ⟨{ id := t.hash, receiptIds := [], gasBurnt := 0, tokensBurnt := 0, executorId := t.signerId },
   .failure⟩

/-! ## Transactions -/

structure TxSt where
  trie : PTrie
  seen : List Bytes
  outs : List OutD1
  locals : List Receipt
  fwd : List Receipt
  ls : List Limit
  gas : Nat
  tokens : Nat

/-- Account deserialization (`Account::deserialize`, `core/primitives-core/src/account.rs:390-447`):
V1 = exactly 72 bytes whose first u128 is not the V2 sentinel `u128::MAX`. -/
def decodeSigner (raw : Bytes) : Except String Account :=
  if leNat (raw.take 16) == Params.u128Max then
    .error "out of domain (t.signer_v1): signer account is not AccountV1"
  else match Account.decode raw with
    | some a => .ok a
    | none => .error "invalid: StorageInconsistentState (signer account)"

def processTx (ctx : ApplyCtx) (st : TxSt) (t : Tx) (flag : Bool) : Except String TxSt := do
  let h := t.hash
  if st.seen.contains h then return st
  let st := { st with seen := h :: st.seen }
  let fail := { st with outs := st.outs ++ [failedOutcome t] }
  if !flag then return fail
  if !t.valid then return fail
  let some c := txCost t ctx.gasPrice | return fail
  let some araw ← readKey st.trie (accountKeyPath t.signerId) "signer account" | return fail
  let a ← decodeSigner araw
  let some kraw ← readKey st.trie (keyAccessKey t.signerId t.pkKey) "access key" | return fail
  let some k := decodeAccessKey kraw | throw "invalid: StorageInconsistentState (access key)"
  let some newAmount := verifyAndCharge a k t c ctx.height | return fail
  let rid := receiptIdFrom h ctx.height 0
  let r : Receipt := { predecessorId := t.signerId, receiverId := t.receiverId, receiptId := rid,
                       signerId := t.signerId, signerPk := t.pkKey, gasPrice := c.receiptGasPrice,
                       deposit := t.deposit }
  let st ← if t.receiverId == t.signerId then pure { st with locals := st.locals ++ [r] }
    else match tryForward ctx st.ls r with
      | some ls' => pure { st with fwd := st.fwd ++ [r], ls := ls' }
      | none => throw "out of domain (e.forwarded): transaction receipt buffered"
  if st.tokens + c.burntAmount ≥ Params.two128 then return st
  let gas := st.gas + c.gasBurnt
  if gas ≥ Params.two64 then throw "invalid: chunk gas overflow (UnexpectedIntegerOverflow panics)"
  let t1 ← match st.trie.set (accountKeyPath t.signerId) (Account.encode { a with amount := newAmount }) with
    | some x => pure x
    | none => throw "invalid: signer account path not revealed"
  let t2 ← match t1.set (keyAccessKey t.signerId t.pkKey) (encodeFullAccessKey t.nonce) with
    | some x => pure x
    | none => throw "invalid: access key path not revealed"
  pure { st with trie := t2, gas, tokens := st.tokens + c.burntAmount,
                 outs := st.outs ++ [⟨{ id := h, receiptIds := [rid], gasBurnt := c.gasBurnt,
                                        tokensBurnt := c.burntAmount, executorId := t.signerId },
                                      .receipt rid⟩] }

def processTxs (ctx : ApplyCtx) : TxSt → List (Tx × Bool) → Except String TxSt
  | st, [] => .ok st
  | st, (t, f) :: rest => do processTxs ctx (← processTx ctx st t f) rest

/-! ## Receipts with a compute accumulator -/

/-- `process_local_receipts` / `process_incoming_receipts` in D1: as `RuntimeD0.applyReceipts`
with the chunk's compute so far (`processing_state.total.compute`, which includes the
transactions) instead of `i·G`. -/
def applyReceiptsC (ctx : ApplyCtx) : Nat → Acc × List Limit → List Receipt →
    Except String (Acc × List Limit × Nat)
  | comp, st, [] => .ok (st.1, st.2, comp)
  | comp, (acc, ls), r :: rs => do
    if comp ≥ ctx.gasLimit then throw "out of domain (e.compute): receipt delayed by the compute limit"
    if r.predecessorId == AccountId.system then
      let acc' ← applySystemReceipt acc r
      applyReceiptsC ctx (comp + Params.G) (acc', ls) rs
    else
      match applyReceipt ⟨ctx.height, ctx.gasPrice⟩ acc r with
      | none =>
        match acc.trie.find (accountKeyPath r.receiverId) with
        | none => throw "invalid: MissingTrieValue (account)"
        | some _ => throw "out of domain (r.success): receipt fails / overflows"
      | some acc' =>
        let newRefunds := acc'.refunds.drop acc.refunds.length
        let ls' ← newRefunds.foldlM (fun ls rf =>
            match tryForward ctx ls rf with
            | some ls' => .ok ls'
            | none => .error "out of domain (e.forwarded): generated receipt buffered") ls
        applyReceiptsC ctx (comp + Params.G) (acc', ls') rs

structure MainOutD1 where
  trie : PTrie
  outcomes : List OutD1
  outgoing : List Receipt
  gasUsed : Nat
  tokensBurnt : Nat
  localIds : List Bytes

/-- New-chunk application in D1. `t` is the partial pre-state trie; `txs` the last new chunk's
transactions with the claim's validity flags. -/
def applyNewChunkD1 (prims : Prims) (ctx : ApplyCtx) (t : PTrie) (receipts : List Receipt)
    (txs : List (Tx × Bool)) : Except String MainOutD1 := do
  queueEmpty (← readKey t keyDelayedIdx "DelayedReceiptIndices") "delayed receipt queue"
  let (t, so) ← schedStep prims ctx t
  let shards ← bufferedShards (← readKey t keyBufferedIdx "BufferedReceiptIndices")
  for s in shards do
    let _ ← readKey t (keyGroupsData s) "BufferedReceiptGroupsQueueData"
  let limits : List Limit := ctx.statuses.map fun (s, ci, missed) =>
    ⟨s, (if s == ctx.own then GASMAX else prims.outGas ci missed ctx.own), so.grant ctx.own s⟩
  -- step 2: transactions
  let st ← processTxs ctx ⟨t, [], [], [], [], limits, 0, 0⟩ txs
  -- local receipts: D0 receipt shape (named receiver) and distinct ids
  if st.locals.any (fun r => !AccountId.isNamed r.receiverId) then
    throw "out of domain (r.shape): local receipt to a non-named account"
  -- step 3: local receipts, then incoming receipts (no delayed receipts in D1)
  let (acc, ls, comp) ← applyReceiptsC ctx st.gas (⟨st.trie, [], [], st.gas, st.tokens⟩, st.ls) st.locals
  let (acc, _, _) ← applyReceiptsC ctx comp (acc, ls) receipts
  queueEmpty (← readKey acc.trie keyYieldIdx "PromiseYieldIndices") "promise yield queue"
  pure ⟨acc.trie, st.outs ++ acc.outcomes.map (fun o => ⟨o, .value⟩), st.fwd ++ acc.refunds,
        acc.gasBurnt, acc.tokensBurnt, st.locals.map Receipt.receiptId⟩

/-- Trie keys the D1 main transition may read. -/
def txKeys (txs : List Tx) : List (List Nat) :=
  txs.flatMap fun t => [accountKeyPath t.signerId, keyAccessKey t.signerId t.pkKey]

end NearSpecV3
