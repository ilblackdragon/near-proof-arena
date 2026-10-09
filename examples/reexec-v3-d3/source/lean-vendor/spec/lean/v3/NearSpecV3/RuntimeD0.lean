import NearSpecV3.Layout
import NearSpecV3.TrieBuild
import NearSpec.TransferV1

/-!
# `Runtime::apply` restricted to domain D0 (new chunk and missing chunk)

Transcription of nearcore 2.13.4 `Runtime::apply` (`runtime/runtime/src/lib.rs:1717-1819`)
for a chunk application in D0 (spec/near-chunk-validation-v0.md §6): no
transactions, only single-`Transfer` action receipts (incl. `system` refunds),
empty delayed / buffered / yield queues, no validator-account update, nothing
delayed or buffered. Any departure from D0 returns `.error "out of domain …"`.

## Trie reads (exactly nearcore's read set in D0)

A missing node on any of these paths is nearcore's `MissingTrieValue` (reject):
* `DelayedReceiptIndices` = `[7]` — `DelayedReceiptQueue::load` (lib.rs:1759), new and missing chunks;
* `BandwidthSchedulerState` = `[15]` — `run_bandwidth_scheduler` (bandwidth_scheduler/mod.rs:59), new and missing;
* `BufferedReceiptIndices` = `[13]` — `ShardsOutgoingReceiptBuffer::load` (receipts_column_helper.rs:286);
* `BufferedReceiptGroupsQueueData{s}` = `[16] ‖ u64le s` for every shard `s` listed in the
  buffered indices — `OutgoingMetadatas::load` (outgoing_metadata.rs:32-45);
* `PromiseYieldIndices` = `[10]` — `resolve_promise_yield_timeouts` (lib.rs:2986);
* `Account{receiver}` = `[0] ‖ id` per receipt (lib.rs:829);
* `AccessKey{signer, key}` = `[2] ‖ id ‖ [2] ‖ handle(key)` for gas refunds (`signer = receiver`,
  `system` predecessor) — `try_refund_gas_key_balance` / `try_refund_allowance`
  (lib.rs:2899-2919, actions.rs:103-146); handle = `0 ‖ 32 B` (ED25519) / `1 ‖ 64 B` (SECP256K1)
  (`signature.rs:674-692`).
Writes: `[15]` (upsert, `NearSpec.PTrie.upsert`) and the receivers' accounts
(same-length `PTrie.set`, AccountV1 is always 72 bytes).

## Per-receipt semantics

* non-`system` predecessor: v1's `TransferV1.applyReceipt` (receiver credit, storage stake,
  burn at `min(purchase, block)`, gas refund of `G·(purchase − burn)` to the signer);
* `system` predecessor: receiver credit and storage stake as above; **no tokens burnt
  and no refund** (lib.rs:924-932, 966-967), but the outcome still reports
  `gas_burnt = G` (`result.gas_burnt`, lib.rs:1150) and it counts in the chunk's
  `gas_used` (Σ outcome gas_burnt); for a gas refund the access key
  is read and must be absent or `FullAccess` (no gas-key balance or allowance write;
  D0 `r.refunds`).
* compute: every processed receipt uses `G` compute (`new_action_receipt` + `transfer`
  exec, compute = gas at PV 86); receipt `i` is delayed iff `i·G ≥ gas_limit`
  (lib.rs:2563-2585) — out of D0 (`e.compute`).
* generated refunds go through `ReceiptSink::forward_or_buffer_receipt`
  (congestion_control.rs:292-325, 403-463): size = borsh length (capped at
  `max_receipt_size`), congestion gas = transfer exec (+ create-account / add-key exec for
  implicit receivers, `cost.rs:722-748`) + `new_action_receipt` exec
  (congestion_control.rs:716-735); forwarded iff `limit.gas ≥ min(gas, allowed_shard_outgoing_gas)`
  and `limit.size ≥ size`; otherwise buffered — out of D0 (`e.forwarded`).
-/

namespace NearSpecV3

open NearSpec NearSpec.TransferV1

def GASMAX : Nat := 18446744073709551615
def maxReceiptSize : Nat := 4194304
def allowedShardOutgoingGas : Nat := 1000000000000000
def createAccountExec : Nat := 7200000000000
def addFullAccessKeyExec : Nat := 101765125000

def keyDelayedIdx : List Nat := nibbles [7]
def keyBwState : List Nat := nibbles [15]
def keyBufferedIdx : List Nat := nibbles [13]
def keyYieldIdx : List Nat := nibbles [10]
def keyGroupsData (s : Nat) : List Nat := nibbles ([16] ++ u64 s)
def keyAccessKey (acct : Bytes) (pk : PublicKey) : List Nat := nibbles ([2] ++ acct ++ [2] ++ pk.encode)

/-- Scheduler interface (implemented in `BandwidthScheduler.lean`). -/
structure SchedIn where
  shardIds : List Nat                         -- layout index order
  own : Nat
  prev : Option Bytes                         -- 0x0f value, none = absent
  statuses : List (Nat × Congestion × Nat)    -- (shard id, congestion info, missed chunks), all slots
  requests : List (Nat × List BwRequest)      -- (shard id, requests), all slots
  prevBlockHash : Bytes

structure SchedOut where
  state : Bytes
  grant : Nat → Nat → Nat                     -- granted bytes on link (sender id, receiver id)

/-- Primitives supplied by leaf modules. -/
structure Prims where
  sched : SchedIn → Option SchedOut
  /-- `CongestionControl::outgoing_gas_limit(sender)` of a receiving shard. -/
  outGas : Congestion → Nat → Nat → Nat

/-- Block-level apply context derived from a block and its chunk slots (§3.5 of the spec). -/
structure ApplyCtx where
  height : Nat
  prevBlockHash : Bytes
  gasPrice : Nat
  gasLimit : Nat
  layout : Layout
  own : Nat
  statuses : List (Nat × Congestion × Nat)
  requests : List (Nat × List BwRequest)

/-- Read a key that must be determined by the witness. -/
def readKey (t : PTrie) (k : List Nat) (what : String) : Except String (Option Bytes) :=
  match t.find k with
  | some v => .ok v
  | none => .error s!"invalid: MissingTrieValue ({what})"

/-- `TrieQueueIndices { first_index: u64, next_available_index: u64 }` is empty. -/
def queueEmpty (v : Option Bytes) (what : String) : Except String Unit :=
  match v with
  | none => .ok ()
  | some b =>
    if b.length != 16 then .error s!"invalid: StorageInconsistentState ({what})"
    else if leNat (b.take 8) == leNat (b.drop 8) then .ok ()
    else .error s!"out of domain (e.queues_empty): {what} not empty"

/-- `BufferedReceiptIndices { shard_buffers: BTreeMap<ShardId, TrieQueueIndices> }`:
returns the listed shard ids; every queue must be empty (D0). -/
def bufferedShards (v : Option Bytes) : Except String (List Nat) :=
  match v with
  | none => .ok []
  | some b => do
    let (es, rest) ← (pVec "shard_buffers" (fun bs => do
        let (s, bs) ← pU64 "shard" bs
        let (f, bs) ← pU64 "first" bs
        let (n, bs) ← pU64 "next" bs
        pure ((s, f, n), bs))) b
    if !rest.isEmpty then throw "invalid: StorageInconsistentState (BufferedReceiptIndices)"
    if es.any (fun e => e.2.1 != e.2.2) then throw "out of domain (e.queues_empty): outgoing buffer not empty"
    pure (es.map (·.1))

/-- Congestion gas of a refund `Transfer` receipt to `receiver` (no attached gas). -/
def refundCongestionGas (receiver : Bytes) : Nat :=
  let base := Params.newActionReceiptExec + Params.transferExec
  if AccountId.isNearImplicit receiver then base + createAccountExec + addFullAccessKeyExec
  else if AccountId.isEthImplicit receiver || AccountId.isNearDeterministic receiver then
    base + createAccountExec
  else base

structure Limit where
  shard : Nat
  gas : Nat
  size : Nat

def Limit.get (ls : List Limit) (s : Nat) : Limit :=
  (ls.find? (·.shard == s)).getD ⟨s, GASMAX, 0⟩

def Limit.put (ls : List Limit) (l : Limit) : List Limit :=
  if ls.any (·.shard == l.shard) then ls.map (fun x => if x.shard == l.shard then l else x)
  else ls ++ [l]

/-- `try_forward` for one generated receipt; `none` = buffered (out of D0). -/
def tryForward (ctx : ApplyCtx) (ls : List Limit) (r : Receipt) : Option (List Limit) :=
  let s := ctx.layout.shardOf r.receiverId
  let size := min r.encode.length maxReceiptSize
  let gas := refundCongestionGas r.receiverId
  let l := Limit.get ls s
  if l.gas ≥ min gas allowedShardOutgoingGas && l.size ≥ size then
    some (Limit.put ls ⟨s, l.gas - gas, l.size - size⟩)
  else none

structure MainOut where
  trie : PTrie
  outcomes : List Outcome
  outgoing : List Receipt
  gasUsed : Nat
  tokensBurnt : Nat

/-- One `system`-predecessor Transfer receipt. -/
def applySystemReceipt (st : Acc) (r : Receipt) : Except String Acc := do
  let key := accountKeyPath r.receiverId
  let raw ← match st.trie.find key with
    | none => throw "invalid: MissingTrieValue (account)"
    | some none => throw "out of domain (r.success): receiver does not exist"
    | some (some v) => pure v
  let a ← match Account.decode raw with
    | none => throw "out of domain (r.success): receiver is not AccountV1"
    | some a => pure a
  let amount' := a.amount + r.deposit
  if amount' ≥ Params.u128Max then throw "out of domain (r.success): balance overflow"
  if amount' + a.locked ≥ Params.two128 then throw "out of domain (r.success): balance overflow"
  if !(amount' + a.locked ≥ Params.storageAmountPerByte * a.storageUsage ||
       a.storageUsage ≤ Params.zeroBalanceStorageLimit) then
    throw "out of domain (r.success): LackBalanceForState"
  if r.signerId == r.receiverId then
    match st.trie.find (keyAccessKey r.receiverId r.signerPk) with
    | none => throw "invalid: MissingTrieValue (access key)"
    | some none => pure ()
    | some (some ak) =>
      -- AccessKey { nonce: u64, permission }; FullAccess = tag 1, no gas-key info
      if !(ak.length == 9 && ak.getD 8 0 == 1) then
        throw "out of domain (r.refunds): refund to a non-FullAccess / gas key"
  match st.trie.set key (Account.encode { a with amount := amount' }) with
  | none => throw "invalid: account path not revealed"
  | some t' =>
    pure { st with trie := t',
                   outcomes := st.outcomes ++
                     [{ id := r.receiptId, receiptIds := [], gasBurnt := Params.G, tokensBurnt := 0,
                        executorId := r.receiverId }],
                   gasBurnt := st.gasBurnt + Params.G }

/-- Apply the incoming receipts in order (process_incoming_receipts, lib.rs:2541-2610). -/
def applyReceipts (ctx : ApplyCtx) : Nat → Acc × List Limit → List Receipt → Except String (Acc × List Limit)
  | _, st, [] => .ok st
  | i, (acc, ls), r :: rs => do
    if i * Params.G ≥ ctx.gasLimit then throw "out of domain (e.compute): receipt delayed by the compute limit"
    if r.predecessorId == AccountId.system then
      let acc' ← applySystemReceipt acc r
      applyReceipts ctx (i + 1) (acc', ls) rs
    else
      match applyReceipt ⟨ctx.height, ctx.gasPrice⟩ acc r with
      | none =>
        -- distinguish a missing path (nearcore: reject) from a failure (out of domain)
        match acc.trie.find (accountKeyPath r.receiverId) with
        | none => throw "invalid: MissingTrieValue (account)"
        | some _ => throw "out of domain (r.success): receipt fails / overflows"
      | some acc' =>
        let newRefunds := acc'.refunds.drop acc.refunds.length
        let ls' ← newRefunds.foldlM (fun ls rf =>
            match tryForward ctx ls rf with
            | some ls' => .ok ls'
            | none => .error "out of domain (e.forwarded): generated receipt buffered") ls
        applyReceipts ctx (i + 1) (acc', ls') rs

/-- Bandwidth scheduler step on a trie: read `0x0f`, run, upsert. -/
def schedStep (prims : Prims) (ctx : ApplyCtx) (t : PTrie) : Except String (PTrie × SchedOut) := do
  let prev ← readKey t keyBwState "bandwidth scheduler state"
  let out ← match prims.sched ⟨ctx.layout.shardIds, ctx.own, prev, ctx.statuses, ctx.requests,
                               ctx.prevBlockHash⟩ with
    | some o => pure o
    | none => throw "invalid: bandwidth scheduler aborted (StorageInconsistentState)"
  match t.upsert keyBwState out.state with
  | some t' => pure (t', out)
  | none => throw "invalid: MissingTrieValue (bandwidth scheduler state path)"

/-- New-chunk application in D0. `t` is the partial pre-state trie. -/
def applyNewChunk (prims : Prims) (ctx : ApplyCtx) (t : PTrie) (receipts : List Receipt) :
    Except String MainOut := do
  queueEmpty (← readKey t keyDelayedIdx "DelayedReceiptIndices") "delayed receipt queue"
  let (t, so) ← schedStep prims ctx t
  let shards ← bufferedShards (← readKey t keyBufferedIdx "BufferedReceiptIndices")
  for s in shards do
    let _ ← readKey t (keyGroupsData s) "BufferedReceiptGroupsQueueData"
  let limits : List Limit := ctx.statuses.map fun (s, ci, missed) =>
    ⟨s, (if s == ctx.own then GASMAX else prims.outGas ci missed ctx.own), so.grant ctx.own s⟩
  let (acc, _) ← applyReceipts ctx 0 (⟨t, [], [], 0, 0⟩, limits) receipts
  queueEmpty (← readKey acc.trie keyYieldIdx "PromiseYieldIndices") "promise yield queue"
  pure ⟨acc.trie, acc.outcomes, acc.refunds, acc.gasBurnt, acc.tokensBurnt⟩

/-- Missing-chunk application in D0 (`missing_chunk_apply_result`, lib.rs:1773-1779):
delayed-queue load + bandwidth scheduler only. -/
def applyMissingChunk (prims : Prims) (ctx : ApplyCtx) (t : PTrie) : Except String PTrie := do
  let _ ← readKey t keyDelayedIdx "DelayedReceiptIndices"
  let (t, _) ← schedStep prims ctx t
  pure t

/-- Keys the D0 main transition may read (to build the partial trie). -/
def mainKeys (receipts : List Receipt) (bufferedShardIds : List Nat) : List (List Nat) :=
  [keyDelayedIdx, keyBwState, keyBufferedIdx, keyYieldIdx] ++
  bufferedShardIds.map keyGroupsData ++
  receipts.map (fun r => accountKeyPath r.receiverId) ++
  (receipts.filter (fun r => r.predecessorId == AccountId.system && r.signerId == r.receiverId)).map
    (fun r => keyAccessKey r.receiverId r.signerPk)

end NearSpecV3
