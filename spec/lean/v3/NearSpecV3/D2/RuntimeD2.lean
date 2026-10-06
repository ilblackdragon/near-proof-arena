import NearSpecV3.D2.Validators

/-!
# `Runtime::apply` in domain D2 (spec/near-chunk-validation-d2.md §1, §5, §6.1, §9.4, §10)

`applyNewChunkD2` (`runtime/runtime/src/lib.rs:1718-1819`): validator accounts update, delayed
queue load, bandwidth scheduler, receipt sink with forwarding from the outgoing buffers,
`process_transactions`, local / delayed / incoming receipts (compute limit, delayed pushes,
instant receipts), yield timeouts, then `validate_apply_state_update` (yield indices, own
congestion info, bandwidth requests, `finalize`, proposals). `applyMissingChunkD2`
(`lib.rs:2937-2984`): validator update, delayed queue load, scheduler, `finalize`.
-/

namespace NearSpecV3.D2

open NearSpec NearSpecV3

/-! ## Transactions (`process_transactions`, `lib.rs:1882-2279`) -/

def failedOutcomeD2 (t : TxD2) (gas tokens : Nat) : OutD1 :=
  ⟨{ id := t.hash, receiptIds := [], gasBurnt := gas, tokensBurnt := tokens, executorId := t.signer },
   .failure⟩

def processTxD2 (env : Env) (rsSeen : RS × List Bytes) (tf : TxD2 × Bool) : Except String (RS × List Bytes) := do
  let (rs, seen) := rsSeen
  let (t, flag) := tf
  let h := t.hash
  if seen.contains h then return (rs, seen)
  let seen := h :: seen
  let fail := ({ rs with outcomes := rs.outcomes ++ [failedOutcomeD2 t 0 0] }, seen)
  if !flag then return fail
  if !t.valid then return fail
  let some c := txCostD2 t.signer t.receiver t.actions env.ctx.gasPrice | return fail
  let some a ← rs.o.getAcct t.signer | return fail
  let some k ← rs.o.getAK t.signer t.pk | return fail
  let verdict ← match t.nonceIdx with
    | some idx => do
      match ← rs.o.getU64 (kNonce t.signer t.pk idx) "gas key nonce" with
      | none => pure Verdict.failed
      | some row => pure (verifyGasKey a k row idx t c env.ctx.height)
    | none => pure (verifyRegular a k t c env.ctx.height)
  match verdict with
  | .failed => return fail
  | .depositFailed k' (idx, nonce) =>
    let out := failedOutcomeD2 t c.gasBurnt c.burntAmount
    if rs.txBurnt + c.burntAmount ≥ two128 then return (rs, seen)
    let g ← ok? (add64 rs.gas c.gasBurnt) (panicked "IntegerOverflowError")
    let cu ← ok? (add64 rs.compute c.gasBurnt) (panicked "IntegerOverflowError")
    let o := rs.o.setAcct t.signer a
    let o := o.set (kNonce t.signer t.pk idx) (u64 nonce)
    let o := (o.setAK t.signer t.pk k').commit
    pure ({ rs with o := o, gas := g, compute := cu, txBurnt := rs.txBurnt + c.burntAmount,
                    outcomes := rs.outcomes ++ [out] }, seen)
  | .success amount k' row =>
    let rid := receiptIdFrom h env.ctx.height 0
    let r : Rcpt := ⟨t.signer, t.receiver, rid,
      .action false ⟨false, t.signer, none, t.pk, c.receiptGasPrice, [], [], t.actions⟩⟩
    let rs ← if t.receiver == t.signer then pure { rs with locals := rs.locals ++ [r] }
             else forwardOrBuffer env rs r
    if rs.txBurnt + c.burntAmount ≥ two128 then return (rs, seen)
    let g ← ok? (add64 rs.gas c.gasBurnt) (panicked "IntegerOverflowError")
    let cu ← ok? (add64 rs.compute c.computeBurnt) (panicked "IntegerOverflowError")
    let out : OutD1 := ⟨{ id := h, receiptIds := [rid], gasBurnt := c.gasBurnt,
                          tokensBurnt := c.burntAmount, executorId := t.signer }, .receipt rid⟩
    let o := rs.o.setAcct t.signer { a with amount := amount }
    let o := match row with
      | some (idx, nonce) => o.set (kNonce t.signer t.pk idx) (u64 nonce)
      | none => o
    let o := (o.setAK t.signer t.pk k').commit
    pure ({ rs with o := o, gas := g, compute := cu, txBurnt := rs.txBurnt + c.burntAmount,
                    outcomes := rs.outcomes ++ [out] }, seen)

/-! ## Receipts (`process_receipts`, `lib.rs:2357-2721`) -/

def processLocals (hooks : ActionHooks) (env : Env) (rs : RS) (locals : List Rcpt) : Except String RS :=
  locals.foldlM (fun rs r =>
    if rs.compute ≥ env.ctx.gasLimit then delayPush rs r
    else processWithInstant hooks env rs r) rs

def processDelayed (hooks : ActionHooks) (env : Env) : Nat → RS → Except String RS
  | 0, rs => .ok rs
  | fuel + 1, rs => do
    if rs.compute ≥ env.ctx.gasLimit then return rs
    let (rs, r) ← delayPop env (rs.dq.next - rs.dq.first + 1) rs
    match r with
    | none => pure rs
    | some r =>
      if !validReceipt false r then throw (inconsistent "Delayed receipt in the state is invalid")
      let rs ← processWithInstant hooks env rs r
      processDelayed hooks env fuel rs

def processIncoming (hooks : ActionHooks) (env : Env) (rs : RS) (incoming : List Rcpt) : Except String RS :=
  incoming.foldlM (fun rs r => do
    if !validReceipt false r then throw (panicked "ReceiptValidationError on an incoming receipt")
    if rs.compute ≥ env.ctx.gasLimit then delayPush rs r
    else processWithInstant hooks env rs r) rs

/-- `PromiseYieldTimeout { account_id, data_id, expires_at }` strict decoding. -/
def decodeYieldTimeout (b : Bytes) : Option (Bytes × Bytes × Nat) :=
  match (do
      let (a, bs) ← pAccountId "account_id" b
      let (d, bs) ← pHash "data_id" bs
      let (e, bs) ← pU64 "expires_at" bs
      pure ((a, d, e), bs) : Except String ((Bytes × Bytes × Nat) × Bytes)) with
  | .ok (x, []) => some x
  | _ => none

/-- `resolve_promise_yield_timeouts` (`lib.rs:2986-3088`); returns the state and the final
`first_index`. -/
def yieldLoop (env : Env) (next : Nat) : Nat → RS × Nat × Nat → Except String (RS × Nat)
  | 0, (rs, i, _) => .ok (rs, i)
  | fuel + 1, (rs, i, k) => do
    if i ≥ next then return (rs, i)
    if rs.compute ≥ env.ctx.gasLimit then return (rs, i)
    let (acct, d, exp) ← match ← rs.o.get (kYieldTimeout i) "promise yield timeout" with
      | none => throw (inconsistent "PromiseYield timeout queue entry should be in the state")
      | some b => ok? (decodeYieldTimeout b) (inconsistent "promise yield timeout")
    if exp > env.ctx.height then return (rs, i)
    let (rs, k) ← if ← rs.o.contains (kYieldReceipt acct d) "promise yield receipt" then do
        let rid := receiptIdFrom d env.ctx.height k
        let rs ← forwardOrBuffer env rs ⟨acct, acct, rid, .data true d none⟩
        pure (rs, k + 1)
      else pure (rs, k)
    let rs := { rs with o := rs.o.remove (kYieldTimeout i) }
    yieldLoop env next fuel (rs, i + 1, k)

/-! ## Apply -/

structure MainOutD2 where
  root : Bytes
  outcomes : List OutD1
  outgoing : List Rcpt
  gasUsed : Nat
  balanceBurnt : Nat
  congestion : Congestion
  bwRequests : List BwRequest
  proposals : List Proposal
  cdRemovals : Nat

def decodeBufIdx (b : Bytes) : Option (List (Nat × Nat × Nat)) :=
  match pVec "shard_buffers" (fun bs => do
      let (s, bs) ← pU64 "shard" bs
      let (f, bs) ← pU64 "first" bs
      let (n, bs) ← pU64 "next" bs
      pure ((s, f, n), bs)) b with
  | .ok (es, []) => some es
  | _ => none

/-- Bandwidth scheduler through the overlay (`run_bandwidth_scheduler`, D0's `schedStep`). -/
def schedOvl (prims : Prims) (ctx : ApplyCtx) (o : Ovl) : Except String (Ovl × SchedOut) := do
  let prev ← o.get kBw "bandwidth scheduler state"
  let out ← match prims.sched ⟨ctx.layout.shardIds, ctx.own, prev, ctx.statuses, ctx.requests,
                               ctx.prevBlockHash⟩ with
    | some x => pure x
    | none => throw "invalid: bandwidth scheduler aborted (StorageInconsistentState)"
  pure ((o.set kBw out.state).commit, out)

/-- Proposals dedup (`lib.rs:2814-2823`): reverse order, keep the first (= last proposed)
of each account. -/
def dedupProposals (ps : List Proposal) : List Proposal :=
  (ps.reverse.foldl (fun (acc : List Proposal × List Bytes) p =>
    if acc.2.contains p.acct then acc else (acc.1 ++ [p], p.acct :: acc.2)) ([], [])).1

def applyNewChunkD2 (hooks : ActionHooks) (prims : Prims) (env : Env) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (lastProps : List (Bytes × Nat))
    (incoming : List Rcpt) (txs : List (TxD2 × Bool)) (ownCong : Congestion) :
    Except String MainOutD2 := do
  let ctx := env.ctx
  let o := Ovl.ofTrie t
  -- 1. validator accounts update
  let o ← match vu with
    | some f => validatorUpdate ctx.layout ctx.own o f lastProps
    | none => pure o
  -- 2. delayed queue load
  let (df, dn) ← o.getIndices kDelayedIdx "DelayedReceiptIndices"
  -- 3. bandwidth scheduler
  let (o, so) ← schedOvl prims ctx o
  -- 4. receipt sink (indices and metadata read from the trie)
  let bufIdx ← match o.trie.find (nibbles kBufIdx) with
    | none => throw (missing "BufferedReceiptIndices")
    | some none => pure []
    | some (some b) => ok? (decodeBufIdx b) (inconsistent "BufferedReceiptIndices")
  let metas ← bufIdx.foldlM (fun ms (s, _, _) => do
      match o.trie.find (nibbles (kGroupsData s)) with
      | none => throw (missing "BufferedReceiptGroupsQueueData")
      | some none => pure ms
      | some (some b) => match decodeMeta b with
        | some m => pure (ms ++ [(s, m)])
        | none => throw (inconsistent "BufferedReceiptGroupsQueueData")) []
  let limits : List Limit := ctx.statuses.map fun (s, ci, missed) =>
    ⟨s, (if s == ctx.own then GASMAX else prims.outGas ci missed ctx.own), so.grant ctx.own s⟩
  let rs : RS := ⟨o, limits, [], bufIdx, metas, ownCong, ⟨df, dn, 0, 0, 0, 0⟩, [], 0, 0, 0, 0, [], [], []⟩
  let rs ← forwardFromBuffer env rs
  -- 5. transactions
  let (rs, _) ← txs.foldlM (processTxD2 env) (rs, [])
  -- 6. receipts: local, delayed, incoming
  let locals := rs.locals
  let rs ← processLocals hooks env { rs with locals := [] } locals
  let rs ← processDelayed hooks env (rs.dq.next - rs.dq.first + 1) rs
  let rs ← processIncoming hooks env rs incoming
  -- yield timeouts
  let (yf, yn) ← rs.o.getIndices kYieldIdx "PromiseYieldIndices"
  let (rs, yf') ← yieldLoop env yn (yn - yf + 1) (rs, yf, 0)
  -- 7. validate_apply_state_update
  let rs := if yf' != yf then { rs with o := rs.o.set kYieldIdx (encIndices yf' yn) } else rs
  let cong ← applyDelayedCongestion rs.dq rs.cong
  let allowed := ctx.layout.shardIds.getD ((ctx.height + (ctx.layout.index ctx.own).getD 0) % ctx.layout.numShards) ctx.own
  let cong := { cong with allowedShard := allowed }
  let bw ← bandwidthRequests env rs
  let o := rs.o.commit
  let root ← o.finalize
  let gasUsed ← ok? (sumNat64 (rs.outcomes.map (·.o.gasBurnt))) (panicked "total gas burnt overflow")
  let burnt ← ok? (add128 rs.txBurnt rs.otherBurnt) (panicked "burnt balance overflow")
  pure ⟨root, rs.outcomes, rs.outgoing, gasUsed, burnt, cong, bw, dedupProposals rs.proposals, o.cdRemovals⟩

def applyMissingChunkD2 (prims : Prims) (env : Env) (t : PTrie) (vu : Option ValidatorUpdateFacts)
    (lastProps : List (Bytes × Nat)) : Except String Bytes := do
  let ctx := env.ctx
  let o := Ovl.ofTrie t
  let o ← match vu with
    | some f => validatorUpdate ctx.layout ctx.own o f lastProps
    | none => pure o
  let _ ← o.getIndices kDelayedIdx "DelayedReceiptIndices"
  let (o, _) ← schedOvl prims ctx o
  o.finalize

end NearSpecV3.D2
