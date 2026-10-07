import ReexecV3D3.Logged.Runtime.D2Receipts
import NearSpecV3.D2.RuntimeD2

namespace NearSpecV3.D2

open NearSpec NearSpecV3 ReexecV3D3.Logged

/-- The trie field of the mirrors' overlays (never read). -/
def dummyT : PTrie := .hash []

def validatorUpdateL (l : Layout) (own : Nat) (o : Ovl) (f : ValidatorUpdateFacts)
    (last : List (Bytes × Nat)) : LM Ovl := do
  let onShard := fun (a : Bytes) => l.shardOf a == own
  let stakeInfo := f.stakeInfo.filter (onShard ·.1)
  let rewards := f.validatorRewards.filter (onShard ·.1)
  let lastP := lastProposals l own last
  let o ← stakeInfo.foldlM (fun o (a, maxStake) => do
      match ← o.getAcctL a with
      | some x =>
        let locked := match lookupAmt rewards a with
          | some r => x.locked + r
          | none => x.locked
        if locked ≥ two128 then throw (panicked "update_validator_accounts overflow")
        if locked < maxStake then throw (inconsistent "FATAL: staking invariant does not hold")
        let ret := locked - max maxStake ((lookupAmt lastP a).getD 0)
        if x.amount + ret ≥ two128 then throw (panicked "update_validator_accounts - set_amount")
        pure (o.setAcct a { x with locked := locked - ret, amount := x.amount + ret })
      | none =>
        if maxStake > 0 then throw (inconsistent "account with max of stakes is not found")
        pure o) o
  let o ← match f.treasury with
    | some t =>
      if onShard t && !(stakeInfo.any (·.1 == t)) then do
        let x ← match ← o.getAcctL t with
          | some x => pure x
          | none => throw (inconsistent "Protocol treasury account is not found")
        let r ← LM.okL (lookupAmt rewards t) (inconsistent "Validator reward for the protocol treasury account is not found")
        if x.amount + r ≥ two128 then throw (panicked "update_validator_accounts - treasure_reward")
        pure (o.setAcct t { x with amount := x.amount + r })
      else pure o
    | none => pure o
  pure o.commit


def processTxD2L (env : Env) (rsSeen : RS × List Bytes) (tf : TxD2 × Bool) : LM (RS × List Bytes) := do
  let (rs, seen) := rsSeen
  let (t, flag) := tf
  let h := t.hash
  if seen.contains h then return (rs, seen)
  let seen := h :: seen
  let fail := ({ rs with outcomes := rs.outcomes ++ [failedOutcomeD2 t 0 0] }, seen)
  if !flag then return fail
  if !t.valid then return fail
  let some c := txCostD2 t.signer t.receiver t.actions env.ctx.gasPrice | return fail
  let some a ← rs.o.getAcctL t.signer | return fail
  let some k ← rs.o.getAKL t.signer t.pk | return fail
  let verdict ← match t.nonceIdx with
    | some idx => do
      match ← rs.o.getU64L (kNonce t.signer t.pk idx) "gas key nonce" with
      | none => pure Verdict.failed
      | some row => pure (verifyGasKey a k row idx t c env.ctx.height)
    | none => pure (verifyRegular a k t c env.ctx.height)
  match verdict with
  | .failed => return fail
  | .depositFailed k' (idx, nonce) =>
    let out := failedOutcomeD2 t c.gasBurnt c.burntAmount
    if rs.txBurnt + c.burntAmount ≥ two128 then return (rs, seen)
    let g ← LM.okL (add64 rs.gas c.gasBurnt) (panicked "IntegerOverflowError")
    let cu ← LM.okL (add64 rs.compute c.gasBurnt) (panicked "IntegerOverflowError")
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
             else forwardOrBufferL env rs r
    if rs.txBurnt + c.burntAmount ≥ two128 then return (rs, seen)
    let g ← LM.okL (add64 rs.gas c.gasBurnt) (panicked "IntegerOverflowError")
    let cu ← LM.okL (add64 rs.compute c.computeBurnt) (panicked "IntegerOverflowError")
    let out : OutD1 := { o := { id := h, receiptIds := [rid], gasBurnt := c.gasBurnt,
                                tokensBurnt := c.burntAmount, executorId := t.signer },
                         status := .receipt rid }
    let o := rs.o.setAcct t.signer { a with amount := amount }
    let o := match row with
      | some (idx, nonce) => o.set (kNonce t.signer t.pk idx) (u64 nonce)
      | none => o
    let o := (o.setAK t.signer t.pk k').commit
    pure ({ rs with o := o, gas := g, compute := cu, txBurnt := rs.txBurnt + c.burntAmount,
                    outcomes := rs.outcomes ++ [out] }, seen)

/-! ## Receipts (`process_receipts`, `lib.rs:2357-2721`) -/

def processLocalsL (hooks : ActionHooksL) (env : Env) (rs : RS) (locals : List Rcpt) : LM RS :=
  locals.foldlM (fun rs r =>
    if rs.compute ≥ env.ctx.gasLimit then delayPushL rs r
    else processWithInstantL hooks env rs r) rs

def processDelayedL (hooks : ActionHooksL) (env : Env) : Nat → RS → LM RS
  | 0, rs => pure rs
  | fuel + 1, rs => do
    if rs.compute ≥ env.ctx.gasLimit then return rs
    let (rs, r) ← delayPopL env (rs.dq.next - rs.dq.first + 1) rs
    match r with
    | none => pure rs
    | some r =>
      if !validReceipt false r then throw (inconsistent "Delayed receipt in the state is invalid")
      let rs ← processWithInstantL hooks env rs r
      processDelayedL hooks env fuel rs

def processIncomingL (hooks : ActionHooksL) (env : Env) (rs : RS) (incoming : List Rcpt) : LM RS :=
  incoming.foldlM (fun rs r => do
    if !validReceipt false r then throw (panicked "ReceiptValidationError on an incoming receipt")
    if rs.compute ≥ env.ctx.gasLimit then delayPushL rs r
    else processWithInstantL hooks env rs r) rs

/-- `resolve_promise_yield_timeouts` (`lib.rs:2986-3088`); returns the state and the final
`first_index`. -/
def yieldLoopL (env : Env) (next : Nat) : Nat → RS × Nat × Nat → LM (RS × Nat)
  | 0, (rs, i, _) => pure (rs, i)
  | fuel + 1, (rs, i, k) => do
    if i ≥ next then return (rs, i)
    if rs.compute ≥ env.ctx.gasLimit then return (rs, i)
    let (acct, d, exp) ← match ← rs.o.getL (kYieldTimeout i) "promise yield timeout" with
      | none => throw (inconsistent "PromiseYield timeout queue entry should be in the state")
      | some b => LM.okL (decodeYieldTimeout b) (inconsistent "promise yield timeout")
    if exp > env.ctx.height then return (rs, i)
    let (rs, k) ← if ← rs.o.containsL (kYieldReceipt acct d) "promise yield receipt" then do
        let rid := receiptIdFrom d env.ctx.height k
        let rs ← forwardOrBufferL env rs ⟨acct, acct, rid, .data true d none⟩
        pure (rs, k + 1)
      else pure (rs, k)
    let rs := { rs with o := rs.o.remove (kYieldTimeout i) }
    yieldLoopL env next fuel (rs, i + 1, k)

/-- Bandwidth scheduler through the overlay (`run_bandwidth_scheduler`, D0's `schedStep`). -/
def schedOvlL (prims : Prims) (ctx : ApplyCtx) (o : Ovl) : LM (Ovl × SchedOut) := do
  let prev ← o.getL kBw "bandwidth scheduler state"
  let out ← match prims.sched ⟨ctx.layout.shardIds, ctx.own, prev, ctx.statuses, ctx.requests,
                               ctx.prevBlockHash⟩ with
    | some x => pure x
    | none => throw "invalid: bandwidth scheduler aborted (StorageInconsistentState)"
  pure ((o.set kBw out.state).commit, out)

def applyNewChunkD2L (hooks : ActionHooksL) (prims : Prims) (env : Env)
    (vu : Option ValidatorUpdateFacts) (lastProps : List (Bytes × Nat))
    (incoming : List Rcpt) (txs : List (TxD2 × Bool)) (ownCong : Congestion) :
    LM MainOutD2 := do
  let ctx := env.ctx
  let o := Ovl.ofTrie dummyT
  -- 1. validator accounts update
  let o ← match vu with
    | some f => validatorUpdateL ctx.layout ctx.own o f lastProps
    | none => pure o
  -- 2. delayed queue load
  let (df, dn) ← o.getIndicesL kDelayedIdx "DelayedReceiptIndices"
  -- 3. bandwidth scheduler
  let (o, so) ← schedOvlL prims ctx o
  -- 4. receipt sink (indices and metadata read from the trie)
  let bufIdx ← match ← trieFindL kBufIdx with
    | none => throw (missing "BufferedReceiptIndices")
    | some none => pure []
    | some (some b) => LM.okL (decodeBufIdx b) (inconsistent "BufferedReceiptIndices")
  let metas ← bufIdx.foldlM (fun ms (s, _, _) => do
      match ← trieFindL (kGroupsData s) with
      | none => throw (missing "BufferedReceiptGroupsQueueData")
      | some none => pure ms
      | some (some b) => match decodeMeta b with
        | some m => pure (ms ++ [(s, m)])
        | none => throw (inconsistent "BufferedReceiptGroupsQueueData")) []
  let limits : List Limit := ctx.statuses.map fun (s, ci, missed) =>
    ⟨s, (if s == ctx.own then GASMAX else prims.outGas ci missed ctx.own), so.grant ctx.own s⟩
  let rs : RS := { o, limits, outgoing := [], bufIdx, metas, cong := ownCong, dq := ⟨df, dn, 0, 0, 0, 0⟩,
                   outcomes := [], gas := 0, compute := 0, txBurnt := 0, otherBurnt := 0,
                   proposals := [], instant := [], locals := [] }
  let rs ← forwardFromBufferL env rs
  -- 5. transactions
  let (rs, _) ← txs.foldlM (processTxD2L env) (rs, [])
  -- 6. receipts: local, delayed, incoming
  let locals := rs.locals
  let rs ← processLocalsL hooks env { rs with locals := [] } locals
  let rs ← processDelayedL hooks env (rs.dq.next - rs.dq.first + 1) rs
  let rs ← processIncomingL hooks env rs incoming
  -- yield timeouts
  let (yf, yn) ← rs.o.getIndicesL kYieldIdx "PromiseYieldIndices"
  let (rs, yf') ← yieldLoopL env yn (yn - yf + 1) (rs, yf, 0)
  -- 7. validate_apply_state_update
  let rs := if yf' != yf then { rs with o := rs.o.set kYieldIdx (encIndices yf' yn) } else rs
  let cong ← liftE (applyDelayedCongestion rs.dq rs.cong)
  let allowed := ctx.layout.shardIds.getD ((ctx.height + (ctx.layout.index ctx.own).getD 0) % ctx.layout.numShards) ctx.own
  let cong := { cong with allowedShard := allowed }
  let bw ← bandwidthRequestsL env rs
  let o := rs.o.commit
  let root ← o.finalizeL
  let gasUsed ← LM.okL (sumNat64 (rs.outcomes.map (·.o.gasBurnt))) (panicked "total gas burnt overflow")
  let burnt ← LM.okL (add128 rs.txBurnt rs.otherBurnt) (panicked "burnt balance overflow")
  -- E9: balance_burnt = tx + other (+ slashed = 0) − subsidized (rt/mod.rs:386-403); negative ⇒ Error
  if rs.subsidized > burnt then throw "invalid: balance_burnt underflow (subsidized exceeds burnt)"
  let burnt := burnt - rs.subsidized
  pure { root, outcomes := rs.outcomes, outgoing := rs.outgoing, gasUsed, balanceBurnt := burnt,
         congestion := cong, bwRequests := bw, proposals := dedupProposals rs.proposals,
         cdRemovals := o.cdRemovals, wasmGas := rs.wasmGas }

def applyMissingChunkD2L (prims : Prims) (env : Env) (vu : Option ValidatorUpdateFacts)
    (lastProps : List (Bytes × Nat)) : LM Bytes := do
  let ctx := env.ctx
  let o := Ovl.ofTrie dummyT
  let o ← match vu with
    | some f => validatorUpdateL ctx.layout ctx.own o f lastProps
    | none => pure o
  let _ ← o.getIndicesL kDelayedIdx "DelayedReceiptIndices"
  let (o, _) ← schedOvlL prims ctx o
  o.finalizeL


end NearSpecV3.D2

