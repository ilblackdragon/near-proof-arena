import ReexecV3D3.Logged.Runtime.D2Actions
import NearSpecV3.D2.Receipts

namespace NearSpecV3.D2

open NearSpec NearSpecV3 ReexecV3D3.Logged

/-- The action loop of `apply_action_receipt` (`lib.rs:845-888`) with `merge`
(`lib.rs:439-493`) and `validate_receipt(NewReceipt)` of each new receipt. `inputs` (E3) and
`deployed` (E4) are passed to every action through `ActCtx`. -/
def actionLoopL (hooks : ActionHooksL) (env : Env) (r : Rcpt) (a : ActionR)
    (inputs : List (Option Bytes)) (deployed : List Bytes) (attempted : List Bytes := []) :
    Nat → List Act → ActSt × AR → LM (ActSt × AR)
  | _, [], acc => pure acc
  | i, act :: rest, (st, res) => do
    let c : ActCtx := { env, r, a, idx := i, nActs := a.actions.length, inputs, deployed, attempted }
    let (st, ar) ← applyActionL hooks c st act
    let ar := if ar.ok && ar.newReceipts.any (fun x => !validReceipt true x) then ar.fail else ar
    -- merge (lib.rs:439-493): asserts, then gas / gas_burnt_for_function_call / gas_used / compute
    if ar.gasFC > ar.gasBurnt then throw (panicked "gas_burnt_for_function_call > gas_burnt")
    if ar.gasBurnt > ar.gasUsed then throw (panicked "gas_burnt > gas_used")
    let gb ← LM.okL (add64 res.gasBurnt ar.gasBurnt) (panicked "gas_burnt overflow")
    let gfc ← LM.okL (add64 res.gasFC ar.gasFC) (panicked "gas_burnt_for_function_call overflow")
    let gu ← LM.okL (add64 res.gasUsed ar.gasUsed) (panicked "gas_used overflow")
    let cu ← LM.okL (add64 res.compute ar.compute) (panicked "compute overflow")
    let res := { res with gasBurnt := gb, gasUsed := gu, compute := cu, gasFC := gfc,
                          logs := res.logs ++ ar.logs }
    if ar.ok then
      let tb ← LM.okL (add128 res.tokensBurnt ar.tokensBurnt) (panicked "tokens_burnt overflow")
      let sub ← LM.okL (add128 res.subsidized ar.subsidized) (panicked "subsidized_amount overflow")
      actionLoopL hooks env r a inputs deployed attempted (i + 1) rest
        (st, { res with newReceipts := res.newReceipts ++ ar.newReceipts,
                        proposals := res.proposals ++ ar.proposals, tokensBurnt := tb,
                        subsidized := sub, ret := ar.ret.shift res.newReceipts.length })
    else pure (st, res.fail)

/-- Assign receipt ids, queue instant receipts, forward or buffer the others
(`lib.rs:1075-1120`). Returns the ids of the action receipts. -/
def emitReceiptsL (env : Env) (parent : Bytes) : RS → Nat → List Rcpt → LM (RS × List Bytes)
  | rs, _, [] => pure (rs, [])
  | rs, k, nr :: rest => do
    let rid := receiptIdFrom parent env.ctx.height k
    let nr := { nr with rid := rid }
    let rs ← if nr.isInstant then pure { rs with instant := rs.instant ++ [nr] }
             else forwardOrBufferL env rs nr
    let (rs, ids) ← emitReceiptsL env parent rs (k + 1) rest
    pure (rs, if nr.isAction then rid :: ids else ids)

/-- `apply_action_receipt` (`lib.rs:776-1164`). Returns the new state, the outcome and its
compute usage. -/
def applyActionReceiptL (hooks : ActionHooksL) (env : Env) (rs : RS) (r : Rcpt) (a : ActionR) :
    LM (RS × OutD1 × Nat) := do
  -- 1. input data: read and remove, then commit (E3: the decoded data is kept, in order)
  let (o, inputs) ← a.inputs.foldlM (fun ((o, ins) : Ovl × List (Option Bytes)) d => do
      match ← o.getL (kReceivedData r.recv d) "received data" with
      | none => throw (inconsistent "received data should be in the state")
      | some b => match decodeReceivedData b with
        | some x => pure (o.remove (kReceivedData r.recv d), ins ++ [x])
        | none => throw (inconsistent "received data")) (rs.o, [])
  let o := o.commit
  -- 2. receiver account
  let acct ← o.getAcctL r.recv
  let res0 : AR := { gasBurnt := Fees.nar.exec, gasUsed := Fees.nar.exec,
                     compute := Fees.nar.execCompute, ok := true, newReceipts := [],
                     proposals := [], tokensBurnt := 0 }
  -- 3. actions
  let (st, res) ← actionLoopL hooks env r a inputs rs.deployed rs.attempted 0 a.actions
    ({ o := o, account := acct, actor := r.pred }, res0)
  let mut o := st.o
  let mut res := res
  -- 4. storage stake
  if res.ok then
    match st.account with
    | some x =>
      match storageStakeOk x x.amount with
      | some true => o := o.setAcct r.recv x
      | some false => res := res.fail
      | none => throw (inconsistent "storage staking overflow")
    | none => pure ()
  -- 5. prices (AccountCostIncrease)
  let purchase := a.gasPrice
  let burn := min purchase env.ctx.gasPrice
  -- 6. refunds
  let isSystem := r.pred == AccountId.system
  let mut otherBurnt := rs.otherBurnt
  let mut charge := 0
  if isSystem then
    if !res.ok then
      let dep ← LM.okL (totalDeposit a.actions) (panicked "IntegerOverflowError")
      otherBurnt ← LM.okL (add128 otherBurnt dep) (panicked "IntegerOverflowError")
  else
    let created := acct.isNone && st.account.isSome && res.ok
    let (rfs, ch) ← liftE (refunds r a res purchase burn created)
    res := { res with newReceipts := res.newReceipts ++ rfs }
    charge := ch
  -- 7. proposals; commit or rollback (E4: the receipt's deploys are committed or dropped)
  let o2 := if res.ok then o.commit else o.rollback
  let deployed := if res.ok then rs.deployed ++ st.deploys else rs.deployed
  -- 8. burnt amounts
  let gasOut := if isSystem then 0 else res.gasBurnt
  let b0 := burn * gasOut
  if b0 ≥ two128 then throw (panicked "IntegerOverflowError")
  let tb ← LM.okL (add128 b0 charge >>= fun x => add128 x res.tokensBurnt) (panicked "IntegerOverflowError")
  -- E10: receiver reward (lib.rs:989-1021): burn · ⌊gasFC · 3/10⌋ to the receiver if it still
  -- exists; the outcome's tokens_burnt (`tb`) keeps it, the chunk's tx_burnt does not.
  -- gasFC = 0 in D2 ⇒ rew = 0 ⇒ the D2 path.
  if res.gasFC * 3 ≥ two64 then throw (panicked "receiver_gas_reward overflow")
  let rew := burn * (res.gasFC * 3 / 10)
  if rew ≥ two128 then throw (panicked "IntegerOverflowError")
  let (o2, txb) ← if rew > 0 then do
      match ← o2.getAcctL r.recv with
      | some x =>
        if rew > tb then throw (panicked "tx_burnt_amount - receiver_reward underflow")
        if x.amount + rew ≥ two128 then throw (panicked "IntegerOverflowError")
        pure ((o2.setAcct r.recv { x with amount := x.amount + rew }).commit, tb - rew)
      | none => pure (o2, tb)
    else pure (o2, tb)
  let txBurnt ← LM.okL (add128 rs.txBurnt txb) (panicked "IntegerOverflowError")
  let subsidized ← LM.okL (add128 rs.subsidized res.subsidized) (panicked "IntegerOverflowError")
  -- 9. output data receivers (E11, lib.rs:1034-1073): a returned promise inherits them,
  -- otherwise one Data receipt each (Value(v) ⇒ Some(v); None ⇒ Some([]); failure ⇒ None)
  let (newRs, dataRs) ← if a.outputs.isEmpty then pure (res.newReceipts, [])
    else match res.ok, res.ret with
      | true, .receiptIdx k =>
        match res.newReceipts[k]? with
        | none => throw (panicked "the receipt for the given receipt index should exist")
        | some nr => match nr.body with
          | .action y na =>
            pure (res.newReceipts.set k { nr with body := .action y { na with outputs := na.outputs ++ a.outputs } }, [])
          | _ => throw (panicked "the receipt should be an action receipt")
      | ok, ret =>
        let data : Option Bytes := if ok then (match ret with | .value v => some v | _ => some []) else none
        pure (res.newReceipts, a.outputs.map fun (d, recv) =>
          ({ pred := r.recv, recv := recv, rid := zero32, body := .data false d data } : Rcpt))
  let rs := { rs with o := o2, otherBurnt := otherBurnt, txBurnt := txBurnt,
                      proposals := rs.proposals ++ res.proposals, deployed := deployed,
                      attempted := rs.attempted ++ st.deploys, wasmGas := rs.wasmGas + res.gasFC,
                      subsidized := subsidized }
  -- 10. receipt ids, instant / forward
  let (rs, ids) ← emitReceiptsL env r.rid rs 0 (newRs ++ dataRs)
  -- 11. outcome (E12: status from the return data; E13: logs of all actions)
  let status : OStatus := if res.ok then
      (match res.ret with
       | .none => .value
       | .value v => .valueBytes v
       | .receiptIdx k => .receipt (receiptIdFrom r.rid env.ctx.height k))
    else .failure
  let out : OutD1 := { o := { id := r.rid, receiptIds := ids, gasBurnt := res.gasBurnt, tokensBurnt := tb,
                              executorId := r.recv },
                       status := status, logs := res.logs }
  pure (rs, out, res.compute)

/-- `process_receipt` (`lib.rs:1303-1527`) and `process_action_receipt` (`lib.rs:1529-1597`). -/
def processReceiptL (hooks : ActionHooksL) (env : Env) (rs : RS) (r : Rcpt) :
    LM (RS × Option (OutD1 × Nat)) := do
  let recv := r.recv
  match r.body with
  | .data false d x =>
    let o := rs.o.set (kReceivedData recv d) (encOptBytes x)
    match ← o.getL (kPostponedId recv d) "postponed receipt id" with
    | none => pure ({ rs with o := o.commit }, none)
    | some ridb =>
      if ridb.length != 32 then throw (inconsistent "postponed receipt id")
      let o := o.remove (kPostponedId recv d)
      let cnt ← match ← o.getL (kPendingCount recv ridb) "pending data count" with
        | none => throw (inconsistent "pending data count should be in the state")
        | some b => LM.okL (decodeU32 b) (inconsistent "pending data count")
      if cnt == 1 then
        let o := o.remove (kPendingCount recv ridb)
        let pr ← match ← o.getL (kPostponed recv ridb) "postponed receipt" with
          | none => throw (inconsistent "pending receipt should be in the state")
          | some b => liftE (decodeStoredRcpt b "postponed receipt")
        let o := o.remove (kPostponed recv ridb)
        match pr.body with
        | .action _ a =>
          let (rs, out, cu) ← applyActionReceiptL hooks env { rs with o := o } pr a
          pure (rs, some (out, cu))
        | _ => throw (panicked "given receipt should be an action receipt")
      else
        if cnt == 0 then throw (inconsistent "pending data count is 0, but there is a new DataReceipt")
        let o := o.set (kPendingCount recv ridb) (u32 (cnt - 1))
        pure ({ rs with o := o.commit }, none)
  | .action false a =>
    let (o, pending) ← a.inputs.foldlM (fun (o, n) d => do
        if ← o.containsL (kReceivedData recv d) "received data" then pure (o, n)
        else pure (o.set (kPostponedId recv d) r.rid, n + 1)) (rs.o, 0)
    if pending == 0 then
      let (rs, out, cu) ← applyActionReceiptL hooks env { rs with o := o } r a
      pure (rs, some (out, cu))
    else
      let o := (o.set (kPendingCount recv r.rid) (u32 pending)).set (kPostponed recv r.rid) r.encode
      pure ({ rs with o := o.commit }, none)
  | .action true a =>
    match a.inputs with
    | [d] => pure ({ rs with o := (rs.o.set (kYieldReceipt recv d) r.encode).commit }, none)
    | _ => throw (panicked "PromiseYield receipt must have exactly one input data id")
  | .data true d x =>
    if x.isNone then
      match ← rs.o.getL (kYieldStatus recv d) "promise yield status" with
      | some [1] => return (rs, none)
      | some [0] | none => pure ()
      | some _ => throw (inconsistent "promise yield status")
    match ← rs.o.getL (kYieldReceipt recv d) "promise yield receipt" with
    | none => pure (rs, none)
    | some b =>
      let yr ← liftE (decodeStoredRcpt b "promise yield receipt")
      let o := (rs.o.remove (kYieldReceipt recv d)).remove (kYieldStatus recv d)
      let o ← match ← o.getL (kDataToYield recv d) "data id to yield id" with
        | none => pure o
        | some y =>
          if y.length != 32 then throw (inconsistent "yield id")
          pure ((o.remove (kYieldToData recv y)).remove (kDataToYield recv d))
      let o := o.set (kReceivedData recv d) (encOptBytes x)
      match yr.body with
      | .action _ a =>
        let (rs, out, cu) ← applyActionReceiptL hooks env { rs with o := o } yr a
        pure (rs, some (out, cu))
      | _ => throw (panicked "given receipt should be an action receipt")

/-- `process_receipt_with_metrics`: totals and outcome (`lib.rs:2335-2345`). -/
def processWithTotalsL (hooks : ActionHooksL) (env : Env) (rs : RS) (r : Rcpt) : LM RS := do
  let (rs, o) ← processReceiptL hooks env rs r
  match o with
  | none => pure rs
  | some (out, cu) =>
    let g ← LM.okL (add64 rs.gas out.o.gasBurnt) (panicked "IntegerOverflowError")
    let c ← LM.okL (add64 rs.compute cu) (panicked "IntegerOverflowError")
    pure { rs with gas := g, compute := c, outcomes := rs.outcomes ++ [out] }

/-- `process_receipt_and_instant_receipts` (`lib.rs:2619-2656`): instant receipts FIFO. -/
def processWithInstantL (hooks : ActionHooksL) (env : Env) (rs : RS) (r : Rcpt) : LM RS := do
  let rs ← processWithTotalsL hooks env rs r
  let rec drain : Nat → RS → LM RS
    | 0, _ => throw (panicked "instant receipt fuel")
    | fuel + 1, rs =>
      match rs.instant with
      | [] => pure rs
      | ir :: more => do
        let rs ← processWithTotalsL hooks env { rs with instant := more } ir
        drain fuel rs
  drain 100000 rs

end NearSpecV3.D2

