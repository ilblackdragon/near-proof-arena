import NearSpecV3.D2.Actions

/-!
# D2 receipt processing (`runtime/runtime/src/lib.rs:776-1597`)

spec/near-chunk-validation-d2.md §6: `apply_action_receipt` (input data, the action loop with
`ActionReceiptResult::merge`, the storage-stake check, refunds
(`refund_unspent_gas_and_deposits`, `lib.rs:1166-1301`), commit/rollback, burnt amounts,
output data receipts, receipt ids, forwarding, the outcome) and `process_receipt` for every
receipt kind (Data, Action, PromiseYield, PromiseResume). All processors are parameterized by
the `ActionHooks` of `D2/Actions.lean`.
-/

namespace NearSpecV3.D2

open NearSpec NearSpecV3

/-- `ReceivedData { data: Option<Vec<u8>> }` strict decoding. -/
def decodeReceivedData (b : Bytes) : Option (Option Bytes) :=
  match pOption "data" (pBytes "data") b with
  | .ok (x, []) => some x
  | _ => none

/-- Decode a receipt stored in the trie: decoding failures are `StorageInconsistentState`,
out-of-domain shapes stay out of domain. -/
def decodeStoredRcpt (b : Bytes) (what : String) : Except String Rcpt :=
  match decodeRcpt b with
  | .ok r => .ok r
  | .error e => if e.startsWith "out of domain" then .error e else .error (inconsistent what)

/-- `check_storage_stake` (`verifier.rs:48-86`): `some true` ok, `some false` lacking,
`none` = overflow (`StorageInconsistentState`). -/
def storageStakeOk (x : Acct) (amount : Nat) : Option Bool :=
  let req := Params.storageAmountPerByte * x.usage
  if req ≥ two128 then none
  else if amount + x.locked ≥ two128 then none
  else some (amount + x.locked ≥ req || x.usage ≤ Params.zeroBalanceStorageLimit)

/-- The action loop of `apply_action_receipt` (`lib.rs:845-888`) with `merge`
(`lib.rs:439-485`) and `validate_receipt(NewReceipt)` of each new receipt. -/
def actionLoop (hooks : ActionHooks) (env : Env) (r : Rcpt) (a : ActionR) :
    Nat → List Act → ActSt × AR → Except String (ActSt × AR)
  | _, [], acc => .ok acc
  | i, act :: rest, (st, res) => do
    let (st, ar) ← applyAction hooks ⟨env, r, a, i, a.actions.length⟩ st act
    let ar := if ar.ok && ar.newReceipts.any (fun x => !validReceipt true x) then ar.fail else ar
    let gb ← ok? (add64 res.gasBurnt ar.gasBurnt) (panicked "gas_burnt overflow")
    let gu ← ok? (add64 res.gasUsed ar.gasUsed) (panicked "gas_used overflow")
    let cu ← ok? (add64 res.compute ar.compute) (panicked "compute overflow")
    let res := { res with gasBurnt := gb, gasUsed := gu, compute := cu }
    if ar.ok then
      let tb ← ok? (add128 res.tokensBurnt ar.tokensBurnt) (panicked "tokens_burnt overflow")
      actionLoop hooks env r a (i + 1) rest
        (st, { res with newReceipts := res.newReceipts ++ ar.newReceipts,
                        proposals := res.proposals ++ ar.proposals, tokensBurnt := tb })
    else pure (st, res.fail)

/-- Refund receipts (`refund_unspent_gas_and_deposits`, `lib.rs:1166-1301`, NEP-536 at PV 85):
returns (new receipts to append, create-account charge). -/
def refunds (r : Rcpt) (a : ActionR) (res : AR) (purchase burn : Nat) (created : Bool) :
    Except String (List Rcpt × Nat) := do
  let dep ← ok? (totalDeposit a.actions) (panicked "IntegerOverflowError")
  let pg ← ok? (totalPrepaidGas a.actions) (panicked "IntegerOverflowError")
  let ps ← ok? (prepaidSend a.actions) (panicked "IntegerOverflowError")
  let prepaid ← ok? (add64 pg ps.gas) (panicked "IntegerOverflowError")
  let pe ← ok? (prepaidExec r.recv a.actions) (panicked "IntegerOverflowError")
  let pexec ← ok? (add64 pe.gas Fees.nar.exec) (panicked "IntegerOverflowError")
  let tot ← ok? (add64 prepaid pexec) (panicked "IntegerOverflowError")
  let spent := if res.ok then res.gasUsed else res.gasBurnt
  if tot < spent then throw (panicked "gross gas refund underflow")
  let gross := tot - spent
  -- gas_refund_penalty = 0/100, min 0: the penalty is 0
  let unused := purchase * gross
  if unused ≥ two128 then throw (panicked "IntegerOverflowError")
  let surplus := (purchase - burn) * res.gasBurnt
  if surplus ≥ two128 then throw (panicked "IntegerOverflowError")
  let burnedCost := burn * Fees.createAccount.exec
  if burnedCost ≥ two128 then throw (panicked "IntegerOverflowError")
  let charge := if created then min (Lim.accountCreationCharge - burnedCost) surplus else 0
  let gasRefund ← ok? (add128 unused (surplus - charge)) (panicked "IntegerOverflowError")
  let depRefund := if res.ok then 0 else dep
  let rs1 : List Rcpt := if depRefund > 0 then
      [⟨AccountId.system, r.refundReceiver, zero32, .action false ⟨false, AccountId.system, none,
         ⟨0, zeros 32⟩, 0, [], [], [.base ⟨[3] ++ u128 depRefund, .transfer depRefund⟩]⟩⟩]
    else []
  let rs2 : List Rcpt := if gasRefund > 0 then
      [⟨AccountId.system, a.signer, zero32, .action false ⟨false, a.signer, none,
         a.signerPk, 0, [], [], [.base ⟨[3] ++ u128 gasRefund, .transfer gasRefund⟩]⟩⟩]
    else []
  pure (rs1 ++ rs2, charge)

/-- Assign receipt ids, queue instant receipts, forward or buffer the others
(`lib.rs:1075-1120`). Returns the ids of the action receipts. -/
def emitReceipts (env : Env) (parent : Bytes) : RS → Nat → List Rcpt → Except String (RS × List Bytes)
  | rs, _, [] => .ok (rs, [])
  | rs, k, nr :: rest => do
    let rid := receiptIdFrom parent env.ctx.height k
    let nr := { nr with rid := rid }
    let rs ← if nr.isInstant then pure { rs with instant := rs.instant ++ [nr] }
             else forwardOrBuffer env rs nr
    let (rs, ids) ← emitReceipts env parent rs (k + 1) rest
    pure (rs, if nr.isAction then rid :: ids else ids)

/-- `apply_action_receipt` (`lib.rs:776-1164`). Returns the new state, the outcome and its
compute usage. -/
def applyActionReceipt (hooks : ActionHooks) (env : Env) (rs : RS) (r : Rcpt) (a : ActionR) :
    Except String (RS × OutD1 × Nat) := do
  -- 1. input data: read and remove, then commit
  let o ← a.inputs.foldlM (fun (o : Ovl) d => do
      match ← o.get (kReceivedData r.recv d) "received data" with
      | none => throw (inconsistent "received data should be in the state")
      | some b => match decodeReceivedData b with
        | some _ => pure (o.remove (kReceivedData r.recv d))
        | none => throw (inconsistent "received data")) rs.o
  let o := o.commit
  -- 2. receiver account
  let acct ← o.getAcct r.recv
  let res0 : AR := ⟨Fees.nar.exec, Fees.nar.exec, Fees.nar.execCompute, true, [], [], 0⟩
  -- 3. actions
  let (st, res) ← actionLoop hooks env r a 0 a.actions (⟨o, acct, r.pred⟩, res0)
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
      let dep ← ok? (totalDeposit a.actions) (panicked "IntegerOverflowError")
      otherBurnt ← ok? (add128 otherBurnt dep) (panicked "IntegerOverflowError")
  else
    let created := acct.isNone && st.account.isSome && res.ok
    let (rfs, ch) ← refunds r a res purchase burn created
    res := { res with newReceipts := res.newReceipts ++ rfs }
    charge := ch
  -- 7. proposals; commit or rollback
  let o2 := if res.ok then o.commit else o.rollback
  -- 8. burnt amounts (receiver reward is 0: no function-call gas in D2)
  let gasOut := if isSystem then 0 else res.gasBurnt
  let b0 := burn * gasOut
  if b0 ≥ two128 then throw (panicked "IntegerOverflowError")
  let tb ← ok? (add128 b0 charge >>= fun x => add128 x res.tokensBurnt) (panicked "IntegerOverflowError")
  let txBurnt ← ok? (add128 rs.txBurnt tb) (panicked "IntegerOverflowError")
  -- 9. output data receivers (ReturnData::None ⇒ data = Some([]); failure ⇒ None)
  let dataRs : List Rcpt := a.outputs.map fun (d, recv) =>
    ⟨r.recv, recv, zero32, .data false d (if res.ok then some [] else none)⟩
  let rs := { rs with o := o2, otherBurnt := otherBurnt, txBurnt := txBurnt,
                      proposals := rs.proposals ++ res.proposals }
  -- 10. receipt ids, instant / forward
  let (rs, ids) ← emitReceipts env r.rid rs 0 (res.newReceipts ++ dataRs)
  -- 11. outcome
  let out : OutD1 := ⟨{ id := r.rid, receiptIds := ids, gasBurnt := res.gasBurnt, tokensBurnt := tb,
                         executorId := r.recv }, if res.ok then .value else .failure⟩
  pure (rs, out, res.compute)

/-- `process_receipt` (`lib.rs:1303-1527`) and `process_action_receipt` (`lib.rs:1529-1597`). -/
def processReceipt (hooks : ActionHooks) (env : Env) (rs : RS) (r : Rcpt) :
    Except String (RS × Option (OutD1 × Nat)) := do
  let recv := r.recv
  match r.body with
  | .data false d x =>
    let o := rs.o.set (kReceivedData recv d) (encOptBytes x)
    match ← o.get (kPostponedId recv d) "postponed receipt id" with
    | none => pure ({ rs with o := o.commit }, none)
    | some ridb =>
      if ridb.length != 32 then throw (inconsistent "postponed receipt id")
      let o := o.remove (kPostponedId recv d)
      let cnt ← match ← o.get (kPendingCount recv ridb) "pending data count" with
        | none => throw (inconsistent "pending data count should be in the state")
        | some b => ok? (decodeU32 b) (inconsistent "pending data count")
      if cnt == 1 then
        let o := o.remove (kPendingCount recv ridb)
        let pr ← match ← o.get (kPostponed recv ridb) "postponed receipt" with
          | none => throw (inconsistent "pending receipt should be in the state")
          | some b => decodeStoredRcpt b "postponed receipt"
        let o := o.remove (kPostponed recv ridb)
        match pr.body with
        | .action _ a =>
          let (rs, out, cu) ← applyActionReceipt hooks env { rs with o := o } pr a
          pure (rs, some (out, cu))
        | _ => throw (panicked "given receipt should be an action receipt")
      else
        if cnt == 0 then throw (inconsistent "pending data count is 0, but there is a new DataReceipt")
        let o := o.set (kPendingCount recv ridb) (u32 (cnt - 1))
        pure ({ rs with o := o.commit }, none)
  | .action false a =>
    let (o, pending) ← a.inputs.foldlM (fun (o, n) d => do
        if ← o.contains (kReceivedData recv d) "received data" then pure (o, n)
        else pure (o.set (kPostponedId recv d) r.rid, n + 1)) (rs.o, 0)
    if pending == 0 then
      let (rs, out, cu) ← applyActionReceipt hooks env { rs with o := o } r a
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
      match ← rs.o.get (kYieldStatus recv d) "promise yield status" with
      | some [1] => return (rs, none)
      | some [0] | none => pure ()
      | some _ => throw (inconsistent "promise yield status")
    match ← rs.o.get (kYieldReceipt recv d) "promise yield receipt" with
    | none => pure (rs, none)
    | some b =>
      let yr ← decodeStoredRcpt b "promise yield receipt"
      let o := (rs.o.remove (kYieldReceipt recv d)).remove (kYieldStatus recv d)
      let o ← match ← o.get (kDataToYield recv d) "data id to yield id" with
        | none => pure o
        | some y =>
          if y.length != 32 then throw (inconsistent "yield id")
          pure ((o.remove (kYieldToData recv y)).remove (kDataToYield recv d))
      let o := o.set (kReceivedData recv d) (encOptBytes x)
      match yr.body with
      | .action _ a =>
        let (rs, out, cu) ← applyActionReceipt hooks env { rs with o := o } yr a
        pure (rs, some (out, cu))
      | _ => throw (panicked "given receipt should be an action receipt")

/-- `process_receipt_with_metrics`: totals and outcome (`lib.rs:2335-2345`). -/
def processWithTotals (hooks : ActionHooks) (env : Env) (rs : RS) (r : Rcpt) : Except String RS := do
  let (rs, o) ← processReceipt hooks env rs r
  match o with
  | none => pure rs
  | some (out, cu) =>
    let g ← ok? (add64 rs.gas out.o.gasBurnt) (panicked "IntegerOverflowError")
    let c ← ok? (add64 rs.compute cu) (panicked "IntegerOverflowError")
    pure { rs with gas := g, compute := c, outcomes := rs.outcomes ++ [out] }

/-- `process_receipt_and_instant_receipts` (`lib.rs:2619-2656`): instant receipts FIFO. -/
def processWithInstant (hooks : ActionHooks) (env : Env) (rs : RS) (r : Rcpt) : Except String RS := do
  let rs ← processWithTotals hooks env rs r
  let rec drain : Nat → RS → Except String RS
    | 0, _ => .error (panicked "instant receipt fuel")
    | fuel + 1, rs =>
      match rs.instant with
      | [] => .ok rs
      | ir :: more => do
        let rs ← processWithTotals hooks env { rs with instant := more } ir
        drain fuel rs
  drain 100000 rs

end NearSpecV3.D2
