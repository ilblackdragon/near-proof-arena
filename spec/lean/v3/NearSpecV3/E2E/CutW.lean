import NearSpecV3.E2E.Statement
import NearSpecV3.E2E.CallMachine

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# E2E-M11b, part 1: the receipt step with its VM calls as a parameter

The engine's receipt step reaches the Wasm interpreter only through `vmCall` inside
`functionCallRecordedF`. Here the chain from `processWithInstant` down to that call
(`processWithInstant`, `processWithTotals`, `processReceipt`, `applyActionReceipt`, `actionLoop`,
`applyAction`, `functionCallRecordedF`) is copied **verbatim**, each copy taking its direct callee
as a parameter (the bottom one takes the VM call). Instantiated with the original callees the copies
are the originals: `fcW_std`, `applyActionW_std`, `applyActionReceiptW_std`, `processReceiptW_std`,
`processWithTotalsW_std` are `rfl`; `actionLoopW_std` and `drainW_std` are inductions over the
recursion. No checker definition is changed.

Every layer is **monotone** in its parameter (`MLe`: every successful result of the left computation
is a successful result of the right one, from every state). The walk `mono_walk` proves it on the
copied bodies. Composed: a receipt step run with a partial VM oracle that succeeds is the real
receipt step (`estepO_sound`, in `CallCut.lean`).
-/

namespace NearSpecV3.Successor.StorageExecution.CutW
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged
open NearSpecV3.Wasm
open NearSpecV3.D3

/-- The VM call: `vmCall fuelOf` with the budget fixed. -/
abbrev VmFn := NearCfg → ByteArray → String → CallCtx → TTN.RealStore → Except String Run
abbrev FcFn := Flags → NearCfg → ActCtx → ActSt → AR → Base → M (ActSt × AR)
abbrev AaFn := Flags → NearCfg → ActCtx → ActSt → Act → M (ActSt × AR)
abbrev AlFn := Flags → NearCfg → Env → Rcpt → ActionR → List (Option Bytes) → List Bytes →
  List Bytes → Nat → List Act → ActSt × AR → M (ActSt × AR)
abbrev AarFn := Flags → NearCfg → Env → RS → Rcpt → ActionR → M (RS × OutD1 × Nat)
abbrev PrFn := Flags → NearCfg → Env → RS → Rcpt → M (RS × Option (OutD1 × Nat))
abbrev PwFn := Flags → NearCfg → Env → RS → Rcpt → M RS

/-! ## The verbatim copies -/

def fcW (vm : VmFn) (fl : Flags) (cfg : NearCfg) (c : ActCtx) (st : ActSt)
    (ar : AR) (b : Base) : M (ActSt × AR) := do
  let .fcall method args gas deposit := b | throw "unmodeled: functionCall hook on a non-FunctionCall"
  let some acct := st.account | throw "invalid: EXPECT_ACCOUNT_EXISTS"
  let env := c.env
  let h := env.ctx.height
  if acct.amount + deposit ≥ 2 ^ 128 then
    throw "invalid: StorageInconsistentState (account balance overflow on deposit)"
  -- code (§2)
  let (codeHash, codeKey) ← resolveCode c st acct
  match codeHash with
  | none =>
    -- CodeDoesNotExist: 0 VM gas, action failure
    setVmErr "CompilationError(CodeDoesNotExist)"
    pure (st, ar.fail)
  | some hh =>
  -- Code (§2.2). A blob in the merged witness store always serves. Otherwise an in-chunk deploy
  -- of the same code serves it through the deploy tracker or, even rolled back, the compiled
  -- cache, unless the call's preparation was pipelined before that deploy ran (`Pipeline`).
  -- The pre-state probe has NO_SIDE_EFFECTS in nearcore and never records proof bytes; only the
  -- complete-code policy consults it.
  let recording ← get
  let pre := prestateCode st.o.trie codeKey
  let sources : CodeSources := {
    witness := env.codeOf, current := st.deploys,
    committed := c.deployed ++ recording.materialized, attempted := c.attempted }
  -- A call only an in-chunk deploy serves may race its pipelined preparation: run the served
  -- branch and remember the race (`Pipeline.Pipe.noteRace`); `run` turns an accept into the race
  -- exclusion, a reject is a reject on every schedule.
  modifyPipe (Pipeline.Pipe.noteRace c.r.rid c.idx hh (sources.deployServed hh))
  let code ← liftE (resolveCodeBytes fl.codePolicy sources pre hh)
  let codeB := toBA code
  if let some why := contractOOD cfg codeB then throw (oodE why)
  -- VMContext (§3)
  let ah := actionHash c.r.rid h c.idx
  let a := c.a
  let isLast := c.idx + 1 == c.nActs
  let ctx : CallCtx := {
    currentAccount := strOf c.r.recv, signer := strOf a.signer, signerPk := toBA a.signerPk.encode,
    predecessor := strOf c.r.pred, refundTo := strOf (a.refundTo.getD c.r.pred), input := toBA args,
    actionHash := some (toBA ah),
    promiseResults := (c.inputs.map fun x => match x with
      | some v => PRes.ok (toBA v) | none => PRes.failed).toArray,
    blockHeight := h, blockTimestamp := env.blockTimestamp, epochHeight := env.epochHeight,
    accountBalance := acct.amount, accountLocked := acct.locked, storageUsage := acct.usage,
    attachedDeposit := deposit, prepaidGas := gas,
    randomSeed := toBA (sha256 (ah ++ env.randomValue)),
    receivers := if isLast then (a.outputs.map fun (_, r) => strOf r).toArray else #[],
    chainId := strOf env.chainId,
    validators := (env.validators.map fun (v, s) => (strOf v, s)).toArray,
    accountContract := (ctxContract acct.contract).1,
    accountContractTag := (ctxContract acct.contract).2 }
  -- trie-backed External over the merged witness values (§4.2, d3-trie-accounting.md)
  let pfx := TTN.contractDataPrefix ctx.currentAccount
  let ovl : TTN.BMap (Option ByteArray) :=
    (st.o.committed ++ st.o.prosp).foldl (fun m (k, v) =>
      m.insert (toBA k) (v.map toBA)) {}
  let recording ← get
  let real : TTN.RealStore := { store := fun hb => (env.codeOf (ofBA hb)).map toBA,
                                root := toBA env.preRoot, overlay := ovl, pfx,
                                recd := recording.recorder, acct := recording.cache,
                                recBefore := recording.receiptStart }
  -- W02: the legacy `(gas / regular + 2) · 64 + 10⁶` budget is exhausted by valid zero-fee
  -- control-flow loops (`Wasm/Fuel.lean`); `wasmFuel` changes only fuel-exhausted results
  -- (`Wasm.successorFuel_moves_only_exhausted`).
  -- `vmCall` passes `fuelOf cfg ctx.prepaidGas`, and `ctx.prepaidGas = gas` (above): the checker's
  -- budget is `wasmFuel cfg gas` (`functionCallRecorded_fuel`).
  let vmr ← liftE (vm cfg codeB (strOf method) ctx real)
  match vmr with
  | .line l =>
    let (burnt, used) ← liftE (lineOutcome l)
    let gb := ar.gasBurnt + burnt
    setVmErr (lineErr l)
    pure (st, { ar.fail with gasBurnt := gb, gasFC := ar.gasFC + burnt, gasUsed := ar.gasUsed + used })
  | .done s err =>
    if let some r := s.real then
      modify fun state => { state with recorder := r.recd, cache := r.acct }
    -- storage writes (also of a failed call: rolled back with the receipt, removals counted)
    let o := match s.real with
      | some r => r.writes.foldl (fun (o : Ovl) (k, v) => match v with
          | some v => o.set (ofBA k) (ofBA v)
          | none => o.remove (ofBA k)) st.o
      | none => st.o
    let st := { st with o }
    let burnt := s.gas.burnt
    let logs := s.logs.toList.map ofBA
    -- receipts + gas distribution (only for VM-produced outcomes, §5.5)
    let (rs, idx, resumes) ← liftE ((if fl.globalActions then managerGlobal else manager) s.actions ah h)
    let (rs, extra) ← liftE (distribute rs gas s.gas.used)
    let used := s.gas.used + extra
    let ar1 := { ar with gasBurnt := ar.gasBurnt + burnt, gasFC := ar.gasFC + burnt,
                         gasUsed := ar.gasUsed + used, compute := ar.compute + s.gas.computeUsage,
                         logs := ar.logs ++ logs }
    match err with
    | some e =>
      if e.startsWith "unmodeled" then throw (oodE e)
      if e.startsWith "invalid" || e.startsWith "StorageInconsistentState" then throw s!"invalid: {e}"
      setVmErr e
      pure (st, ar1.fail)
    | none =>
      -- `PromiseYieldIndices` is read on every successful call; each yield receipt enqueues a
      -- timeout `{account, data_id, expires_at = h + 200}` (§4.2.1–4, `fc.rs:154-222`)
      let (yf, yn) ← logged (st.o.getIndicesL kYieldIdx "PromiseYieldIndices")
      let mut o := st.o
      let mut next := yn
      for m in rs do
        if m.yield then
          let some did := m.inputs.head? | throw "unmodeled: yield receipt without data id"
          if next ≥ 2 ^ 64 - 1 then throw "invalid: panicked (promise yield indices overflow)"
          o := o.set (kYieldTimeout next) (borshBytes c.r.recv ++ did ++ u64 (h + 200))
          next := next + 1
      if next != yn then o := o.set kYieldIdx (encIndices yf next)
      let st := { st with o }
      let rcpts ← rs.toList.mapM fun m => do
        let acts ← liftE ((if fl.globalActions then finishActsGlobal else finishActs) m)
        pure (⟨c.r.recv, m.recv, zero32, .action m.yield ⟨true, a.signer, m.refundTo, a.signerPk,
          a.gasPrice, m.outputs, m.inputs, acts⟩⟩ : Rcpt)
      let rcpts := rcpts ++ resumes.map fun (d, p) =>
        (⟨c.r.recv, c.r.recv, zero32, .data true d (some p)⟩ : Rcpt)
      let ret : Ret ← match s.ret with
        | none => pure .none
        | some (.inl v) => pure (.value (ofBA v))
        | some (.inr r) => match idx.find? (·.1 == r) with
          | some (_, m) => pure (.receiptIdx m)
          | none => throw (oodE "promise_return of a non-receipt log index")
      let acct' := { acct with amount := s.balance, usage := s.storageUsage }
      pure ({ st with account := some acct' },
            { ar1 with newReceipts := ar1.newReceipts ++ rcpts, ret := ret,
                       subsidized := ar1.subsidized + s.subsidized })

def applyActionW (fc : FcFn) (fl : Flags) (cfg : NearCfg) (c : ActCtx) (st : ActSt) (a : Act) : M (ActSt × AR) := do
  match a with
  | .base ⟨_, b@(.fcall _ _ _ _)⟩ =>
    let ex := actExec c.r.recv a
    let res : AR := { gasBurnt := ex.gas, gasUsed := ex.gas, compute := ex.compute,
                      ok := true, newReceipts := [], proposals := [], tokensBurnt := 0 }
    let elig := c.nActs == 1 && c.r.pred != AccountId.system
    if !existenceOk a st.account c.r.recv elig then return (st, res.fail)
    if !permissionOk a st.account st.actor c.r.recv then return (st, res.fail)
    try fc fl cfg c st res b
    catch e => throw (if e.startsWith "unmodeled" then oodE e else e)
  | .base ⟨_, b@(.deployGlobal _)⟩
  | .base ⟨_, b@(.useGlobal _)⟩
  | .base ⟨_, b@(.stateInit _)⟩ => applyGlobal fl.globalActions c st a b
  | _ => ordinaryAction c st a

def actionLoopW (aa : AaFn) (fl : Flags) (hooks : NearCfg) (env : Env) (r : Rcpt) (a : ActionR)
    (inputs : List (Option Bytes)) (deployed : List Bytes) (attempted : List Bytes := []) :
    Nat → List Act → ActSt × AR → M (ActSt × AR)
  | _, [], acc => pure acc
  | i, act :: rest, (st, res) => do
    let c : ActCtx := { env, r, a, idx := i, nActs := a.actions.length, inputs, deployed, attempted }
    modify fun r => { r with vmErr := none }
    let (st', ar) ← aa fl hooks c st act
    let badNew := ar.ok && ar.newReceipts.any (fun x => !validReceipt true x)
    let ar := if badNew then ar.fail else ar
    if !ar.ok && (← get).observe then
      let vm := (← get).vmErr
      let kind := if badNew then "NewReceiptValidationError"
        else match vm with
          | some e => s!"FunctionCallError({e})"
          | none => FailureKinds.actionKind c st act
      modify fun r => { r with curFail := some s!"ActionError[{i}].{kind}" }
    let st := st'
    -- merge (lib.rs:439-493): asserts, then gas / gas_burnt_for_function_call / gas_used / compute
    if ar.gasFC > ar.gasBurnt then throw (panicked "gas_burnt_for_function_call > gas_burnt")
    if ar.gasBurnt > ar.gasUsed then throw (panicked "gas_burnt > gas_used")
    let gb ← okR (add64 res.gasBurnt ar.gasBurnt) (panicked "gas_burnt overflow")
    let gfc ← okR (add64 res.gasFC ar.gasFC) (panicked "gas_burnt_for_function_call overflow")
    let gu ← okR (add64 res.gasUsed ar.gasUsed) (panicked "gas_used overflow")
    let cu ← okR (add64 res.compute ar.compute) (panicked "compute overflow")
    let res := { res with gasBurnt := gb, gasUsed := gu, compute := cu, gasFC := gfc,
                          logs := res.logs ++ ar.logs }
    if ar.ok then
      let tb ← okR (add128 res.tokensBurnt ar.tokensBurnt) (panicked "tokens_burnt overflow")
      let sub ← okR (add128 res.subsidized ar.subsidized) (panicked "subsidized_amount overflow")
      actionLoopW aa fl hooks env r a inputs deployed attempted (i + 1) rest
        (st, { res with newReceipts := res.newReceipts ++ ar.newReceipts,
                        proposals := res.proposals ++ ar.proposals, tokensBurnt := tb,
                        subsidized := sub, ret := ar.ret.shift res.newReceipts.length })
    else pure (st, res.fail)


def applyActionReceiptW (al : AlFn) (fl : Flags) (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt) (a : ActionR) :
    M (RS × OutD1 × Nat) := do
  -- 1. input data: read and remove, then commit (E3: the decoded data is kept, in order)
  let (o, inputs) ← a.inputs.foldlM (fun ((o, ins) : Ovl × List (Option Bytes)) d => do
      match ← getR o (kReceivedData r.recv d) "received data" with
      | none => throw (inconsistent "received data should be in the state")
      | some b => match decodeReceivedData b with
        | some x => pure (o.remove (kReceivedData r.recv d), ins ++ [x])
        | none => throw (inconsistent "received data")) (rs.o, [])
  let o := o.commit
  -- 2. receiver account
  let acct ← getAcctR o r.recv
  startReceipt
  modify fun x => { x with curFail := none }
  let res0 : AR := { gasBurnt := Fees.nar.exec, gasUsed := Fees.nar.exec,
                     compute := Fees.nar.execCompute, ok := true, newReceipts := [],
                     proposals := [], tokensBurnt := 0 }
  -- 3. actions
  let (st, res) ← al fl hooks env r a inputs rs.deployed rs.attempted 0 a.actions
    ({ o := o, account := acct, actor := r.pred }, res0)
  modifyPipe (·.recordDeploys st.deploys)
  let mut o := st.o
  let mut res := res
  -- 4. storage stake
  if res.ok then
    match st.account with
    | some x =>
      match storageStakeOk x x.amount with
      | some true => o := o.setAcct r.recv x
      | some false =>
        res := res.fail
        modify fun x => { x with curFail := some "ActionError[None].LackBalanceForState" }
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
      let dep ← okR (totalDeposit a.actions) (panicked "IntegerOverflowError")
      otherBurnt ← okR (add128 otherBurnt dep) (panicked "IntegerOverflowError")
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
  let tb ← okR (add128 b0 charge >>= fun x => add128 x res.tokensBurnt) (panicked "IntegerOverflowError")
  -- E10: receiver reward (lib.rs:989-1021): burn · ⌊gasFC · 3/10⌋ to the receiver if it still
  -- exists; the outcome's tokens_burnt (`tb`) keeps it, the chunk's tx_burnt does not.
  -- gasFC = 0 in D2 ⇒ rew = 0 ⇒ the D2 path.
  if res.gasFC * 3 ≥ two64 then throw (panicked "receiver_gas_reward overflow")
  let rew := burn * (res.gasFC * 3 / 10)
  if rew ≥ two128 then throw (panicked "IntegerOverflowError")
  let (o2, txb) ← if rew > 0 then do
      match ← getAcctR o2 r.recv with
      | some x =>
        if rew > tb then throw (panicked "tx_burnt_amount - receiver_reward underflow")
        if x.amount + rew ≥ two128 then throw (panicked "IntegerOverflowError")
        pure ((o2.setAcct r.recv { x with amount := x.amount + rew }).commit, tb - rew)
      | none => pure (o2, tb)
    else pure (o2, tb)
  let txBurnt ← okR (add128 rs.txBurnt txb) (panicked "IntegerOverflowError")
  let subsidized ← okR (add128 rs.subsidized res.subsidized) (panicked "IntegerOverflowError")
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
  let (rs, ids) ← emitReceipts fl.globalActions env r.rid rs 0 (newRs ++ dataRs)
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
  if !res.ok then
    let kind := (← get).curFail.getD FailureKinds.unclassified
    modifyDetail fun d => { d with failKinds := d.failKinds ++ [(r.rid, kind)] }
  pure (rs, out, res.compute)


def processReceiptW (aar : AarFn) (fl : Flags) (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt) :
    M (RS × Option (OutD1 × Nat)) := do
  let recv := r.recv
  match r.body with
  | .distribution d =>
    if !fl.globalActions then throw oodGcd
    let (rs, forward, materialized) ← logged (GlobalExecution.applyDistributionL env rs r d)
    if let some code := materialized then
      modify fun state => { state with materialized := state.materialized ++ [code] }
      modifyPipe (·.recordDeploys [code])
    let rs ← match forward with
      | some next => forwardOrBufferR fl.globalActions env rs next
      | none => pure rs
    pure (rs, none)
  | .data false d x =>
    let o := rs.o.set (kReceivedData recv d) (encOptBytes x)
    match ← getR o (kPostponedId recv d) "postponed receipt id" with
    | none => pure ({ rs with o := o.commit }, none)
    | some ridb =>
      if ridb.length != 32 then throw (inconsistent "postponed receipt id")
      let o := o.remove (kPostponedId recv d)
      let cnt ← match ← getR o (kPendingCount recv ridb) "pending data count" with
        | none => throw (inconsistent "pending data count should be in the state")
        | some b => okR (decodeU32 b) (inconsistent "pending data count")
      if cnt == 1 then
        let o := o.remove (kPendingCount recv ridb)
        let pr ← match ← getR o (kPostponed recv ridb) "postponed receipt" with
          | none => throw (inconsistent "pending receipt should be in the state")
          | some b => decodeStoredRcptR fl.globalActions b "postponed receipt"
        let o := o.remove (kPostponed recv ridb)
        match pr.body with
        | .action _ a =>
          let (rs, out, cu) ← aar fl hooks env { rs with o := o } pr a
          pure (rs, some (out, cu))
        | _ => throw (panicked "given receipt should be an action receipt")
      else
        if cnt == 0 then throw (inconsistent "pending data count is 0, but there is a new DataReceipt")
        let o := o.set (kPendingCount recv ridb) (u32 (cnt - 1))
        pure ({ rs with o := o.commit }, none)
  | .action false a =>
    let (o, pending) ← a.inputs.foldlM (fun (o, n) d => do
        if ← containsR o (kReceivedData recv d) "received data" then pure (o, n)
        else pure (o.set (kPostponedId recv d) r.rid, n + 1)) (rs.o, 0)
    if pending == 0 then
      let (rs, out, cu) ← aar fl hooks env { rs with o := o } r a
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
      match ← getR rs.o (kYieldStatus recv d) "promise yield status" with
      | some [1] => return (rs, none)
      | some [0] | none => pure ()
      | some _ => throw (inconsistent "promise yield status")
    match ← getR rs.o (kYieldReceipt recv d) "promise yield receipt" with
    | none => pure (rs, none)
    | some b =>
      let yr ← decodeStoredRcptR fl.globalActions b "promise yield receipt"
      let o := (rs.o.remove (kYieldReceipt recv d)).remove (kYieldStatus recv d)
      let o ← match ← getR o (kDataToYield recv d) "data id to yield id" with
        | none => pure o
        | some y =>
          if y.length != 32 then throw (inconsistent "yield id")
          pure ((o.remove (kYieldToData recv y)).remove (kDataToYield recv d))
      let o := o.set (kReceivedData recv d) (encOptBytes x)
      match yr.body with
      | .action _ a =>
        let (rs, out, cu) ← aar fl hooks env { rs with o := o } yr a
        pure (rs, some (out, cu))
      | _ => throw (panicked "given receipt should be an action receipt")


def processWithTotalsW (pr : PrFn) (fl : Flags) (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt) : M RS := do
  modifyPipe Pipeline.startReceipt
  let before := rs.o
  let (rs, o) ← pr fl hooks env rs r
  -- W01 attribution: the receipt and the receipt whose outcome it produced (a postponed or
  -- yielded receipt the data receipt completed)
  let ids := match o with
    | some (out, _) => if out.o.id == r.rid then [r.rid] else [r.rid, out.o.id]
    | none => [r.rid]
  if (← get).observe then
    pushAttrib ids (committedDiff before rs.o.commit)
  match o with
  | none => pure rs
  | some (out, cu) =>
    let g ← okR (add64 rs.gas out.o.gasBurnt) (panicked "IntegerOverflowError")
    let c ← okR (add64 rs.compute cu) (panicked "IntegerOverflowError")
    modifyDetail fun d => { d with outCompute := d.outCompute ++ [(out.o.id, cu)] }
    pure { rs with gas := g, compute := c, outcomes := rs.outcomes ++ [out] }


/-- `processWithInstant.drain`, verbatim, over its `processWithTotals`. -/
def drainW (pwt : PwFn) (fl : Flags) (hooks : NearCfg) (env : Env) : Nat → RS → M RS
    | 0, _ => throw (panicked "instant receipt fuel")
    | fuel + 1, rs =>
      match rs.instant with
      | [] => pure rs
      | ir :: more => do
        let rs ← pwt fl hooks env { rs with instant := more } ir
        drainW pwt fl hooks env fuel rs

/-- `processWithInstant`, verbatim, over its `processWithTotals`. -/
def processWithInstantW (pwt : PwFn) (fl : Flags) (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt) :
    M RS := do
  let rs ← pwt fl hooks env rs r
  drainW pwt fl hooks env 100000 rs

/-! ## The copies at the original callees are the originals -/

theorem fcW_std : fcW (vmCall wasmFuel) = functionCallRecorded := by
  funext fl cfg c st ar b; rfl

theorem applyActionW_std : applyActionW functionCallRecorded = applyAction := by
  funext fl cfg c st a; rfl

theorem actionLoopW_std : @actionLoopW applyAction = @actionLoop := by
  funext fl hooks env r a inputs deployed attempted i l acc
  induction l generalizing i acc with
  | nil => rfl
  | cons act rest ih =>
    obtain ⟨st, res⟩ := acc
    rw [actionLoopW.eq_2, actionLoop.eq_2]
    simp only [ih]
    rfl

theorem applyActionReceiptW_std : applyActionReceiptW @actionLoop = applyActionReceipt := by
  funext fl hooks env rs r a; rfl

theorem processReceiptW_std : processReceiptW applyActionReceipt = processReceipt := by
  funext fl hooks env rs r; rfl

theorem processWithTotalsW_std : processWithTotalsW processReceipt = processWithTotals := by
  funext fl hooks env rs r; rfl

theorem drainW_std (fl : Flags) (hooks : NearCfg) (env : Env) :
    drainW processWithTotals fl hooks env = processWithInstant.drain fl hooks env := by
  funext n rs
  induction n generalizing rs with
  | zero => rfl
  | succ n ih =>
    simp only [drainW, processWithInstant.drain]
    cases rs.instant with
    | nil => rfl
    | cons ir more => simp only [ih]

theorem processWithInstantW_std : processWithInstantW processWithTotals = processWithInstant := by
  funext fl hooks env rs r
  simp only [processWithInstantW, drainW_std, processWithInstant]

/-! ## Monotonicity in the callee -/

/-- `x ⊑ y`: every successful result of `x` (from any recorder state and environment) is a
successful result of `y`. -/
def MLe {α : Type} (x y : M α) : Prop :=
  ∀ r e a r', x r e = .ok (a, r') → y r e = .ok (a, r')

theorem MLe.refl {α : Type} (x : M α) : MLe x x := fun _ _ _ _ h => h

theorem MLe.bind' {α β : Type} {x1 x2 : M α} {f1 f2 : α → M β}
    (hf : ∀ a, MLe (f1 a) (f2 a)) (hx : MLe x1 x2) : MLe (x1 >>= f1) (x2 >>= f2) := by
  intro r e b r' h
  rw [NearSpecV3.E2E.M.bind_run] at h ⊢
  unfold NearSpecV3.E2E.bindRes at h ⊢
  rcases h1 : x1 r e with err | ⟨a, r1⟩ <;> rw [h1] at h
  · cases h
  · rw [hx r e a r1 h1]; exact hf a r1 e b r' h

theorem MLe.liftE {α : Type} {x1 x2 : Except String α} (h : ∀ v, x1 = .ok v → x2 = .ok v) :
    MLe (StorageExecution.liftE x1) (StorageExecution.liftE x2) := by
  intro r e a r' hx
  unfold StorageExecution.liftE at hx ⊢
  rcases h1 : x1 with err | v <;> rw [h1] at hx
  · cases hx
  · rw [h v h1]; exact hx

theorem MLe.tryCatch_throw {α : Type} {x1 x2 : M α} (g : String → String) (hx : MLe x1 x2) :
    MLe (tryCatch x1 (fun e => throw (g e))) (tryCatch x2 (fun e => throw (g e))) := by
  intro r e a r' h
  have e1 : (tryCatch x1 (fun e => throw (g e)) : M α) r e =
      Except.tryCatch (x1 r e) (fun err => Except.error (g err)) := rfl
  have e2 : (tryCatch x2 (fun e => throw (g e)) : M α) r e =
      Except.tryCatch (x2 r e) (fun err => Except.error (g err)) := rfl
  rw [e1] at h; rw [e2]
  rcases h1 : x1 r e with err | ⟨b, r1⟩ <;> rw [h1] at h
  · cases h
  · rw [hx r e b r1 h1]; exact h

/-- Walk two copies of a `do` block that differ only in the callee: descend under binds, split
`if`/`match` together, close identical leaves by reflexivity and callee leaves by hypothesis. -/
syntax "mono_walk" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| mono_walk) => `(tactic| (
      first
        | (with_reducible exact MLe.refl _)
        | (apply hcallee)
        | (apply ih)
        | (with_reducible refine MLe.bind' (fun _ => ?_) ?_) <;> mono_walk
        | (refine MLe.tryCatch_throw _ ?_; mono_walk)
        | (split <;> mono_walk)
        | (cases ‹_ × _›; mono_walk)
        | (dsimp only; mono_walk)))

theorem fcW_mono {vm1 vm2 : VmFn}
    (hcallee : ∀ cfg code m ctx real, MLe (StorageExecution.liftE (vm1 cfg code m ctx real))
      (StorageExecution.liftE (vm2 cfg code m ctx real))) :
    ∀ fl cfg c st ar b, MLe (fcW vm1 fl cfg c st ar b) (fcW vm2 fl cfg c st ar b) := by
  intro fl cfg c st ar b
  unfold fcW
  mono_walk

theorem applyActionW_mono {fc1 fc2 : FcFn}
    (hcallee : ∀ fl cfg c st ar b, MLe (fc1 fl cfg c st ar b) (fc2 fl cfg c st ar b)) :
    ∀ fl cfg c st a, MLe (applyActionW fc1 fl cfg c st a) (applyActionW fc2 fl cfg c st a) := by
  intro fl cfg c st a
  unfold applyActionW
  mono_walk

theorem actionLoopW_mono {aa1 aa2 : AaFn}
    (hcallee : ∀ fl cfg c st a, MLe (aa1 fl cfg c st a) (aa2 fl cfg c st a)) :
    ∀ fl hooks env r a inputs deployed attempted i l acc,
      MLe (@actionLoopW aa1 fl hooks env r a inputs deployed attempted i l acc)
        (@actionLoopW aa2 fl hooks env r a inputs deployed attempted i l acc) := by
  intro fl hooks env r a inputs deployed attempted i l acc
  induction l generalizing i acc with
  | nil => rw [actionLoopW.eq_1, actionLoopW.eq_1]; exact MLe.refl _
  | cons act rest ih =>
    obtain ⟨st, res⟩ := acc
    rw [actionLoopW.eq_2, actionLoopW.eq_2]
    mono_walk

theorem applyActionReceiptW_mono {al1 al2 : AlFn}
    (hcallee : ∀ fl hooks env r a inputs deployed attempted i l acc,
      MLe (al1 fl hooks env r a inputs deployed attempted i l acc)
        (al2 fl hooks env r a inputs deployed attempted i l acc)) :
    ∀ fl hooks env rs r a, MLe (applyActionReceiptW al1 fl hooks env rs r a)
      (applyActionReceiptW al2 fl hooks env rs r a) := by
  intro fl hooks env rs r a
  unfold applyActionReceiptW
  mono_walk

theorem processReceiptW_mono {aar1 aar2 : AarFn}
    (hcallee : ∀ fl hooks env rs r a, MLe (aar1 fl hooks env rs r a) (aar2 fl hooks env rs r a)) :
    ∀ fl hooks env rs r, MLe (processReceiptW aar1 fl hooks env rs r)
      (processReceiptW aar2 fl hooks env rs r) := by
  intro fl hooks env rs r
  unfold processReceiptW
  mono_walk

theorem processWithTotalsW_mono {pr1 pr2 : PrFn}
    (hcallee : ∀ fl hooks env rs r, MLe (pr1 fl hooks env rs r) (pr2 fl hooks env rs r)) :
    ∀ fl hooks env rs r, MLe (processWithTotalsW pr1 fl hooks env rs r)
      (processWithTotalsW pr2 fl hooks env rs r) := by
  intro fl hooks env rs r
  unfold processWithTotalsW
  mono_walk

theorem drainW_mono {pw1 pw2 : PwFn}
    (hcallee : ∀ fl hooks env rs r, MLe (pw1 fl hooks env rs r) (pw2 fl hooks env rs r)) :
    ∀ fl hooks env n rs, MLe (drainW pw1 fl hooks env n rs) (drainW pw2 fl hooks env n rs) := by
  intro fl hooks env n rs
  induction n generalizing rs with
  | zero => exact MLe.refl _
  | succ n ih =>
    simp only [drainW]
    mono_walk

theorem processWithInstantW_mono {pw1 pw2 : PwFn}
    (hcallee : ∀ fl hooks env rs r, MLe (pw1 fl hooks env rs r) (pw2 fl hooks env rs r)) :
    ∀ fl hooks env rs r, MLe (processWithInstantW pw1 fl hooks env rs r)
      (processWithInstantW pw2 fl hooks env rs r) := by
  intro fl hooks env rs r
  unfold processWithInstantW
  refine MLe.bind' (fun _ => drainW_mono hcallee _ _ _ _ _) (hcallee _ _ _ _ _)

/-! ## The VM oracle -/

/-- A VM query: the arguments of one `vmCall` (the call machine's `CallArgs`). -/
abbrev VmQ := NearSpecV3.Wasm.CallCut.CallArgs

/-- A VM oracle: an answer (or a failure) for every query. -/
abbrev VmO := VmQ → Except String Run

/-- The checker's VM: `vmCall wasmFuel`. -/
def vmStd : VmO := fun q => vmCall wasmFuel q.cfg q.code q.method q.ctx q.real

def vmOf (o : VmO) : VmFn := fun cfg code method ctx real => o ⟨cfg, code, method, ctx, real⟩

theorem vmOf_std : vmOf vmStd = vmCall wasmFuel := rfl

/-- The checker's VM answers every query with the call machine's result. -/
theorem vmStd_eq (q : VmQ) : vmStd q = .ok (NearSpecV3.Wasm.CallCut.callResult q) := rfl

/-- `processWithInstant` with its VM calls answered by the oracle `o`. -/
def pwO (o : VmO) : PwFn :=
  processWithInstantW (processWithTotalsW (processReceiptW (applyActionReceiptW
    (@actionLoopW (applyActionW (fcW (vmOf o)))))))

/-- **At the checker's VM, the oracle receipt step is the receipt step.** -/
theorem pwO_std : pwO vmStd = processWithInstant := by
  unfold pwO
  rw [vmOf_std, fcW_std, applyActionW_std, actionLoopW_std, applyActionReceiptW_std,
    processReceiptW_std, processWithTotalsW_std, processWithInstantW_std]

/-- `o1 ≤ o2`: every answer of `o1` is the answer of `o2`. -/
def OLe (o1 o2 : VmO) : Prop := ∀ q v, o1 q = .ok v → o2 q = .ok v

/-- **The oracle receipt step is monotone in the oracle.** -/
theorem pwO_mono {o1 o2 : VmO} (h : OLe o1 o2) :
    ∀ fl hooks env rs r, MLe (pwO o1 fl hooks env rs r) (pwO o2 fl hooks env rs r) :=
  processWithInstantW_mono (processWithTotalsW_mono (processReceiptW_mono
    (applyActionReceiptW_mono (actionLoopW_mono (applyActionW_mono (fcW_mono
      (fun cfg code m ctx real => MLe.liftE (fun v hv => h _ v hv))))))))

#print axioms pwO_std
#print axioms pwO_mono

end NearSpecV3.Successor.StorageExecution.CutW
