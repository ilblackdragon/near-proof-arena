import NearSpecV3.Successor.TierO4Receipt

/-!
# W12 / O4 — the proof-side recorder copy `NS` (README §14)

`EngineObligations` (§12) cannot be satisfied (§13, `remClosed_soft_absurd`): its premises quantify
over every value. §14 replaces them by premises on the witness. This module defines the proof-side
copy of the recorder engine (`StorageExecution`, at `fl0`) that the first of them refers to:

* **no soft-limit test** (G1): `processLocals`, `processDelayedLoop`, `processIncoming` and
  `yieldLoop` never consult `softExceeded`;
* **a fresh store for every VM call** (G6): the call's `RealStore` gets an empty recorder, an empty
  TTN cache and `recBefore = 0`, exactly as the legacy hook builds it, and the recorder is not
  updated from the VM;
* **a named exclusion where only a rolled-back deploy serves the code** (G3b, found this session):
  `resolveColdCodeNS` is `resolveColdCode` except that a code found only among the chunk's
  rolled-back deploys (`attempted`, not `committed`, not the receiver's own pre-state contract) is
  `out of domain (e.code_attempted_only)` instead of being served. The legacy engine rejects it
  (`MissingTrieValue`); nearcore serves it from the compiled-contract cache.

The rest is a copy of the recorder at `fl0` (global actions off, the cold code policy). Within the
`FunctionCall` hook the copy works on the state with the revealed pre-state trie
(`st.wt (preT …)`), which is the recorder's own state on every run (the recorder starts from
`Ovl.ofTrie (revealAll …)`), and computes the call after code selection in `Except` (`callTailNS`):
nothing there reads or writes the recorder except the recorder's own logged read of
`PromiseYieldIndices`, which only feeds the recorder. Observation-only updates (`setVmErr`) are
dropped from the hook.

No checker uses `NS`: it is a reference for the per-witness premise
`Tier.checker .storageResolution c w = checkNS c w` (`TierO4NSSim.lean`), which the instrumented
checker measures (`--o4-premises`, `MainSuccessor.lean`).
-/

namespace NearSpecV3.Successor.StorageExecutionNS
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged
open NearSpecV3.Wasm NearSpecV3.D3
open NearSpecV3.Successor.StorageExecution

/-- The legacy hook's pre-state contract hash of the receiver (`D3.functionCall`'s `preHash`). -/
def preHashOf (o : Ovl) (recv : Bytes) : Option Bytes :=
  match o.trie.find (nibbles (kAccount recv)) with
  | some (some raw) => match decodeAcct raw with
    | some x => match x.contract with | .local h0 => some h0 | _ => none
    | none => none
  | _ => none

/-- G3b: code that only a rolled-back in-chunk deploy provides, for a receiver whose pre-state
contract is a different one. -/
def attemptedOnlyExclusion : String :=
  "out of domain (e.code_attempted_only): contract code served only by a rolled-back in-chunk deploy"

/-- `resolveColdCode` with the G3b exclusion (module comment). -/
def resolveColdCodeNS (sources : CodeSources) (timely preIs : Bool) (hash : Bytes) : Except String Bytes :=
  match sources.witness hash with
  | some code => .ok code
  | none =>
    match sources.current.find? (fun code => sha256 code == hash) with
    | some code => .ok code
    | none =>
      match (sources.committed ++ sources.attempted).find? (fun code => sha256 code == hash) with
      | some code =>
        if !timely then .error raceExclusion
        else if !preIs && (sources.committed.find? (fun code => sha256 code == hash)).isNone then
          .error attemptedOnlyExclusion
        else .ok code
      | none => .error missingCode

/-- The legacy hook's tail after code selection, with the recorder's fuel certificate (`vmCall`)
and the legacy fresh `RealStore`. -/
def callTailNS (cfg : NearCfg) (c : ActCtx) (st : ActSt) (ar : AR) (method args : Bytes) (gas deposit : Nat)
    (acct : D2.Acct) (hh code : Bytes) : Except String (ActSt × AR) := do
  let env := c.env
  let h := env.ctx.height
  let codeB := toBA code
  if let some why := contractOOD cfg codeB then throw (oodE why)
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
    accountContract := some (toBA hh) }
  let pfx := TTN.contractDataPrefix ctx.currentAccount
  let ovl : TTN.BMap (Option ByteArray) :=
    (st.o.committed ++ st.o.prosp).foldl (fun m (k, v) =>
      m.insert (toBA k) (v.map toBA)) {}
  let real : TTN.RealStore := { store := fun hb => (env.codeOf (ofBA hb)).map toBA,
                                root := toBA env.preRoot, overlay := ovl, pfx }
  match ← vmCall wasmFuel cfg codeB (strOf method) ctx real with
  | .line l =>
    let (burnt, used) ← lineOutcome l
    let gb := ar.gasBurnt + burnt
    pure (st, { ar.fail with gasBurnt := gb, gasFC := ar.gasFC + burnt, gasUsed := ar.gasUsed + used })
  | .done s err =>
    let o := match s.real with
      | some r => r.writes.foldl (fun (o : Ovl) (k, v) => match v with
          | some v => o.set (ofBA k) (ofBA v)
          | none => o.remove (ofBA k)) st.o
      | none => st.o
    let st := { st with o }
    let burnt := s.gas.burnt
    let logs := s.logs.toList.map ofBA
    let (rs, idx, resumes) ← manager s.actions ah h
    let (rs, extra) ← distribute rs gas s.gas.used
    let used := s.gas.used + extra
    let ar1 := { ar with gasBurnt := ar.gasBurnt + burnt, gasFC := ar.gasFC + burnt,
                         gasUsed := ar.gasUsed + used, compute := ar.compute + s.gas.computeUsage,
                         logs := ar.logs ++ logs }
    match err with
    | some e =>
      if e.startsWith "unmodeled" then throw (oodE e)
      if e.startsWith "invalid" || e.startsWith "StorageInconsistentState" then throw s!"invalid: {e}"
      pure (st, ar1.fail)
    | none =>
      let (yf, yn) ← st.o.getIndices kYieldIdx "PromiseYieldIndices"
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
        let acts ← finishActs m
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

/-- The `FunctionCall` hook of `NS` (module comment). -/
def functionCallNS (cfg : NearCfg) (c : ActCtx) (st0 : ActSt) (ar : AR) (b : Base) : M (ActSt × AR) := do
  let st := st0.wt (preT c.env.store c.env.preRoot)
  let .fcall method args gas deposit := b | throw "unmodeled: functionCall hook on a non-FunctionCall"
  let some acct := st.account | throw "invalid: EXPECT_ACCOUNT_EXISTS"
  if acct.amount + deposit ≥ 2 ^ 128 then
    throw "invalid: StorageInconsistentState (account balance overflow on deposit)"
  let (codeHash, _) ← resolveCode c st acct
  match codeHash with
  | none => pure (st, ar.fail)
  | some hh =>
    let recording ← get
    let sources : CodeSources := { witness := c.env.codeOf, current := st.deploys,
                                   committed := c.deployed, attempted := c.attempted }
    let timely := recording.pipe.deterministic c.r.rid c.idx hh
    let code ← liftE (resolveColdCodeNS sources timely (preHashOf st.o c.r.recv == some hh) hh)
    liftE (callTailNS cfg c st ar method args gas deposit acct hh code)

def applyAction (cfg : NearCfg) (c : ActCtx) (st : ActSt) (a : Act) : M (ActSt × AR) := do
  match a with
  | .base ⟨_, b@(.fcall _ _ _ _)⟩ =>
    let ex := actExec c.r.recv a
    let res : AR := { gasBurnt := ex.gas, gasUsed := ex.gas, compute := ex.compute,
                      ok := true, newReceipts := [], proposals := [], tokensBurnt := 0 }
    let elig := c.nActs == 1 && c.r.pred != AccountId.system
    if !existenceOk a st.account c.r.recv elig then return (st, res.fail)
    if !permissionOk a st.account st.actor c.r.recv then return (st, res.fail)
    try functionCallNS cfg c st res b
    catch e => throw (if e.startsWith "unmodeled" then oodE e else e)
  | .base ⟨_, b@(.deployGlobal _)⟩
  | .base ⟨_, b@(.useGlobal _)⟩
  | .base ⟨_, b@(.stateInit _)⟩ => applyGlobal false c st a b
  | _ => ordinaryAction c st a

def actionLoop (hooks : NearCfg) (env : Env) (r : Rcpt) (a : ActionR)
    (inputs : List (Option Bytes)) (deployed : List Bytes) (attempted : List Bytes := []) :
    Nat → List Act → ActSt × AR → M (ActSt × AR)
  | _, [], acc => pure acc
  | i, act :: rest, (st, res) => do
    let c : ActCtx := { env, r, a, idx := i, nActs := a.actions.length, inputs, deployed, attempted }
    modify fun r => { r with vmErr := none }
    let (st', ar) ← applyAction hooks c st act
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
      actionLoop hooks env r a inputs deployed attempted (i + 1) rest
        (st, { res with newReceipts := res.newReceipts ++ ar.newReceipts,
                        proposals := res.proposals ++ ar.proposals, tokensBurnt := tb,
                        subsidized := sub, ret := ar.ret.shift res.newReceipts.length })
    else pure (st, res.fail)

def applyActionReceipt (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt) (a : ActionR) :
    M (RS × OutD1 × Nat) := do
  let (o, inputs) ← a.inputs.foldlM (fun ((o, ins) : Ovl × List (Option Bytes)) d => do
      match ← getR o (kReceivedData r.recv d) "received data" with
      | none => throw (inconsistent "received data should be in the state")
      | some b => match decodeReceivedData b with
        | some x => pure (o.remove (kReceivedData r.recv d), ins ++ [x])
        | none => throw (inconsistent "received data")) (rs.o, [])
  let o := o.commit
  let acct ← getAcctR o r.recv
  startReceipt
  modify fun x => { x with curFail := none }
  let res0 : AR := { gasBurnt := Fees.nar.exec, gasUsed := Fees.nar.exec,
                     compute := Fees.nar.execCompute, ok := true, newReceipts := [],
                     proposals := [], tokensBurnt := 0 }
  let (st, res) ← actionLoop hooks env r a inputs rs.deployed rs.attempted 0 a.actions
    ({ o := o, account := acct, actor := r.pred }, res0)
  modifyPipe (·.recordDeploys st.deploys)
  let mut o := st.o
  let mut res := res
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
  let purchase := a.gasPrice
  let burn := min purchase env.ctx.gasPrice
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
  let o2 := if res.ok then o.commit else o.rollback
  let deployed := if res.ok then rs.deployed ++ st.deploys else rs.deployed
  let gasOut := if isSystem then 0 else res.gasBurnt
  let b0 := burn * gasOut
  if b0 ≥ two128 then throw (panicked "IntegerOverflowError")
  let tb ← okR (add128 b0 charge >>= fun x => add128 x res.tokensBurnt) (panicked "IntegerOverflowError")
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
  let (rs, ids) ← emitReceipts false env r.rid rs 0 (newRs ++ dataRs)
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

def processReceipt (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt) :
    M (RS × Option (OutD1 × Nat)) := do
  let recv := r.recv
  match r.body with
  | .distribution _ => throw oodGcd
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
          | some b => decodeStoredRcptR false b "postponed receipt"
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
        if ← containsR o (kReceivedData recv d) "received data" then pure (o, n)
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
      match ← getR rs.o (kYieldStatus recv d) "promise yield status" with
      | some [1] => return (rs, none)
      | some [0] | none => pure ()
      | some _ => throw (inconsistent "promise yield status")
    match ← getR rs.o (kYieldReceipt recv d) "promise yield receipt" with
    | none => pure (rs, none)
    | some b =>
      let yr ← decodeStoredRcptR false b "promise yield receipt"
      let o := (rs.o.remove (kYieldReceipt recv d)).remove (kYieldStatus recv d)
      let o ← match ← getR o (kDataToYield recv d) "data id to yield id" with
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

def processWithTotals (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt) : M RS := do
  modifyPipe Pipeline.startReceipt
  let before := rs.o
  let (rs, o) ← processReceipt hooks env rs r
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

def processWithInstant (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt) : M RS := do
  let rs ← processWithTotals hooks env rs r
  let rec drain : Nat → RS → M RS
    | 0, _ => throw (panicked "instant receipt fuel")
    | fuel + 1, rs =>
      match rs.instant with
      | [] => pure rs
      | ir :: more => do
        let rs ← processWithTotals hooks env { rs with instant := more } ir
        drain fuel rs
  drain 100000 rs

/-- `processLocals` without the soft-limit test (G1). -/
def processLocals (hooks : NearCfg) (env : Env) (rs : RS) (locals : List Rcpt) : M RS := do
  let decode ← pipeDecode false
  modifyPipe (Pipeline.startList decode rs.o · locals)
  locals.foldlM (fun rs r => do
    if rs.compute ≥ env.ctx.gasLimit then logged (delayPushL rs r)
    else
      modifyPipe (Pipeline.stepList decode rs.o)
      processWithInstant hooks env rs r) rs

def processDelayedLoop (hooks : NearCfg) (env : Env) : Nat → RS → M RS
  | 0, rs => pure rs
  | fuel + 1, rs => do
    if rs.compute ≥ env.ctx.gasLimit then return rs
    let (rs, r) ← delayPopR false env (rs.dq.next - rs.dq.first + 1) rs
    match r with
    | none => pure rs
    | some r =>
      match (← get).pipe.next with
      | some n =>
        if n - 1 == 0 then scheduleDelayed false env rs
        else modifyPipe fun p => { p with next := some (n - 1) }
      | none => pure ()
      if !validReceipt false r then throw (inconsistent "Delayed receipt in the state is invalid")
      let rs ← processWithInstant hooks env rs r
      processDelayedLoop hooks env fuel rs

def processDelayed (hooks : NearCfg) (env : Env) (fuel : Nat) (rs : RS) : M RS := do
  scheduleDelayed false env rs
  processDelayedLoop hooks env fuel rs

def processIncoming (hooks : NearCfg) (env : Env) (rs : RS) (incoming : List Rcpt) : M RS := do
  let decode ← pipeDecode false
  modifyPipe (Pipeline.startList decode rs.o · incoming)
  incoming.foldlM (fun rs r => do
    if !validReceipt false r then throw (panicked "ReceiptValidationError on an incoming receipt")
    if rs.compute ≥ env.ctx.gasLimit then logged (delayPushL rs r)
    else
      modifyPipe (Pipeline.stepList decode rs.o)
      processWithInstant hooks env rs r) rs

def yieldLoop (env : Env) (next : Nat) : Nat → RS × Nat × Nat → M (RS × Nat)
  | 0, (rs, i, _) => pure (rs, i)
  | fuel + 1, (rs, i, k) => do
    if i ≥ next then return (rs, i)
    if rs.compute ≥ env.ctx.gasLimit then return (rs, i)
    let (acct, d, exp) ← match ← getR rs.o (kYieldTimeout i) "promise yield timeout" with
      | none => throw (inconsistent "PromiseYield timeout queue entry should be in the state")
      | some b => okR (decodeYieldTimeout b) (inconsistent "promise yield timeout")
    if exp > env.ctx.height then return (rs, i)
    let (rs, k) ← if ← containsR rs.o (kYieldReceipt acct d) "promise yield receipt" then do
        let rid := receiptIdFrom d env.ctx.height k
        let rs ← forwardOrBufferR false env rs ⟨acct, acct, rid, .data true d none⟩
        pure (rs, k + 1)
      else pure (rs, k)
    let rs := { rs with o := rs.o.remove (kYieldTimeout i) }
    yieldLoop env next fuel (rs, i + 1, k)

def applyNewChunkD2 (hooks : NearCfg) (prims : Prims) (env : Env) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (lastProps : List (Bytes × Nat))
    (incoming : List Rcpt) (txs : List (TxD2 × Bool)) (ownCong : Congestion) :
    M MainOutD2 := do
  let ctx := env.ctx
  let o := Ovl.ofTrie t
  let o ← match vu with
    | some f => validatorUpdateR ctx.layout ctx.own o f lastProps
    | none => pure o
  let (df, dn) ← getIndicesR o kDelayedIdx "DelayedReceiptIndices"
  let (o, so) ← schedOvlR prims ctx o
  let bufIdx ← match ← trieFindR kBufIdx with
    | none => throw (missing "BufferedReceiptIndices")
    | some none => pure []
    | some (some b) => okR (decodeBufIdx b) (inconsistent "BufferedReceiptIndices")
  let metas ← bufIdx.foldlM (fun ms (s, _, _) => do
      match ← trieFindR (kGroupsData s) with
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
  let rs ← forwardFromBufferR false env rs
  let (rs, _) ← txs.foldlM (processTxR env) (rs, [])
  let locals := rs.locals
  let rs ← processLocals hooks env { rs with locals := [] } locals
  let rs ← processDelayed hooks env (rs.dq.next - rs.dq.first + 1) rs
  let rs ← processIncoming hooks env rs incoming
  let (yf, yn) ← getIndicesR rs.o kYieldIdx "PromiseYieldIndices"
  let (rs, yf') ← yieldLoop env yn (yn - yf + 1) (rs, yf, 0)
  let rs := if yf' != yf then { rs with o := rs.o.set kYieldIdx (encIndices yf' yn) } else rs
  let cong ← liftE (applyDelayedCongestion rs.dq rs.cong)
  let allowed := ctx.layout.shardIds.getD ((ctx.height + (ctx.layout.index ctx.own).getD 0) % ctx.layout.numShards) ctx.own
  let cong := { cong with allowedShard := allowed }
  let bw ← bandwidthRequestsR env rs
  let o := rs.o.commit
  let root ← finalizeR o
  let gasUsed ← okR (sumNat64 (rs.outcomes.map (·.o.gasBurnt))) (panicked "total gas burnt overflow")
  let burnt ← okR (add128 rs.txBurnt rs.otherBurnt) (panicked "burnt balance overflow")
  if rs.subsidized > burnt then throw "invalid: balance_burnt underflow (subsidized exceeds burnt)"
  let burnt := burnt - rs.subsidized
  let recd ← get
  pure { root, outcomes := rs.outcomes, outgoing := rs.outgoing, gasUsed, balanceBurnt := burnt,
         congestion := cong, bwRequests := bw, proposals := dedupProposals rs.proposals,
         cdRemovals := o.cdRemovals, wasmGas := rs.wasmGas,
         committed := some (sortKV o.committed), compute := some rs.compute,
         detail := if recd.observe then some recd.detail else none }

/-- The `NS` main transition (module comment). -/
def run (cfg : NearCfg) (prims : Prims) (env : Env) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (props : List (Bytes × Nat))
    (incoming : List Rcpt) (txs : List (TxD2 × Bool)) (congestion : Congestion) :
    Except String MainOutD2 :=
  ((applyNewChunkD2 cfg prims env t vu props incoming txs congestion).run
    { observe := cfg.observeDetail } env).map Prod.fst

end NearSpecV3.Successor.StorageExecutionNS

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2

/-- The storage-resolution driver with the `NS` engine. -/
def recorderDriverNS (cfg : Wasm.NearCfg) : ExecutionDriver :=
  { recorderDriver cfg with
    apply := fun _ p e t vu props incoming txs congestion =>
      StorageExecutionNS.run cfg p e t vu props incoming txs congestion }

/-- The `.storageResolution` shell at the `NS` driver: the reference of the G1/G6 premise. -/
def checkNS (c w : Bytes) : Except String Unit :=
  checkD2CoreGWith (recorderDriverNS (Tier.cfg .storageResolution).wasm)
    (D3.d3Hooks (Tier.cfg .storageResolution).wasm) true c w (some maxGasBurnt)

end NearSpecV3.Successor

namespace NearSpecV3.Successor.O4E
open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## The named recorder escapes (G2, G3, G3b, G4, G7)

The strings by which the recorder (and `NS`) may fail where the legacy engine decides. The second
premise of the §14 theorem is that the storage-resolution verdict is none of them. -/

/-- G2: the fuel certificate (`StorageExecution.vmCall`). -/
def escG2 : String := D3.oodE "w.fuel_certificate: a prepared function fails the fuel certificate"
/-- G7: a global action with global actions off (`StorageExecution.applyGlobal`). -/
def escG7 : String := "out of domain (w.shape): global action"
/-- G4: nearcore's empty-buffer assertion on a V3 layout (`forwardFromBufferV3L`). -/
def escG4 : String := "invalid: buffered receipts gas left with empty outgoing buffers"

/-- The escape set: G2, G3 (`raceExclusion`), G3b (`attemptedOnlyExclusion`), G4, G7. -/
def esc (s : String) : Bool :=
  s == escG2 || s == raceExclusion || s == StorageExecutionNS.attemptedOnlyExclusion || s == escG7 ||
    s == escG4

/-- The escape's name, for the instrumented checker. -/
def escName (s : String) : String :=
  if s == escG2 then "G2" else if s == raceExclusion then "G3" else
  if s == StorageExecutionNS.attemptedOnlyExclusion then "G3b" else if s == escG7 then "G7" else
  if s == escG4 then "G4" else ""

end NearSpecV3.Successor.O4E
