import NearSpecV3.Logged.D2Runtime
import NearSpecV3.D3.GlobalContract
import NearSpecV3.D3.FunctionCall
import NearSpecV3.Successor.CodeResolution
import NearSpecV3.Successor.Pipeline
import NearSpecV3.Successor.GlobalCodecs
import NearSpecV3.Successor.GlobalExecution
import NearSpecV3.Successor.QueueExecution
import NearSpecV3.Successor.PromiseActions
import NearSpecV3.Wasm.Fuel
import NearSpecV3.Wasm.FuelCert
import NearSpecV3.Successor.FailureKinds

/-! Chunk-scoped protocol recorder over the existing read-logging D2 operations.
Reads are executed against the authenticated witness store; recorder state is computed locally.
Contract code is a separate witness access, not a trie-proof read. No recorder answers are inputs.
-/
namespace NearSpecV3.Successor.StorageExecution
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged
open NearSpecV3.Wasm

structure Recording where
  recorder : TTN.Recorder := {}
  cache : TTN.Acct := {}
  receiptStart : Nat := 0
  softLimit : Nat := 4000000
  globalActions : Bool := false
  codePolicy : CodeWitnessPolicy := .coldPartial
  /-- Authenticated code committed by distribution, distinct from local deployment tracking. -/
  materialized : List Bytes := []
  /-- The preparation pipeline's schedule, replayed to decide deploy-served code (`Pipeline`). -/
  pipe : Pipeline.Pipe := {}
  /-- Observation only (W01, `NearCfg.observeDetail`): nothing below is read by a check. -/
  observe : Bool := false
  /-- The VM error of the last function call that failed in the VM (`FunctionCallError(…)`). -/
  vmErr : Option String := none
  /-- The failure kind of the action receipt being applied. -/
  curFail : Option String := none
  detail : ObsDetail := {}

abbrev M := StateT Recording (ReaderT Env (Except String))

def liftE {α : Type} (x : Except String α) : M α := fun r _ => x.map (fun v => (v, r))
def okR {α : Type} (x : Option α) (e : String) : M α := liftE (ok? x e)

def logged {α : Type} (x : LM α) : M α := do
  let env ← read
  let (out, keys) := SM.runR (hGet env.store) (x env.preRoot)
  let state ← get
  let recorder := keys.foldl (fun acc h =>
    match env.codeOf h with
    | some bytes => acc.record (D3.toBA h) bytes.length
    | none => acc) state.recorder
  set { state with recorder }
  liftE out

def startReceipt : M Unit := modify fun r => { r with receiptStart := r.recorder.size }
def modifyPipe (f : Pipeline.Pipe → Pipeline.Pipe) : M Unit := modify fun r => { r with pipe := f r.pipe }

/-! ### Observation (W01): failure kinds, per-outcome compute, per-receipt storage attribution.
Recorded only when `Recording.observe`; never read by a check. -/

def setVmErr (e : String) : M Unit := modify fun r => { r with vmErr := some e }
def modifyDetail (f : ObsDetail → ObsDetail) : M Unit := do
  if (← get).observe then modify fun r => { r with detail := f r.detail }

/-- The error of an `abort B U <error>` harness line. -/
def lineErr (l : String) : String :=
  match l.splitOn " " with
  | "abort" :: _ :: _ :: rest => " ".intercalate rest
  | _ => l

/-- The committed changes of one step: `Ovl.commit` updates a key in place and appends a new key
(`kvPut`), so `before.committed` is a positional prefix of `after.committed`. A change is a key
whose committed value differs from its value before the step (the earlier committed value, else
the pre-state trie value). Ascending key, `none` = deleted.

The second list holds the keys first committed in this step whose pre-state *value* the witness
does not reveal (the step wrote the key without reading it, so the recorded trie holds only the
value reference): the checker cannot tell whether the write changed the value. -/
def committedDiff (before after : Ovl) : List (Bytes × Option Bytes) × List (Bytes × Option Bytes) :=
  let rec go : List (Bytes × Option Bytes) → List (Bytes × Option Bytes) → List (Bytes × Option Bytes)
    | (k, v) :: as, (k', v') :: bs =>
      let rest := go as bs
      if k == k' then (if v == v' then rest else (k, v) :: rest)
      else (k, v) :: rest  -- not reached: kvPut never reorders
    | as, [] => as
    | [], _ => []
  let all := go after.committed before.committed
  let isNew := fun (k : Bytes) => (kvFind k before.committed).isNone
  let known := all.filter fun (k, v) =>
    !isNew k || (match before.trie.find (nibbles k) with
      | some p => p != v
      | none => false)
  let unknown := all.filter fun (k, _) => isNew k && (before.trie.find (nibbles k)).isNone
  (sortKV known, sortKV unknown)

/-- The id list of an attribution entry for the keys whose pre-state value is unknown
(`committedDiff`.2): the entry's ids behind the marker id `"pre?"`. -/
def unknownPreMarker : Bytes := "pre?".toUTF8.toList

def pushAttrib (ids : List Bytes) (d : List (Bytes × Option Bytes) × List (Bytes × Option Bytes)) : M Unit :=
  modifyDetail fun x => { x with attrib := x.attrib ++ [(ids, d.1)] ++
    (if d.2.isEmpty then [] else [(unknownPreMarker :: ids, d.2)]) }
def softExceeded : M Bool := do
  let r ← get
  pure (r.recorder.size > r.softLimit)

def accountRemovals (before after : Ovl) : M Unit :=
  modify fun r => { r with recorder := { r.recorder with
    size := r.recorder.size + 2000 * (after.cdRemovals - before.cdRemovals) } }

/-- Non-VM actions use the existing logged implementation, retaining reads on action failure. -/
def ordinaryAction (c : ActCtx) (st : ActSt) (a : Act) : M (ActSt × AR) := do
  let out ← logged (applyActionL d2HooksL c st a)
  accountRemovals st.o out.1.o
  pure out

/-- All four legacy magic hashes redirect at PV86, independently of the current chain.
The target global wallet hash is selected using the current authenticated chain id. -/
def resolveCode (c : ActCtx) (st : ActSt) (acct : D2.Acct) : M (Option Bytes × Bytes) := do
  match D3.L4.Rci.resolve c.env.chainId c.r.recv acct.contract with
  | .none => pure (none, [])
  | .accountLocal h id => pure (some h, kCode id)
  | .global h (.codeHash id) => pure (some h, D3.L4.kGlobalContractCode (.codeHash id))
  | .global _ (.accountId id) =>
    let key := D3.L4.kGlobalContractCode (.accountId id)
    let _ ← logged (st.o.refLenL key "global contract identifier")
    let h ← liftE (D3.L4.Rci.resolveCodeHash st.o (.global [] (.accountId id)))
    pure (h, key)
  | .legacyEthWallet _ => throw "out of domain: pre-PV83 built-in wallet"

open NearSpecV3.D3

/-- The VM call of a `FunctionCall` action under the step budget `fuelOf cfg ctx.prepaidGas`.

W02: the call first runs the fuel certificate (`Wasm/FuelCert.lean`). `Wasm.wasmFuel_sufficient`
proves the budget `wasmFuel` never decides an outcome for a certified contract; a contract whose
prepared functions fail the certificate is out of domain (`w.fuel_certificate`) instead of being
run under a budget not proved sufficient. No measured contract fails it (evidence
`fuel-sufficiency/`). -/
def vmCall (fuelOf : NearCfg → Nat → Nat) (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) (real : TTN.RealStore) : Except String Run :=
  if !fuelCertified cfg code then .error (oodE "w.fuel_certificate: a prepared function fails the fuel certificate")
  else .ok (runCallWithLimits cfg code method ctx (fuelOf cfg ctx.prepaidGas) true false (some real))

/-- `functionCallRecorded` with the step budget as a parameter; the checker uses `wasmFuel`. -/
def functionCallRecordedF (fuelOf : NearCfg → Nat → Nat) (cfg : NearCfg) (c : ActCtx) (st : ActSt)
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
  let timely := recording.pipe.deterministic c.r.rid c.idx hh
  let code ← liftE (resolveCodeBytes recording.codePolicy sources pre hh timely)
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
    accountContract := some (toBA hh) }
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
  let vmr ← liftE (vmCall fuelOf cfg codeB (strOf method) ctx real)
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
    let (rs, idx, resumes) ← liftE ((if recording.globalActions then managerGlobal else manager) s.actions ah h)
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
        let acts ← liftE ((if recording.globalActions then finishActsGlobal else finishActs) m)
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

/-- The successor's `FunctionCall` hook: the successor step budget `wasmFuel`. -/
def functionCallRecorded (cfg : NearCfg) (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) :
    M (ActSt × AR) :=
  functionCallRecordedF wasmFuel cfg c st ar b

def applyGlobal (c : ActCtx) (st : ActSt) (a : Act) (b : Base) : M (ActSt × AR) := do
  if !(← get).globalActions then throw "out of domain (w.shape): global action"
  let ex := actExec c.r.recv a
  let res : AR := { gasBurnt := ex.gas, gasUsed := ex.gas, compute := ex.compute,
                    ok := true, newReceipts := [], proposals := [], tokensBurnt := 0 }
  let elig := c.nActs == 1 && c.r.pred != AccountId.system
  if !existenceOk a st.account c.r.recv elig then return (st, res.fail)
  if !permissionOk a st.account st.actor c.r.recv then return (st, res.fail)
  let out ← logged (GlobalExecution.applyGlobalActionL c st res b)
  accountRemovals st.o out.1.o
  pure out

/-- Dispatch shares the original fee/existence/permission checks. Only call resolution and
recorder state differ. Other actions reuse their read-logging implementation. -/
def applyAction (cfg : NearCfg) (c : ActCtx) (st : ActSt) (a : Act) : M (ActSt × AR) := do
  match a with
  | .base ⟨_, b@(.fcall _ _ _ _)⟩ =>
    let ex := actExec c.r.recv a
    let res : AR := { gasBurnt := ex.gas, gasUsed := ex.gas, compute := ex.compute,
                      ok := true, newReceipts := [], proposals := [], tokensBurnt := 0 }
    let elig := c.nActs == 1 && c.r.pred != AccountId.system
    if !existenceOk a st.account c.r.recv elig then return (st, res.fail)
    if !permissionOk a st.account st.actor c.r.recv then return (st, res.fail)
    try functionCallRecorded cfg c st res b
    catch e => throw (if e.startsWith "unmodeled" then oodE e else e)
  | .base ⟨_, b@(.deployGlobal _)⟩
  | .base ⟨_, b@(.useGlobal _)⟩
  | .base ⟨_, b@(.stateInit _)⟩ => applyGlobal c st a b
  | _ => ordinaryAction c st a

def getR (o : Ovl) (k : Bytes) (what : String) := logged (o.getL k what)
def getAcctR (o : Ovl) (k : Bytes) := logged (o.getAcctL k)
def getIndicesR (o : Ovl) (k : Bytes) (what : String) := logged (o.getIndicesL k what)
def containsR (o : Ovl) (k : Bytes) (what : String) := logged (o.containsL k what)
def finalizeR (o : Ovl) := logged o.finalizeL
/-- `receiver_shard_id` with its error: a distribution target that is neither in the layout nor in
its split history is `EpochError::ShardingError` (`receipt.rs:448-458`), which fails the chunk
application. A V2 layout's static split history is not decoded (`decodeLayout`), so an obsolete
target under a V2 layout stays out of domain: a PV86 claim's V2 layouts never change between its
epochs (`Successor.LayoutReach`), and a distribution receipt would have to outlive the static layout
change of an earlier protocol version in a receipt queue. -/
def globalTarget (layout : Layout) (r : Rcpt) : Except String Nat := do
  let target := r.routedShard layout
  if !layout.shardIds.contains target then
    if layout.lastSplit.isNone then
      throw "out of domain (c.layout): distribution target outside a V2 layout"
    throw "invalid: ShardingError: distribution target is not in the shard layout or its split history"
  pure target

def globalQueuePolicy : QueuePolicy := ⟨GlobalCodecs.decodeStoredGlobal, globalTarget⟩

def forwardOrBufferR (env : Env) (rs : RS) (r : Rcpt) : M RS := do
  if (← get).globalActions then logged (forwardOrBufferLWith globalQueuePolicy env rs r)
  else logged (forwardOrBufferL env rs r)
def delayPopR (env : Env) (fuel : Nat) (rs : RS) : M (RS × Option Rcpt) := do
  if (← get).globalActions then logged (delayPopLWith globalQueuePolicy env fuel rs)
  else logged (delayPopL env fuel rs)
def bandwidthRequestsR (env : Env) (rs : RS) :=
  if env.ctx.layout.lastSplit.isSome then logged (bandwidthRequestsV3L env rs)
  else logged (bandwidthRequestsV2AnyL env rs)
/-- `forward_from_buffer` (`congestion_control.rs:236-286`) for a V3 layout: the buffers to
`get_split_parent_shard_ids()` = `{last_split}` (`shard_layout/mod.rs:402-408`) are forwarded first,
each receipt to its shard in the current layout (a child), then the layout's own shards. Buffers to
other shards outside the layout are still excluded. A V2 layout keeps `forwardFromBufferL(With)`. -/
def forwardFromBufferV3L (globals : Bool) (env : Env) (rs : RS) : LM RS := do
  let l := env.ctx.layout
  let parents := match l.lastSplit with
    | some p => if l.shardIds.contains p then [] else [p]
    | none => []
  -- `forward_from_buffer` (`congestion_control.rs:236-289`) forwards the buffers of the last split's
  -- parent (`get_split_parent_shard_ids`, the recent split only) and of the layout's shards. A buffer
  -- to an older ancestor is not forwarded; when every forwarded buffer is empty, nearcore requires
  -- that no buffered gas is left (`:281-284`).
  let rs ← (parents ++ l.shardIds).foldlM (fun rs s =>
    if globals then forwardFromBufferToShardLWith globalQueuePolicy env rs s
    else forwardFromBufferToShardL env rs s) rs
  let allEmpty := (parents ++ l.shardIds).all fun s => let (f, n) := bufGet rs.bufIdx s; n ≤ f
  if allEmpty && rs.cong.bufferedGas != 0 then
    throw "invalid: buffered receipts gas left with empty outgoing buffers"
  pure rs

def forwardFromBufferR (env : Env) (rs : RS) : M RS := do
  if env.ctx.layout.lastSplit.isSome then logged (forwardFromBufferV3L (← get).globalActions env rs)
  else if (← get).globalActions then logged (forwardFromBufferLWith globalQueuePolicy env rs)
  else logged (forwardFromBufferL env rs)
def decodeStoredRcptR (b : Bytes) (what : String) : M Rcpt := do
  if (← get).globalActions then liftE (GlobalCodecs.decodeStoredRcptGlobal b what)
  else liftE (decodeStoredRcpt b what)
def trieFindR (key : Bytes) := logged (trieFindL key)
def processTxR (env : Env) (rs : RS × List Bytes) (tf : TxD2 × Bool) : M (RS × List Bytes) := do
  let (rs0, _) := rs
  let out ← logged (processTxD2L env rs tf)
  if (← get).observe && out.1.outcomes.length > rs0.outcomes.length then
    let (t, flag) := tf
    let rs1 := out.1
    let cu := rs1.compute - rs0.compute
    let isFail : Bool := match rs1.outcomes.getLast?.map (·.status) with
      | some OStatus.failure => true
      | _ => false
    let kinds : List (Bytes × String) := bif isFail then
        [(t.hash, "InvalidTxError." ++ FailureKinds.txKind env.ctx.gasPrice env.ctx.height rs0.o t flag)]
      else []
    modifyDetail fun d => { d with failKinds := d.failKinds ++ kinds,
                                   outCompute := d.outCompute ++ [(t.hash, cu)] }
    pushAttrib [t.hash] (committedDiff rs0.o rs1.o.commit)
  pure out
def validatorUpdateR (l : Layout) (own : Nat) (o : Ovl) (f : ValidatorUpdateFacts) (ps : List (Bytes × Nat)) :=
  logged (validatorUpdateL l own o f ps)
def schedOvlR (prims : Prims) (ctx : ApplyCtx) (o : Ovl) := logged (schedOvlL prims ctx o)

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
      actionLoop hooks env r a inputs deployed attempted (i + 1) rest
        (st, { res with newReceipts := res.newReceipts ++ ar.newReceipts,
                        proposals := res.proposals ++ ar.proposals, tokensBurnt := tb,
                        subsidized := sub, ret := ar.ret.shift res.newReceipts.length })
    else pure (st, res.fail)

/-- Assign receipt ids, queue instant receipts, forward or buffer the others
(`lib.rs:1075-1120`). Returns the ids of the action receipts. -/
def emitReceipts (env : Env) (parent : Bytes) : RS → Nat → List Rcpt → M (RS × List Bytes)
  | rs, _, [] => pure (rs, [])
  | rs, k, nr :: rest => do
    let rid := receiptIdFrom parent env.ctx.height k
    let nr := { nr with rid := rid }
    let rs ← if nr.isInstant then pure { rs with instant := rs.instant ++ [nr] }
             else forwardOrBufferR env rs nr
    let (rs, ids) ← emitReceipts env parent rs (k + 1) rest
    pure (rs, if nr.isAction then rid :: ids else ids)

/-- `apply_action_receipt` (`lib.rs:776-1164`). Returns the new state, the outcome and its
compute usage. -/
def applyActionReceipt (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt) (a : ActionR) :
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
  let (st, res) ← actionLoop hooks env r a inputs rs.deployed rs.attempted 0 a.actions
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
  let (rs, ids) ← emitReceipts env r.rid rs 0 (newRs ++ dataRs)
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

/-- `process_receipt` (`lib.rs:1303-1527`) and `process_action_receipt` (`lib.rs:1529-1597`). -/
def processReceipt (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt) :
    M (RS × Option (OutD1 × Nat)) := do
  let recv := r.recv
  match r.body with
  | .distribution d =>
    if !(← get).globalActions then throw oodGcd
    let (rs, forward, materialized) ← logged (GlobalExecution.applyDistributionL env rs r d)
    if let some code := materialized then
      modify fun state => { state with materialized := state.materialized ++ [code] }
      modifyPipe (·.recordDeploys [code])
    let rs ← match forward with
      | some next => forwardOrBufferR env rs next
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
          | some b => decodeStoredRcptR b "postponed receipt"
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
      let yr ← decodeStoredRcptR b "promise yield receipt"
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

/-- `process_receipt_with_metrics`: totals and outcome (`lib.rs:2335-2345`). -/
def processWithTotals (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt) : M RS := do
  modifyPipe Pipeline.startReceipt
  let before := rs.o
  let (rs, o) ← processReceipt hooks env rs r
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

/-- `process_receipt_and_instant_receipts` (`lib.rs:2619-2656`): instant receipts FIFO. -/
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

/-- The stored-receipt decoder of the active codec, for the pipeline's side-effect-free reads. -/
def pipeDecode : M (Bytes → Except String Rcpt) := do
  if (← get).globalActions then pure fun b => GlobalCodecs.decodeStoredRcptGlobal b "stored receipt"
  else pure fun b => decodeStoredRcpt b "stored receipt"

/-- A fresh `peek_iter` of the delayed queue and a schedule over it (`lib.rs:2452-2493`). -/
def scheduleDelayed (env : Env) (rs : RS) : M Unit := do
  let decode ← pipeDecode
  let decodeStored := if (← get).globalActions then globalQueuePolicy.decodeStored else decodeStored
  modifyPipe fun p =>
    let (p, look) := Pipeline.peekDelayed decodeStored env.ctx.layout env.ctx.own rs.o p
      (rs.dq.next - rs.dq.first + 1) rs.dq.first rs.dq.next
    let (p, _, next) := Pipeline.schedule decode rs.o p look
    { p with next }

def processLocals (hooks : NearCfg) (env : Env) (rs : RS) (locals : List Rcpt) : M RS := do
  let decode ← pipeDecode
  modifyPipe (Pipeline.startList decode rs.o · locals)
  locals.foldlM (fun rs r => do
    if rs.compute ≥ env.ctx.gasLimit || (← softExceeded) then logged (delayPushL rs r)
    else
      modifyPipe (Pipeline.stepList decode rs.o)
      processWithInstant hooks env rs r) rs

def processDelayedLoop (hooks : NearCfg) (env : Env) : Nat → RS → M RS
  | 0, rs => pure rs
  | fuel + 1, rs => do
    if rs.compute ≥ env.ctx.gasLimit || (← softExceeded) then return rs
    let (rs, r) ← delayPopR env (rs.dq.next - rs.dq.first + 1) rs
    match r with
    | none => pure rs
    | some r =>
      match (← get).pipe.next with
      | some n =>
        if n - 1 == 0 then scheduleDelayed env rs
        else modifyPipe fun p => { p with next := some (n - 1) }
      | none => pure ()
      if !validReceipt false r then throw (inconsistent "Delayed receipt in the state is invalid")
      let rs ← processWithInstant hooks env rs r
      processDelayedLoop hooks env fuel rs

def processDelayed (hooks : NearCfg) (env : Env) (fuel : Nat) (rs : RS) : M RS := do
  scheduleDelayed env rs
  processDelayedLoop hooks env fuel rs

def processIncoming (hooks : NearCfg) (env : Env) (rs : RS) (incoming : List Rcpt) : M RS := do
  let decode ← pipeDecode
  modifyPipe (Pipeline.startList decode rs.o · incoming)
  incoming.foldlM (fun rs r => do
    if !validReceipt false r then throw (panicked "ReceiptValidationError on an incoming receipt")
    if rs.compute ≥ env.ctx.gasLimit || (← softExceeded) then logged (delayPushL rs r)
    else
      modifyPipe (Pipeline.stepList decode rs.o)
      processWithInstant hooks env rs r) rs

/-- `resolve_promise_yield_timeouts` (`lib.rs:2986-3088`); returns the state and the final
`first_index`. -/
def yieldLoop (env : Env) (next : Nat) : Nat → RS × Nat × Nat → M (RS × Nat)
  | 0, (rs, i, _) => pure (rs, i)
  | fuel + 1, (rs, i, k) => do
    if i ≥ next then return (rs, i)
    if rs.compute ≥ env.ctx.gasLimit || (← softExceeded) then return (rs, i)
    let (acct, d, exp) ← match ← getR rs.o (kYieldTimeout i) "promise yield timeout" with
      | none => throw (inconsistent "PromiseYield timeout queue entry should be in the state")
      | some b => okR (decodeYieldTimeout b) (inconsistent "promise yield timeout")
    if exp > env.ctx.height then return (rs, i)
    let (rs, k) ← if ← containsR rs.o (kYieldReceipt acct d) "promise yield receipt" then do
        let rid := receiptIdFrom d env.ctx.height k
        let rs ← forwardOrBufferR env rs ⟨acct, acct, rid, .data true d none⟩
        pure (rs, k + 1)
      else pure (rs, k)
    let rs := { rs with o := rs.o.remove (kYieldTimeout i) }
    yieldLoop env next fuel (rs, i + 1, k)

/-- Bandwidth scheduler through the overlay (`run_bandwidth_scheduler`, D0's `schedStep`). -/
def applyNewChunkD2 (hooks : NearCfg) (prims : Prims) (env : Env) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (lastProps : List (Bytes × Nat))
    (incoming : List Rcpt) (txs : List (TxD2 × Bool)) (ownCong : Congestion) :
    M MainOutD2 := do
  let ctx := env.ctx
  let o := Ovl.ofTrie t
  -- 1. validator accounts update
  let o ← match vu with
    | some f => validatorUpdateR ctx.layout ctx.own o f lastProps
    | none => pure o
  -- 2. delayed queue load
  let (df, dn) ← getIndicesR o kDelayedIdx "DelayedReceiptIndices"
  -- 3. bandwidth scheduler
  let (o, so) ← schedOvlR prims ctx o
  -- 4. receipt sink (indices and metadata read from the trie)
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
  let rs ← forwardFromBufferR env rs
  -- 5. transactions
  let (rs, _) ← txs.foldlM (processTxR env) (rs, [])
  -- 6. receipts: local, delayed, incoming
  let locals := rs.locals
  let rs ← processLocals hooks env { rs with locals := [] } locals
  let rs ← processDelayed hooks env (rs.dq.next - rs.dq.first + 1) rs
  let rs ← processIncoming hooks env rs incoming
  -- yield timeouts
  let (yf, yn) ← getIndicesR rs.o kYieldIdx "PromiseYieldIndices"
  let (rs, yf') ← yieldLoop env yn (yn - yf + 1) (rs, yf, 0)
  -- 7. validate_apply_state_update
  let rs := if yf' != yf then { rs with o := rs.o.set kYieldIdx (encIndices yf' yn) } else rs
  let cong ← liftE (applyDelayedCongestion rs.dq rs.cong)
  let allowed := ctx.layout.shardIds.getD ((ctx.height + (ctx.layout.index ctx.own).getD 0) % ctx.layout.numShards) ctx.own
  let cong := { cong with allowedShard := allowed }
  let bw ← bandwidthRequestsR env rs
  let o := rs.o.commit
  let root ← finalizeR o
  let gasUsed ← okR (sumNat64 (rs.outcomes.map (·.o.gasBurnt))) (panicked "total gas burnt overflow")
  let burnt ← okR (add128 rs.txBurnt rs.otherBurnt) (panicked "burnt balance overflow")
  -- E9: balance_burnt = tx + other (+ slashed = 0) − subsidized (rt/mod.rs:386-403); negative ⇒ Error
  if rs.subsidized > burnt then throw "invalid: balance_burnt underflow (subsidized exceeds burnt)"
  let burnt := burnt - rs.subsidized
  let recd ← get
  pure { root, outcomes := rs.outcomes, outgoing := rs.outgoing, gasUsed, balanceBurnt := burnt,
         congestion := cong, bwRequests := bw, proposals := dedupProposals rs.proposals,
         cdRemovals := o.cdRemovals, wasmGas := rs.wasmGas,
         committed := some (sortKV o.committed), compute := some rs.compute,
         detail := if recd.observe then some recd.detail else none }

/-- Execute the recorder-aware main transition. Limits are protocol constants; the initial
recorder is empty regardless of unused values included in the witness. -/
def run (cfg : NearCfg) (prims : Prims) (env : Env) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (props : List (Bytes × Nat))
    (incoming : List Rcpt) (txs : List (TxD2 × Bool)) (congestion : Congestion)
    (globalActions : Bool := false) (codePolicy : CodeWitnessPolicy := .coldPartial) :
    Except String MainOutD2 :=
  ((applyNewChunkD2 cfg prims env t vu props incoming txs congestion).run
    { globalActions, codePolicy, observe := cfg.observeDetail } env).map Prod.fst

end NearSpecV3.Successor.StorageExecution
