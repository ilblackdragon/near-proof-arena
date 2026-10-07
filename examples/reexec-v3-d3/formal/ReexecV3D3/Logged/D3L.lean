import ReexecV3D3.Logged.Runtime.D2Check
import ReexecV3D3.Logged.Runtime.WasmRun
import NearSpecV3.D3.FunctionCall

/-!
# The D3 `FunctionCall` hook with every recorded-storage read logged

`functionCallL` is `D3.functionCall` in `LM`: the pre-state contract lookup goes through the lazy trie
(`trieFindL`), code blobs through `LM.getB`, and the WASM call through `W.runCallL` (its trie store is
read through `SM.get'`; the machine states carry no store). `checkD3L` is `checkD3` on these hooks.
-/

namespace NearSpecV3.D3

open NearSpec NearSpecV3 NearSpecV3.D2 ReexecV3D3.Logged NearSpecV3.Wasm

/-- `codeAvailable` with the recorded-storage lookup through `LM.getB`. -/
def codeAvailableL (c : ActCtx) (st : ActSt) (h : Bytes) : LM (Option Bytes) :=
  match (st.deploys ++ c.deployed).find? (fun code => sha256 code == h) with
  | some code => pure (some code)
  | none => LM.getB h

def functionCallL (cfg : NearCfg) (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) :
    LM (ActSt × AR) := do
  let .fcall method args gas deposit := b | throw "unmodeled: functionCall hook on a non-FunctionCall"
  let some acct := st.account | throw "invalid: EXPECT_ACCOUNT_EXISTS"
  -- ETH-implicit accounts with a local contract may resolve to the legacy-wallet global contract
  -- (`contract_code.rs:56-76`); conservatively out of domain (§10.0 P5)
  if AccountId.isEthImplicit c.r.recv then
    match acct.contract with
    | .local _ => throw (oodE "ETH-implicit account with a local contract (legacy wallet resolution)")
    | _ => pure ()
  let env := c.env
  let h := env.ctx.height
  if acct.amount + deposit ≥ 2 ^ 128 then
    throw "invalid: StorageInconsistentState (account balance overflow on deposit)"
  -- code (§2)
  let codeHash ← match acct.contract with
    | .none => pure none
    | .local hh => pure (some hh)
    | _ => throw "out of domain (w.shape): global contract identifier"
  match codeHash with
  | none =>
    -- CodeDoesNotExist: 0 VM gas, action failure
    pure (st, ar.fail)
  | some hh =>
  -- Code (§2.2, cold-cache rule). A blob in the merged witness store always serves. Otherwise:
  -- for the account's *pre-state* contract (nearcore's "contract access", `fc.rs:355-393`) the
  -- verdict depends on the compiled-contract cache and the preparation pipeline (an in-chunk
  -- deploy of the same code, even rolled back, precompiles it; pipelined receipts are prepared
  -- before such a deploy runs): out of domain if that code was deployed in this chunk, else
  -- nearcore's `MissingTrieValue`. A contract set by a deploy in this chunk comes from the deploy
  -- tracker (`contract.rs:42-69`).
  let fr ← trieFindL (kAccount c.r.recv)
  let preHash : Option Bytes := match fr with
    | some (some raw) => match decodeAcct raw with
      | some x => match x.contract with | .local h0 => some h0 | _ => none
      | none => none
    | _ => none
  let code ← match ← LM.getB hh with
    | some code => pure code
    | none =>
      if preHash == some hh then
        if (st.deploys ++ c.deployed ++ c.attempted).any (fun x => sha256 x == hh) then
          throw (oodE "pre-state contract served only by the in-chunk compiled-contract cache")
        else throw "invalid: MissingTrieValue (contract code)"
      else match ← codeAvailableL c st hh with
        | some code => pure code
        | none => throw "invalid: MissingTrieValue (contract code)"
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
  let ovl : Std.HashMap ByteArray (Option ByteArray) :=
    (st.o.committed ++ st.o.prosp).foldl (fun m (k, v) =>
      m.insert (toBA k) (v.map toBA)) {}
  let real : TTN.RealStore := { store := W.dummy, root := toBA env.preRoot, overlay := ovl, pfx }
  let fuel := (gas / pv86.regularOpCost + 2) * 64 + 1000000
  match ← LM.lift (W.runCallL cfg codeB (strOf method) ctx fuel true false (W.dr real)) with
  | .line l =>
    let (burnt, used) ← liftE (lineOutcome l)
    let gb := ar.gasBurnt + burnt
    pure (st, { ar.fail with gasBurnt := gb, gasFC := ar.gasFC + burnt, gasUsed := ar.gasUsed + used })
  | .done s err =>
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
    let (rs, idx, resumes) ← liftE (manager s.actions ah h)
    let (rs, extra) ← liftE (distribute rs gas s.gas.used)
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
      -- `PromiseYieldIndices` is read on every successful call; each yield receipt enqueues a
      -- timeout `{account, data_id, expires_at = h + 200}` (§4.2.1–4, `fc.rs:154-222`)
      let (yf, yn) ← st.o.getIndicesL kYieldIdx "PromiseYieldIndices"
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
        let acts ← liftE (finishActs m)
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

def functionCallD3L (cfg : NearCfg) (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) : LM (ActSt × AR) :=
  tryCatch (functionCallL cfg c st ar b) (fun e => throw (if e.startsWith "unmodeled" then oodE e else e))

def d3HooksL (cfg : NearCfg) : ActionHooksL where
  functionCall := functionCallD3L cfg

end NearSpecV3.D3
