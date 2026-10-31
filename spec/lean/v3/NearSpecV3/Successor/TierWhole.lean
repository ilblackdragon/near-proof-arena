import NearSpecV3.Successor.TierRefine

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 — the whole-state (recorder) engine is monotone in its call semantics

`StorageExecution` threads a `Recording` state through `M = StateT Recording (ReaderT Env
(Except String))`. `MRef x y`: from every state and environment, `x` refines `y` (`Refines` on the
result *and* the final state). The engine's functions take the Wasm configuration and read it only
in `functionCallRecorded`, at three places on one code blob: `contractOOD`, `wasmFuel` and
`runCallWithLimits`. `functionCallRecordedWith` abstracts them (`rfl`), `functionCallRecordedWith_mono`
relates two instantiations, and the walk below lifts that to `StorageExecution.run`
(`run_cfg_mono`), then to the recorder driver and the whole-state shells.

Application: floats on the whole-state engine (`Lift.floats_whole`).
-/

namespace NearSpecV3.Successor.StorageExecution
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged NearSpecV3.Wasm NearSpecV3.D3

/-- `functionCallRecordedF` with its configuration-dependent calls as parameters
(`functionCallRecorded_eq_with` is `rfl`). -/
def functionCallRecordedWith (ga : Bool)
    (res : List Bytes → List Bytes → List Bytes → PrestateCode → Bytes → Bool → Except String Bytes)
    (ood : ByteArray → Option String)
    (vm : ByteArray → String → CallCtx → TTN.RealStore → Except String Run)
    (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) : M (ActSt × AR) := do
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
  let timely := recording.pipe.deterministic c.r.rid c.idx hh
  let code ← liftE (res st.deploys (c.deployed ++ recording.materialized) c.attempted pre hh timely)
  let codeB := toBA code
  if let some why := ood codeB then throw (oodE why)
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
    accountContract := (NearSpecV3.Successor.StorageExecution.ctxContract acct.contract).1,
    accountContractTag := (NearSpecV3.Successor.StorageExecution.ctxContract acct.contract).2 }
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
  let vmr ← liftE (vm codeB (strOf method) ctx real)
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
    let (rs, idx, resumes) ← liftE ((if ga then managerGlobal else manager) s.actions ah h)
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
        let acts ← liftE ((if ga then finishActsGlobal else finishActs) m)
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

/-- The code resolution of the recorded call, its witness source fixed to the call's environment. -/
def resOf (fl : Flags) (c : ActCtx) :
    List Bytes → List Bytes → List Bytes → PrestateCode → Bytes → Bool → Except String Bytes :=
  fun current committed attempted pre hash timely =>
    resolveCodeBytes fl.codePolicy { witness := c.env.codeOf, current, committed, attempted } pre hash timely

theorem functionCallRecorded_eq_with (fl : Flags) (cfg : NearCfg) (c : ActCtx) :
    functionCallRecorded fl cfg c = functionCallRecordedWith fl.globalActions (resOf fl c) (contractOOD cfg)
      (fun code m ctx real => vmCall wasmFuel cfg code m ctx real) c := rfl

end NearSpecV3.Successor.StorageExecution

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Wasm StorageExecution

/-! ## `MRef`: refinement in the recorder monad -/

/-- From every recorder state and environment, `x` reports an exclusion or returns exactly what
`y` returns (value and final state). -/
def MRef {α : Type} (x y : StorageExecution.M α) : Prop := ∀ r env, Refines (x r env) (y r env)

namespace MRef

theorem refl {α : Type} (x : StorageExecution.M α) : MRef x x := fun _ _ => Refines.refl _

theorem trans {α : Type} {x y z : StorageExecution.M α} (h₁ : MRef x y) (h₂ : MRef y z) : MRef x z :=
  fun r env => Refines.trans (h₁ r env) (h₂ r env)

theorem bind_run {α β : Type} (x : StorageExecution.M α) (f : α → StorageExecution.M β) (r : Recording)
    (env : Env) : (x >>= f) r env = (x r env) >>= (fun p => f p.1 p.2 env) := by
  show (StateT.bind x f) r env = _
  simp only [StateT.bind, bind, ReaderT.bind, Except.bind]

theorem bind {α β : Type} {x y : StorageExecution.M α} {f g : α → StorageExecution.M β}
    (hx : MRef x y) (hf : ∀ a, MRef (f a) (g a)) : MRef (x >>= f) (y >>= g) := by
  intro r env
  rw [bind_run, bind_run]
  exact Refines.bind (hx r env) fun p => hf p.1 p.2 env

theorem throw_bind {α β : Type} (e : String) (he : isExclusion e = true)
    (f : α → StorageExecution.M β) (y : StorageExecution.M β) :
    MRef (throw e >>= f) y := fun _ _ => Or.inr ⟨e, rfl, he⟩

theorem throw_bind_same {α β : Type} (e : String) (f g : α → StorageExecution.M β) :
    MRef (throw e >>= f) (throw e >>= g) := fun _ _ => Or.inl rfl

theorem throw_ex {α : Type} (e : String) (he : isExclusion e = true) (y : StorageExecution.M α) :
    MRef (throw e) y := fun _ _ => Or.inr ⟨e, rfl, he⟩

theorem ite_congr {β : Type} (c : Prop) [Decidable c] {t t' e e' : StorageExecution.M β}
    (ht : c → MRef t t') (he : ¬c → MRef e e') :
    MRef (if c then t else e) (if c then t' else e') := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact ht hc
  · simp only [hc, ite_false]; exact he hc

theorem foldlM {α β : Type} (l : List β) (init : α)
    {f g : α → β → StorageExecution.M α} (h : ∀ a b, MRef (f a b) (g a b)) :
    MRef (l.foldlM f init) (l.foldlM g init) := by
  induction l generalizing init with
  | nil => exact refl _
  | cons x t ih =>
    simp only [List.foldlM_cons]
    exact bind (h init x) fun a => ih a

theorem forIn_list {α σ : Type} (l : List α) (init : σ)
    {f g : α → σ → StorageExecution.M (ForInStep σ)} (h : ∀ a s, MRef (f a s) (g a s)) :
    MRef (forIn l init f) (forIn l init g) := by
  induction l generalizing init with
  | nil => exact refl _
  | cons a t ih =>
    simp only [List.forIn_cons]
    refine bind (h a init) fun r => ?_
    cases r with
    | done s => exact refl _
    | yield s => exact ih s

theorem forIn_array {α σ : Type} (l : Array α) (init : σ)
    {f g : α → σ → StorageExecution.M (ForInStep σ)} (h : ∀ a s, MRef (f a s) (g a s)) :
    MRef (forIn l init f) (forIn l init g) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact forIn_list _ _ h

theorem mapM {α β : Type} (l : List α) {f g : α → StorageExecution.M β} (h : ∀ a, MRef (f a) (g a)) :
    MRef (l.mapM f) (l.mapM g) := by
  induction l with
  | nil => exact refl _
  | cons a t ih =>
    simp only [List.mapM_cons]
    exact bind (h a) fun b => bind ih fun _ => refl _

/-- `try x catch e => H e`, when the handler keeps every exclusion an exclusion. -/
theorem tryCatch {α : Type} {x y : StorageExecution.M α} (H : String → StorageExecution.M α)
    (hx : MRef x y)
    (hH : ∀ e, isExclusion e = true → ∀ r env, ∃ e', H e r env = .error e' ∧ isExclusion e' = true) :
    MRef (MonadExcept.tryCatch x H) (MonadExcept.tryCatch y H) := by
  intro r env
  have hl : (MonadExcept.tryCatch x H : StorageExecution.M α) r env =
      Except.tryCatch (x r env) (fun e => H e r env) := rfl
  have hr : (MonadExcept.tryCatch y H : StorageExecution.M α) r env =
      Except.tryCatch (y r env) (fun e => H e r env) := rfl
  rw [hl, hr]
  rcases hx r env with h | ⟨e, he, hex⟩
  · rw [h]; exact Refines.refl _
  · rw [he]
    obtain ⟨e', h', hx'⟩ := hH e hex r env
    exact Or.inr ⟨e', h', hx'⟩

end MRef

end NearSpecV3.Successor

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Wasm StorageExecution

/-! ## The recorded call -/

/-- Two instantiations of the recorded call's configuration-dependent calls agree on a code blob, or
the first excludes it. -/
def VmRel (ood ood' : ByteArray → Option String)
    (vm vm' : ByteArray → String → CallCtx → TTN.RealStore → Except String Run) : Prop :=
  ∀ code, (ood code = ood' code ∧ ∀ m ctx real, vm code m ctx real = vm' code m ctx real) ∨
    ∃ w, ood code = some w

theorem VmRel.none {ood ood' : ByteArray → Option String}
    {vm vm' : ByteArray → String → CallCtx → TTN.RealStore → Except String Run} (h : VmRel ood ood' vm vm')
    {X : ByteArray} (hn : ∀ w, ood X = some w → False) :
    ood' X = ood X ∧ ∀ m ctx real, vm' X m ctx real = vm X m ctx real := by
  rcases h X with ⟨e1, e2⟩ | ⟨w, hw⟩
  · exact ⟨e1.symm, fun m ctx real => (e2 m ctx real).symm⟩
  · exact (hn w hw).elim

theorem functionCallRecordedWith_mono (ga : Bool)
    (res : List Bytes → List Bytes → List Bytes → PrestateCode → Bytes → Bool → Except String Bytes)
    {ood ood' : ByteArray → Option String}
    {vm vm' : ByteArray → String → CallCtx → TTN.RealStore → Except String Run} (h : VmRel ood ood' vm vm')
    (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) :
    MRef (functionCallRecordedWith ga res ood vm c st ar b) (functionCallRecordedWith ga res ood' vm' c st ar b) := by
  unfold functionCallRecordedWith
  repeat (first
    | (with_reducible exact MRef.refl _)
    | (exact fun _ _ => Or.inr ⟨_, rfl, oodE_isExclusion _⟩)
    | (refine (fun (hx : _ ∧ _) => ?_) (VmRel.none h (by assumption)); obtain ⟨e1, e2⟩ := hx;
       simp only [e1, e2])
    | ((refine MRef.bind (by with_reducible exact MRef.refl _) fun (_, _) => ?_); try dsimp only)
    | ((refine MRef.bind (by with_reducible exact MRef.refl _) fun _ => ?_); try dsimp only)
    | (refine MRef.ite_congr _ (fun _ => ?_) (fun _ => ?_))
    | ((refine MRef.bind (MRef.forIn_array _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((refine MRef.bind (MRef.forIn_list _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((refine MRef.bind (MRef.mapM _ fun _ => ?_) fun _ => ?_); try dsimp only)
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only))))
  all_goals exact MRef.refl _

/-- The hypothesis every walk lemma below carries: the two runs' recorded calls refine, on every
call whose environment satisfies `P`. The two runs share `globalActions` (`ga`) and may differ in
the Wasm configuration and the code policy. -/
def RecRefine (P : Env → Prop) (ga : Bool) (p : CodeWitnessPolicy) (cfg : NearCfg)
    (p' : CodeWitnessPolicy) (cfg' : NearCfg) : Prop :=
  ∀ c st ar b, P c.env →
    MRef (functionCallRecorded ⟨ga, p⟩ cfg c st ar b) (functionCallRecorded ⟨ga, p'⟩ cfg' c st ar b)

theorem recRefine_of_vmRel {cfg cfg' : NearCfg} (P : Env → Prop) (ga : Bool) (p : CodeWitnessPolicy)
    (h : VmRel (D3.contractOOD cfg) (D3.contractOOD cfg')
      (fun code m ctx real => vmCall wasmFuel cfg code m ctx real)
      (fun code m ctx real => vmCall wasmFuel cfg' code m ctx real)) :
    RecRefine P ga p cfg p cfg' := by
  intro c st ar b _
  rw [functionCallRecorded_eq_with, functionCallRecorded_eq_with]
  exact functionCallRecordedWith_mono ga _ h c st ar b

end NearSpecV3.Successor
