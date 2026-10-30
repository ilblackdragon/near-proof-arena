import NearSpecV3.Successor.TierProofs

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O1 — floats: preparation and execution

`NearCfg.floats` is read at exactly the three preparation guards (`floatGuardImport`,
`floatGuardGlobal`, `floatGuardBody`). This file proves the consequence at every layer:

* `earlyPass_floats` / `prepare_floats`: with floats switched on, preparation returns the same
  result, unless the float-free configuration reported `outOfDomain`;
* `run_floats`, `callEntry_floats`, `runCall_floats`, `runCallWithLimits_floats`: the interpreter
  never reads the flag;
* `functionCallD3_floats`: the D3 hook refines (`HooksRefine`).
-/

namespace NearSpecV3.Wasm

/-! ## Preparation -/

/-- `x` reports a float exclusion, or equals `y`, on every input. -/
def PRef {α : Type} (x y : PM α) : Prop :=
  ∀ s b n, x s b n = y s b n ∨ ∃ w, x s b n = .error (.ood w)

namespace PRef

theorem refl {α : Type} (x : PM α) : PRef x x := fun _ _ _ => Or.inl rfl

theorem bind_run {α β : Type} (x : PM α) (f : α → PM β) (s : PS) (b : ByteArray) (n : Nat) :
    (x >>= f) s b n = match x s b n with
      | .ok ((a, s'), n') => f a s' b n'
      | .error e => .error e := by
  show (StateT.bind x f) s b n = _
  simp only [StateT.bind, bind, ReaderT.bind, StateT.bind, Except.bind]
  rcases x s b n with e | ⟨⟨a, s'⟩, n'⟩ <;> rfl

theorem bind {α β : Type} {x y : PM α} {f g : α → PM β} (hx : PRef x y) (hf : ∀ a, PRef (f a) (g a)) :
    PRef (x >>= f) (y >>= g) := by
  intro s b n
  rw [bind_run, bind_run]
  rcases hx s b n with h | ⟨w, h⟩
  · rw [← h]
    rcases x s b n with e | ⟨⟨a, s'⟩, n'⟩
    · exact Or.inl rfl
    · exact hf a s' b n'
  · rw [h]; exact Or.inr ⟨w, rfl⟩

theorem throw_ood {α : Type} (w : String) (y : PM α) : PRef (throw (.ood w)) y :=
  fun _ _ _ => Or.inr ⟨w, rfl⟩

theorem throw_ood_bind {α β : Type} (w : String) (f : α → PM β) (y : PM β) :
    PRef (throw (.ood w) >>= f) y :=
  fun _ _ _ => Or.inr ⟨w, rfl⟩

theorem forIn_list {α σ : Type} (l : List α) (init : σ) {f g : α → σ → PM (ForInStep σ)}
    (h : ∀ a s, PRef (f a s) (g a s)) : PRef (forIn l init f) (forIn l init g) := by
  induction l generalizing init with
  | nil => exact refl _
  | cons a t ih =>
    simp only [List.forIn_cons]
    refine bind (h a init) fun r => ?_
    cases r with
    | done s => exact refl _
    | yield s => exact ih s

theorem forIn_array {α σ : Type} (l : Array α) (init : σ) {f g : α → σ → PM (ForInStep σ)}
    (h : ∀ a s, PRef (f a s) (g a s)) : PRef (forIn l init f) (forIn l init g) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact forIn_list _ _ h

theorem forIn_range {σ : Type} (r : Std.Legacy.Range) (init : σ) {f g : Nat → σ → PM (ForInStep σ)}
    (h : ∀ a s, PRef (f a s) (g a s)) : PRef (forIn r init f) (forIn r init g) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact forIn_list _ _ h

theorem ite_congr {β : Type} (c : Prop) [Decidable c] {t t' e e' : PM β}
    (ht : c → PRef t t') (he : ¬c → PRef e e') :
    PRef (if c then t else e) (if c then t' else e') := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact ht hc
  · simp only [hc, ite_false]; exact he hc

end PRef

theorem floatGuardImport_on (cfg : NearCfg) (ft : FuncType) :
    floatGuardImport { cfg with floats := true } ft = false := by simp [floatGuardImport]
theorem floatGuardGlobal_on (cfg : NearCfg) (gs : Array Global) :
    floatGuardGlobal { cfg with floats := true } gs = false := by simp [floatGuardGlobal]
theorem floatGuardBody_on (cfg : NearCfg) (groups : Array (Nat × VT)) (ft : FuncType) (code : Array Instr) :
    floatGuardBody { cfg with floats := true } groups ft code = false := by simp [floatGuardBody]

macro "pref_lockstep" : tactic => `(tactic|
  repeat (first
    | (with_reducible exact PRef.refl _)
    | (exact PRef.throw_ood _ _)
    | (exact PRef.throw_ood_bind _ _ _)
    | ((refine PRef.bind (PRef.forIn_list _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((refine PRef.bind (PRef.forIn_array _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((refine PRef.bind (PRef.forIn_range _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((refine PRef.bind (PRef.refl _) fun _ => ?_); try dsimp only)
    | (refine PRef.ite_congr _ (fun _ => ?_) (fun _ => ?_))
    | (exact PRef.refl _)
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only)))))

theorem sectionBody_floats (cfg : NearCfg) (id sEnd : Nat) :
    PRef (sectionBody cfg id sEnd) (sectionBody { cfg with floats := true } id sEnd) := by
  unfold sectionBody
  simp only [floatGuardImport_on, floatGuardGlobal_on, floatGuardBody_on, Bool.false_eq_true, ite_false]
  pref_lockstep

def earlyPassWith (sec : Nat → Nat → PM Unit) : PM Unit := do
  for x in [0x00, 0x61, 0x73, 0x6D] do
    if (← liftP byte) ≠ x then deser "magic header not detected"
  for x in [0x01, 0x00, 0x00, 0x00] do
    if (← liftP byte) ≠ x then deser "unknown binary version"
  let b ← readThe ByteArray
  for _ in [0:b.size] do
    if (← getThe Nat) ≥ b.size then break
    let id ← liftP byte
    let len ← liftP u32
    let st ← getThe Nat
    if st + len > b.size then
      -- wasmparser streams the code section: `CodeSectionStart { count }` is yielded (and NEAR's
      -- function budget checked, `prepare_v3.rs:225-230`) before the truncation is noticed
      if id = 10 then
        let n ← liftP u32
        if n > (← get).funcBudget then prepFail "TooManyFunctions" "code section count"
      deser "section size mismatch: unexpected end"
    if id ≠ 0 then
      match sectionRank id with
      | some r =>
        if r ≤ (← get).lastId then deser "section out of order"
        modify fun s => { s with lastId := r }
      | none => deser "malformed section id"
    if id = 4 ∨ id = 11 ∨ id = 12 then
      modify fun s => { s with m := { s.m with rawSizes := s.m.rawSizes.push (id, len) } }
    -- section payloads are parsed with a reader bounded to the section
    let sub := b.extract 0 (st + len)
    let r := ((sec id (st + len)).run (← get)).run sub |>.run st
    match r with
    | .ok ((_, s'), pos') =>
      set s'
      if pos' ≠ st + len then deser "section size mismatch"
      set (σ := Nat) pos'
    | .error e => throw e
  -- validator.end
  let s ← get
  if s.m.funcTypes.size > 0 ∧ !s.sawCode then deser "function and code section have inconsistent lengths"
  match s.m.dataCount with
  | some n => if n > 0 ∧ !s.sawData then deser "data count and data section have inconsistent lengths"
  | none => pure ()

theorem earlyPass_eq_with (cfg : NearCfg) : earlyPass cfg = earlyPassWith (sectionBody cfg) := rfl

theorem earlyPassWith_mono {sec sec' : Nat → Nat → PM Unit} (hs : ∀ i e, PRef (sec i e) (sec' i e)) :
    PRef (earlyPassWith sec) (earlyPassWith sec') := by
  unfold earlyPassWith
  repeat (first
    | (with_reducible exact PRef.refl _)
    | ((refine PRef.bind (PRef.forIn_list _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((refine PRef.bind (PRef.forIn_range _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((refine PRef.bind (by with_reducible exact PRef.refl _) fun _ => ?_); try dsimp only)
    | (refine PRef.ite_congr _ (fun _ => ?_) (fun _ => ?_))
    | (generalize h1 : ((StateT.run (sec _ _) _).run _).run _ = r1
       generalize h2 : ((StateT.run (sec' _ _) _).run _).run _ = r2
       have hrel : r1 = r2 ∨ ∃ w, r1 = .error (.ood w) := by
         subst h1 h2; exact hs _ _ _ _ _
       clear h1 h2
       rcases hrel with rfl | ⟨w, rfl⟩
       · exact PRef.refl _
       · exact PRef.throw_ood_bind _ _ _)
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only))))

theorem earlyPass_floats (cfg : NearCfg) :
    PRef (earlyPass cfg) (earlyPass { cfg with floats := true }) := by
  rw [earlyPass_eq_with, earlyPass_eq_with]
  exact earlyPassWith_mono (sectionBody_floats cfg)

/-- **Preparation.** Switching floats on changes preparation only where the float-free
configuration reported `outOfDomain`. -/
theorem prepare_floats (cfg : NearCfg) (code : ByteArray) (bl : Bool) :
    prepare cfg code bl = prepare { cfg with floats := true } code bl ∨
      ∃ w, prepare cfg code bl = .outOfDomain w := by
  rcases earlyPass_floats cfg { funcBudget := cfg.maxFunctions, localBudget := cfg.maxLocals } code 0
    with h | ⟨w, h⟩
  · left
    unfold prepare
    simp only [StateT.run, ReaderT.run]
    rw [h]
    rfl
  · right
    refine ⟨w, ?_⟩
    unfold prepare
    simp only [StateT.run, ReaderT.run]
    rw [h]

/-! ## Execution never reads the flag -/

theorem exec_floats (cfg : NearCfg) (b : Bool) (p : Prepared) (s : St) (f : Frame) (pf : PFunc)
    (i : Instr) : exec { cfg with floats := b } p s f pf i = exec cfg p s f pf i := rfl

theorem step_floats (cfg : NearCfg) (b : Bool) (p : Prepared) (s : St) :
    step { cfg with floats := b } p s = step cfg p s := rfl

theorem run_floats (cfg : NearCfg) (b : Bool) (p : Prepared) :
    ∀ n s, run { cfg with floats := b } p n s = run cfg p n s
  | 0, _ => rfl
  | n + 1, s => by simp only [run, step_floats, run_floats cfg b p n]

theorem callEntry_floats (cfg : NearCfg) (b : Bool) (p : Prepared) (fuel : Nat) (s : St) (fi : Nat) :
    callEntry { cfg with floats := b } p fuel s fi = callEntry cfg p fuel s fi := by
  unfold callEntry
  simp only [run_floats]

theorem instantiate_floats (cfg : NearCfg) (b : Bool) (p : Prepared) (g : Gas) :
    instantiate { cfg with floats := b } p g = instantiate cfg p g := rfl

theorem runCall_floats (cfg : NearCfg) (b : Bool) (code : ByteArray) (method : String) (ctx : CallCtx)
    (fuel : Nat) (bl full : Bool) (real : Option TTN.RealStore)
    (hp : prepare { cfg with floats := b } code bl = prepare cfg code bl) :
    runCall { cfg with floats := b } code method ctx fuel bl full real =
      runCall cfg code method ctx fuel bl full real := by
  unfold runCall
  rw [hp]
  simp only [callEntry_floats, instantiate_floats]

theorem runCallWithLimits_floats (cfg : NearCfg) (b : Bool) (code : ByteArray) (method : String)
    (ctx : CallCtx) (fuel : Nat) (bl full : Bool) (real : Option TTN.RealStore)
    (hp : prepare { cfg with floats := b } code bl = prepare cfg code bl) :
    runCallWithLimits { cfg with floats := b } code method ctx fuel bl full real =
      runCallWithLimits cfg code method ctx fuel bl full real := by
  unfold runCallWithLimits
  rw [hp, runCall_floats cfg b code method ctx fuel bl full real hp]

end NearSpecV3.Wasm

/-! ## The D3 hook, with its configuration-dependent calls abstracted

`D3.functionCall cfg` reads `cfg` at exactly three places: the Wasm step budget `wasmFuel cfg gas`
(since the UQ-010 fuel fix, 2026-10-29), and, on the same code blob, the domain check
`contractOOD cfg code` and the call `runCallWithLimits cfg code …`. `functionCallWith` is the
same body with those three as parameters; `functionCall_eq_with` is `rfl`, so the copy cannot
drift from the definition without breaking the build. -/

namespace NearSpecV3.D3
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Wasm

/-- `D3.functionCall` with its two configuration-dependent calls abstracted
(`functionCall_eq_with` is `rfl`). -/
def functionCallWith (fuelOf : Nat → Nat) (ood : ByteArray → Option String)
    (rc : ByteArray → String → CallCtx → Nat → TTN.RealStore → Run)
    (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) :
    Except String (ActSt × AR) := do
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
  let preHash : Option Bytes := match st.o.trie.find (nibbles (kAccount c.r.recv)) with
    | some (some raw) => match decodeAcct raw with
      | some x => match x.contract with | .local h0 => some h0 | _ => none
      | none => none
    | _ => none
  let code ← match env.codeOf hh with
    | some code => pure code
    | none =>
      if preHash == some hh then
        if (st.deploys ++ c.deployed ++ c.attempted).any (fun x => sha256 x == hh) then
          throw (oodE "pre-state contract served only by the in-chunk compiled-contract cache")
        else throw "invalid: MissingTrieValue (contract code)"
      else match codeAvailable c st hh with
        | some code => pure code
        | none => throw "invalid: MissingTrieValue (contract code)"
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
    accountContract := some (toBA hh) }
  -- trie-backed External over the merged witness values (§4.2, d3-trie-accounting.md)
  let pfx := TTN.contractDataPrefix ctx.currentAccount
  let ovl : TTN.BMap (Option ByteArray) :=
    (st.o.committed ++ st.o.prosp).foldl (fun m (k, v) =>
      m.insert (toBA k) (v.map toBA)) {}
  let real : TTN.RealStore := { store := fun hb => (env.codeOf (ofBA hb)).map toBA,
                                root := toBA env.preRoot, overlay := ovl, pfx }
  let fuel := fuelOf gas
  match rc codeB (strOf method) ctx fuel real with
  | .line l =>
    let (burnt, used) ← lineOutcome l
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
      -- `PromiseYieldIndices` is read on every successful call; each yield receipt enqueues a
      -- timeout `{account, data_id, expires_at = h + 200}` (§4.2.1–4, `fc.rs:154-222`)
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


theorem functionCall_eq_with (cfg : NearCfg) :
    functionCall cfg = functionCallWith (wasmFuel cfg) (contractOOD cfg)
      (fun code m ctx fuel real => runCallWithLimits cfg code m ctx fuel true false (some real)) := rfl

end NearSpecV3.D3

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Wasm

/-- Hook refinement, pointwise. -/
def HooksRefine (h h' : ActionHooks) : Prop :=
  ∀ c st r b, Refines (h.functionCall c st r b) (h'.functionCall c st r b)

theorem HooksRefine.refl (h : ActionHooks) : HooksRefine h h := fun _ _ _ _ => Refines.refl _

theorem HooksRefine.trans {a b c : ActionHooks} (h₁ : HooksRefine a b) (h₂ : HooksRefine b c) :
    HooksRefine a c := fun x y z w => Refines.trans (h₁ x y z w) (h₂ x y z w)

/-- Two instantiations of the hook's calls agree on a code blob, or the first excludes it. -/
def CallRel (ood ood' : ByteArray → Option String)
    (rc rc' : ByteArray → String → CallCtx → Nat → TTN.RealStore → Run) : Prop :=
  ∀ code, (ood code = ood' code ∧ ∀ m ctx fuel real, rc code m ctx fuel real = rc' code m ctx fuel real) ∨
    ∃ w, ood code = some w

theorem CallRel.step {ood ood' : ByteArray → Option String}
    {rc rc' : ByteArray → String → CallCtx → Nat → TTN.RealStore → Run} (h : CallRel ood ood' rc rc')
    {X : ByteArray} {o : Option String} (h1 : ood X = o) :
    (o = ood' X ∧ ∀ m ctx fuel real, rc' X m ctx fuel real = rc X m ctx fuel real) ∨ ∃ w, o = some w := by
  subst h1
  rcases h X with ⟨e1, e2⟩ | ⟨w, hw⟩
  · exact Or.inl ⟨e1, fun m ctx fuel real => (e2 m ctx fuel real).symm⟩
  · exact Or.inr ⟨w, hw⟩

theorem CallRel.none {ood ood' : ByteArray → Option String}
    {rc rc' : ByteArray → String → CallCtx → Nat → TTN.RealStore → Run} (h : CallRel ood ood' rc rc')
    {X : ByteArray} (hn : ∀ w, ood X = some w → False) :
    ood' X = ood X ∧ ∀ m ctx fuel real, rc' X m ctx fuel real = rc X m ctx fuel real := by
  rcases h X with ⟨e1, e2⟩ | ⟨w, hw⟩
  · exact ⟨e1.symm, fun m ctx fuel real => (e2 m ctx fuel real).symm⟩
  · exact (hn w hw).elim

theorem oodE_isExclusion (w : String) : isExclusion (D3.oodE w) = true := by
  unfold D3.oodE; ood_tac

theorem functionCallWith_mono {fuelOf : Nat → Nat} {ood ood' : ByteArray → Option String}
    {rc rc' : ByteArray → String → CallCtx → Nat → TTN.RealStore → Run} (h : CallRel ood ood' rc rc')
    (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) :
    Refines (D3.functionCallWith fuelOf ood rc c st ar b) (D3.functionCallWith fuelOf ood' rc' c st ar b) := by
  unfold D3.functionCallWith
  repeat (first
    | (with_reducible exact Refines.refl _)
    | (exact Refines.throw_bind _ _ _)
    | (exact Or.inr ⟨_, rfl, oodE_isExclusion _⟩)
    | (refine (fun (hx : _ ∧ _) => ?_) (CallRel.none h (by assumption)); obtain ⟨e1, e2⟩ := hx; simp only [e1, e2])
    | ((refine Refines.bind' (by with_reducible rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Refines.bind' (by with_reducible rfl) fun _ => ?_); try dsimp only)
    | (refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_))
    | ((refine Refines.bind (Refines.forIn_congr _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((refine Refines.bind' (by rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Refines.bind' (by rfl) fun _ => ?_); try dsimp only)
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only))))

theorem functionCall_mono {cfg cfg' : NearCfg}
    (h : CallRel (D3.contractOOD cfg) (D3.contractOOD cfg')
      (fun code m ctx fuel real => runCallWithLimits cfg code m ctx fuel true false (some real))
      (fun code m ctx fuel real => runCallWithLimits cfg' code m ctx fuel true false (some real)))
    (hf : wasmFuel cfg = wasmFuel cfg') (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) :
    Refines (D3.functionCall cfg c st ar b) (D3.functionCall cfg' c st ar b) := by
  rw [D3.functionCall_eq_with, D3.functionCall_eq_with, ← hf]
  exact functionCallWith_mono h c st ar b

/-- The `unmodeled` wrapper preserves refinement. -/
theorem functionCallD3_mono {cfg cfg' : NearCfg}
    (h : ∀ c st ar b, Refines (D3.functionCall cfg c st ar b) (D3.functionCall cfg' c st ar b)) :
    HooksRefine (D3.d3Hooks cfg) (D3.d3Hooks cfg') := by
  intro c st ar b
  show Refines (D3.functionCallD3 cfg c st ar b) (D3.functionCallD3 cfg' c st ar b)
  unfold D3.functionCallD3
  rcases h c st ar b with he | ⟨e, he, hx⟩
  · rw [he]; exact Refines.refl _
  · rw [he]
    dsimp only
    split
    · exact Or.inr ⟨_, rfl, oodE_isExclusion e⟩
    · exact Or.inr ⟨_, rfl, hx⟩

/-- **O1, call level.** Floats switched on: the domain check and the call agree on every code blob
the float-free configuration does not exclude. -/
theorem callRel_floats (cfg : NearCfg) :
    CallRel (D3.contractOOD cfg) (D3.contractOOD { cfg with floats := true })
      (fun code m ctx fuel real => runCallWithLimits cfg code m ctx fuel true false (some real))
      (fun code m ctx fuel real =>
        runCallWithLimits { cfg with floats := true } code m ctx fuel true false (some real)) := by
  intro code
  rcases prepare_floats cfg code true with hp | ⟨w, hp⟩
  · left
    refine ⟨?_, fun m ctx fuel real => ?_⟩
    · unfold D3.contractOOD; rw [hp]
    · exact (runCallWithLimits_floats cfg true code m ctx fuel true false (some real) hp.symm).symm
  · right
    refine ⟨w, ?_⟩
    unfold D3.contractOOD; rw [hp]

/-- **O1, hook level.** -/
theorem d3Hooks_floats (cfg : NearCfg) : HooksRefine (D3.d3Hooks cfg) (D3.d3Hooks { cfg with floats := true }) :=
  functionCallD3_mono (functionCall_mono (callRel_floats cfg) rfl)

end NearSpecV3.Successor
