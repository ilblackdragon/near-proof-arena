import NearSpecV3.Successor.TierO4X

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O4 — the `NS` simulation and the final O4 theorem (README §14)

The legacy engine (`D2.applyNewChunkD2 (D3.d3Hooks cfg)`) is simulated by the proof-side recorder
copy `NS` (`TierO4NS.lean`) up to the named escapes (`SimX`), with the trivial recorder invariant
`P := True`: `NS` has no soft-limit test, so neither `soft` nor `RemClosed` is needed (§13).

* **The `FunctionCall` hook (`FCSim`, walked here).** `functionCall_nf` puts the legacy hook in a
  normal form (`fcLegNF`); `code_rel` relates the legacy code selection to `resolveColdCodeNS` (G3
  race and G3b rolled-back-deploy code are escapes; an in-chunk-deploy-served pre-state contract is
  a legacy exclusion); `tail_rel` relates the legacy VM tail to `callTailNS` (G2 certificate is an
  escape; the VM store is the legacy fresh one, G6 being the `NS` premise).
* **G5 is unreachable**: `Rci.resolve` redirects a local contract to the global wallet only on an
  ETH-implicit account (`resolve_local_nonEth`), and the legacy hook excludes every ETH-implicit
  account with a local contract before resolving code. So no value reaches the legacy
  `MissingTrieValue` against a recorder redirection.
* **G7** is an escape: `applyGlobal false` fails with `escG7` at once.
* **G4**: on a V2 layout forwarding is `fwdSim_v2`; on a V3 layout `fwdSimX_v3` proves the recorder's
  `forwardFromBufferV3L` against the legacy `forwardFromBuffer`: a non-empty buffer outside the
  layout is a legacy exclusion, an empty parent buffer forwards nothing, and the final empty-buffer
  assertion is the escape `escG4`.

The final theorem `relSuccessor_runtimeLimits_storageResolution` needs only two premises, both on
the witness: `Tier.checker .storageResolution c w = checkNS c w` (G1, G6) and "the
storage-resolution result is not an `esc` string" (G2, G3, G3b, G4, G7). `o4_premises_nonvacuous`
exhibits a witness on which both hold.
-/

namespace NearSpecV3.Successor.O4E
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged
open NearSpecV3.Successor
open NearSpecV3.Successor.StorageExecution (M Recording)
open NearSpecV3.Wasm NearSpecV3.D3

/-! ## The legacy hook in normal form -/

def legacyCode (c : ActCtx) (st : ActSt) (hh : Bytes) : Except String Bytes :=
  match c.env.codeOf hh with
  | some code => pure code
  | none =>
    if StorageExecutionNS.preHashOf st.o c.r.recv == some hh then
      if (st.deploys ++ c.deployed ++ c.attempted).any (fun x => sha256 x == hh) then
        throw (oodE "pre-state contract served only by the in-chunk compiled-contract cache")
      else throw "invalid: MissingTrieValue (contract code)"
    else match codeAvailable c st hh with
      | some code => pure code
      | none => throw "invalid: MissingTrieValue (contract code)"

def callTailLeg (cfg : NearCfg) (c : ActCtx) (st : ActSt) (ar : AR) (method args : Bytes) (gas deposit : Nat)
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
    accountContract := (NearSpecV3.Successor.StorageExecution.ctxContract acct.contract).1,
    accountContractTag := (NearSpecV3.Successor.StorageExecution.ctxContract acct.contract).2 }
  let pfx := TTN.contractDataPrefix ctx.currentAccount
  let ovl : TTN.BMap (Option ByteArray) :=
    (st.o.committed ++ st.o.prosp).foldl (fun m (k, v) =>
      m.insert (toBA k) (v.map toBA)) {}
  let real : TTN.RealStore := { store := fun hb => (env.codeOf (ofBA hb)).map toBA,
                                root := toBA env.preRoot, overlay := ovl, pfx }
  let fuel := wasmFuel cfg gas
  match runCallWithLimits cfg codeB (strOf method) ctx fuel true false (some real) with
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

def isLocalC : Contract → Bool
  | .local _ => true
  | _ => false

def legacyLocal (cfg : NearCfg) (c : ActCtx) (st : ActSt) (ar : AR) (m args : Bytes) (g d : Nat)
    (acct : D2.Acct) (hh : Bytes) : Except String (ActSt × AR) :=
  match c.env.codeOf hh with
  | some code => callTailLeg cfg c st ar m args g d acct hh code
  | none =>
    if StorageExecutionNS.preHashOf st.o c.r.recv == some hh then
      if (st.deploys ++ c.deployed ++ c.attempted).any (fun x => sha256 x == hh) then
        throw (oodE "pre-state contract served only by the in-chunk compiled-contract cache")
      else throw "invalid: MissingTrieValue (contract code)"
    else match codeAvailable c st hh with
      | some code => callTailLeg cfg c st ar m args g d acct hh code
      | none => throw "invalid: MissingTrieValue (contract code)"

def fcLegNF (cfg : NearCfg) (c : ActCtx) (st : ActSt) (ar : AR) (m args : Bytes) (g d : Nat) :
    Except String (ActSt × AR) :=
  match st.account with
  | none => throw "invalid: EXPECT_ACCOUNT_EXISTS"
  | some acct =>
    if AccountId.isEthImplicit c.r.recv && isLocalC acct.contract then
      throw (oodE "ETH-implicit account with a local contract (legacy wallet resolution)")
    else if acct.amount + d ≥ 2 ^ 128 then
      throw "invalid: StorageInconsistentState (account balance overflow on deposit)"
    else match acct.contract with
      | .none => pure (st, ar.fail)
      | .local hh => legacyLocal cfg c st ar m args g d acct hh
      | _ => throw "out of domain (w.shape): global contract identifier"

theorem legacyLocal_eq (cfg : NearCfg) (c : ActCtx) (st : ActSt) (ar : AR) (m args : Bytes) (g d : Nat)
    (acct : D2.Acct) (hh : Bytes) :
    legacyLocal cfg c st ar m args g d acct hh = legacyCode c st hh >>= callTailLeg cfg c st ar m args g d acct hh := by
  unfold legacyLocal legacyCode
  split
  · rfl
  · split
    · split <;> rfl
    · split <;> rfl

set_option maxHeartbeats 4000000 in
theorem functionCall_nf (cfg : NearCfg) (c : ActCtx) (st : ActSt) (ar : AR) (m args : Bytes) (g d : Nat) :
    D3.functionCall cfg c st ar (.fcall m args g d) = fcLegNF cfg c st ar m args g d := by
  unfold D3.functionCall fcLegNF
  rcases st with ⟨o, account, actor, deploys⟩
  cases account with
  | none => rfl
  | some acct =>
    rcases acct with ⟨amount, locked, usage, contract, v2⟩
    dsimp only
    cases contract <;> cases heth : AccountId.isEthImplicit c.r.recv <;>
      simp only [heth, isLocalC, Bool.true_and, Bool.false_and, Bool.and_false, Bool.and_true,
        Bool.false_eq_true, ↓reduceIte] <;>
      (by_cases hov : amount + d ≥ 2 ^ 128 <;> simp only [hov, ↓reduceIte]) <;> rfl

/-! ## Code selection and the VM tail -/

theorem esc_escG2 : esc escG2 = true := by simp [esc]
theorem esc_race : esc raceExclusion = true := by simp [esc]
theorem esc_att : esc StorageExecutionNS.attemptedOnlyExclusion = true := by simp [esc]
theorem esc_escG7 : esc escG7 = true := by simp [esc]
theorem esc_escG4 : esc escG4 = true := by simp [esc]

theorem find?_append_eq {α : Type} (p : α → Bool) (l₁ l₂ : List α) :
    (l₁ ++ l₂).find? p = match l₁.find? p with | some a => some a | none => l₂.find? p := by
  rw [List.find?_append]; cases l₁.find? p <;> rfl

theorem any_eq_find? {α : Type} (p : α → Bool) (l : List α) : l.any p = (l.find? p).isSome := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.any_cons, List.find?_cons]; cases p a <;> simp [ih]

/-- **Code selection (G3, G3b).** The legacy selection and `resolveColdCodeNS` agree, or the legacy
one excludes, or `NS` fails with the race (G3) or the rolled-back-deploy exclusion (G3b). -/
theorem code_rel (c : ActCtx) (st : ActSt) (hh : Bytes) (timely : Bool) :
    RelE (legacyCode c st hh)
      (StorageExecutionNS.resolveColdCodeNS (⟨c.env.codeOf, st.deploys, c.deployed, c.attempted⟩ : CodeSources)
        timely (StorageExecutionNS.preHashOf st.o c.r.recv == some hh) hh) := by
  unfold legacyCode StorageExecutionNS.resolveColdCodeNS
  dsimp only
  cases hw : c.env.codeOf hh with
  | some code => exact Or.inl rfl
  | none =>
    simp only []
    rw [find?_append_eq]
    by_cases hp : (StorageExecutionNS.preHashOf st.o c.r.recv == some hh) = true
    · simp only [hp, ↓reduceIte]
      rw [any_eq_find?, find?_append_eq, find?_append_eq]
      cases h1 : st.deploys.find? (fun x => sha256 x == hh) with
      | some x => exact Or.inr (Or.inl ⟨_, rfl, by ood_tac⟩)
      | none =>
        cases h2 : c.deployed.find? (fun x => sha256 x == hh) with
        | some x => exact Or.inr (Or.inl ⟨_, rfl, by ood_tac⟩)
        | none =>
          cases h3 : c.attempted.find? (fun x => sha256 x == hh) with
          | some x => exact Or.inr (Or.inl ⟨_, rfl, by ood_tac⟩)
          | none => exact Or.inl rfl
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      unfold codeAvailable
      rw [find?_append_eq]
      cases h1 : st.deploys.find? (fun x => sha256 x == hh) with
      | some x => exact Or.inl rfl
      | none =>
        cases h2 : c.deployed.find? (fun x => sha256 x == hh) with
        | some x =>
          cases timely
          · exact Or.inr (Or.inr ⟨_, esc_race, rfl⟩)
          · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.isNone_some, Bool.and_false]
            exact Or.inl rfl
        | none =>
          simp only [hw]
          cases h3 : c.attempted.find? (fun x => sha256 x == hh) with
          | some x =>
            cases timely
            · exact Or.inr (Or.inr ⟨_, esc_race, rfl⟩)
            · simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.isNone_none,
                Bool.not_false, Bool.and_self]
              exact Or.inr (Or.inr ⟨_, esc_att, rfl⟩)
          | none => exact Or.inl rfl

/-- **The VM tail (G2).** The legacy tail and `callTailNS` agree, or `NS` fails the certificate. -/
theorem tail_rel (cfg : NearCfg) (c : ActCtx) (st : ActSt) (ar : AR) (m args : Bytes) (g d : Nat)
    (acct : D2.Acct) (hh code : Bytes) :
    RelE (callTailLeg cfg c st ar m args g d acct hh code)
      (StorageExecutionNS.callTailNS cfg c st ar m args g d acct hh code) := by
  unfold callTailLeg StorageExecutionNS.callTailNS
  dsimp only
  cases hood : contractOOD cfg (toBA code) with
  | some why => exact Or.inl rfl
  | none =>
    simp only []
    cases hc : fuelCertified cfg (toBA code)
    · refine Or.inr (Or.inr ⟨escG2, esc_escG2, ?_⟩)
      simp only [StorageExecution.vmCall, hc, Bool.not_false, ↓reduceIte]
      rfl
    · simp only [StorageExecution.vmCall, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact Or.inl rfl

/-- **G5 is unreachable** (module comment): a local contract of a non-ETH-implicit account resolves
to itself. -/
theorem resolve_local_nonEth (chainId acct h : Bytes) (he : AccountId.isEthImplicit acct = false) :
    D3.L4.Rci.resolve chainId acct (.local h) = .accountLocal h acct := by
  simp [D3.L4.Rci.resolve, he]

/-! ## The `FunctionCall` hook -/

section fc
variable {e : Env} {P : Recording → Prop}

theorem SimX.err_run {α β : Type} {φ : β → α} {err : String} {y : M β}
    (hy : ∀ r, y.run r e = .error err) : SimX e P φ (Except.error err : Except String α) y :=
  fun r _ => Or.inl (Or.inr (hy r))

theorem SimX.excl' {α β : Type} {φ : β → α} {y : M β} (err : String) (he : isExclusion err = true) :
    SimX e P φ (Except.error err : Except String α) y := SimX.of (Sim.excl err he)

theorem SimX.esc_run {α β : Type} {φ : β → α} {x : Except String α} {y : M β} (s : String)
    (hs : esc s = true) (hy : ∀ r, y.run r e = .error s) : SimX e P φ x y :=
  fun r _ => Or.inr ⟨s, hs, hy r⟩

/-- The hook at the identity value map: both sides run on the state with the revealed trie. -/
theorem simx_functionCall (cfg : NearCfg) (c : ActCtx) (st0 : ActSt) (res : AR) (m args : Bytes) (g d : Nat)
    (hc : c.env = e) :
    SimX e P id (D3.functionCall cfg c (st0.wt (T e)) res (.fcall m args g d))
      (StorageExecutionNS.functionCallNS cfg c st0 res (.fcall m args g d)) := by
  subst hc
  rw [functionCall_nf]
  unfold fcLegNF StorageExecutionNS.functionCallNS
  rcases st0 with ⟨o, account, actor, deploys⟩
  cases account with
  | none => exact SimX.err_run fun _ => rfl
  | some acct =>
    rcases acct with ⟨amount, locked, usage, contract, v2⟩
    dsimp only
    cases contract with
    | none =>
      simp only [isLocalC, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      by_cases hov : amount + d ≥ 2 ^ 128
      · simp only [hov, ↓reduceIte]; exact SimX.err_run fun _ => rfl
      · simp only [hov, ↓reduceIte]
        exact SimX.of (fun r hr => ⟨_, r, rfl, rfl, hr⟩)
    | «local» h =>
      cases heth : AccountId.isEthImplicit c.r.recv
      · simp only [isLocalC, heth, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        by_cases hov : amount + d ≥ 2 ^ 128
        · simp only [hov, ↓reduceIte]; exact SimX.err_run fun _ => rfl
        · simp only [hov, ↓reduceIte]
          rw [legacyLocal_eq]
          have hres : StorageExecution.resolveCode c
              ⟨o.wt (T c.env), some ⟨amount, locked, usage, .local h, v2⟩, actor, deploys⟩
              ⟨amount, locked, usage, .local h, v2⟩ = pure (some h, kCode c.r.recv) := by
            unfold StorageExecution.resolveCode
            rw [resolve_local_nonEth _ _ _ heth]
          rw [hres, pure_bind]
          dsimp only
          refine SimX.get_all fun r0 => ?_
          refine SimX.bind_id (SimX.liftE_rel (code_rel c _ h _)) fun code => ?_
          exact SimX.liftE_rel (tail_rel cfg c _ res m args g d _ h code)
      · simp only [isLocalC, heth, Bool.and_self, ↓reduceIte]
        exact SimX.excl' _ (by ood_tac)
    | «global» h =>
      simp only [isLocalC, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      by_cases hov : amount + d ≥ 2 ^ 128
      · simp only [hov, ↓reduceIte]; exact SimX.err_run fun _ => rfl
      · simp only [hov, ↓reduceIte]; exact SimX.excl' _ (by ood_tac)
    | byAccount id =>
      simp only [isLocalC, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      by_cases hov : amount + d ≥ 2 ^ 128
      · simp only [hov, ↓reduceIte]; exact SimX.err_run fun _ => rfl
      · simp only [hov, ↓reduceIte]; exact SimX.excl' _ (by ood_tac)

end fc

/-! ## The hook wrapper (`unmodeled` → exclusion) and the value map -/

/-- The legacy wrapper `D3.functionCallD3` on a result. -/
def mapUnmodeled {α : Type} (x : Except String α) : Except String α :=
  match x with
  | .error e => if e.startsWith "unmodeled" then .error (oodE e) else .error e
  | r => r

theorem functionCallD3_eq (cfg : NearCfg) (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) :
    D3.functionCallD3 cfg c st ar b = mapUnmodeled (D3.functionCall cfg c st ar b) := by
  unfold D3.functionCallD3 mapUnmodeled; cases D3.functionCall cfg c st ar b <;> rfl

theorem esc_not_unmodeled {s : String} (hs : esc s = true) : s.startsWith "unmodeled" = false := by
  unfold esc at hs
  simp only [Bool.or_eq_true, beq_iff_eq] at hs
  rcases hs with (((h | h) | h) | h) | h <;> subst h <;> with_unfolding_all decide

theorem isExclusion_oodE (x : String) : isExclusion (oodE x) = true := by
  unfold oodE; ood_tac

section hook
variable {e : Env} {P : Recording → Prop}

theorem run_tryCatch {β : Type} (y : M β) (h : String → M β) (r : Recording) :
    (tryCatch y h : M β).run r e = Except.tryCatch (y.run r e) (fun err => (h err).run r e) := rfl

/-- The hook wrapper on both sides, and the value map: a legacy hook value is a fixed point of the
map (`HooksR_d3`), so the identity-map simulation of the hook gives the `ActSim` one. -/
theorem simx_hook {x : Except String (ActSt × AR)} {y : M (ActSt × AR)}
    {φ : ActSt × AR → ActSt × AR} (h : SimX e P id x y)
    (hid : ∀ a, mapUnmodeled x = .ok a → a = φ a) :
    SimX e P φ (mapUnmodeled x)
      (try y catch err => throw (if err.startsWith "unmodeled" then oodE err else err) : M (ActSt × AR)) := by
  intro r hr
  have ht : (try y catch err => throw (if err.startsWith "unmodeled" then oodE err else err) :
      M (ActSt × AR)).run r e = Except.tryCatch (y.run r e)
        (fun err => .error (if err.startsWith "unmodeled" then oodE err else err)) := rfl
  rcases h r hr with h1 | ⟨s, hs, hy⟩
  · unfold SimAt at h1
    cases hx : x with
    | ok a =>
      rw [hx] at h1
      obtain ⟨b0, r', hyb, hab, hr'⟩ := h1
      have hb0 : a = b0 := hab
      refine Or.inl ⟨b0, r', ht.trans (by rw [hyb]; rfl), ?_, hr'⟩
      rw [hb0]
      exact hid b0 (by rw [hx, hb0]; rfl)
    | error err =>
      rw [hx] at h1
      refine Or.inl ?_
      unfold SimAt mapUnmodeled
      cases hu : err.startsWith "unmodeled"
      · simp only [hu, Bool.false_eq_true, ↓reduceIte]
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (ht.trans (by rw [h1]; simp [Except.tryCatch, hu]))
      · simp only [hu, ↓reduceIte]
        rcases h1 with h1 | h1
        · exact Or.inl (isExclusion_oodE err)
        · exact Or.inr (ht.trans (by rw [h1]; simp [Except.tryCatch, hu]))
  · exact Or.inr ⟨s, hs, ht.trans (by rw [hy]; simp [Except.tryCatch, esc_not_unmodeled hs])⟩

/-- **`FCSim` for `NS`.** -/
theorem fcSimNS (cfg : NearCfg) (c : ActCtx) (st : ActSt) (res : AR) (m args : Bytes) (g d : Nat)
    (hc : c.env = e) :
    SimX e P (fun p => (p.1.wt (T e), p.2)) (D3.functionCallD3 cfg c (st.wt (T e)) res (.fcall m args g d))
      (try StorageExecutionNS.functionCallNS cfg c st res (.fcall m args g d)
       catch err => throw (if err.startsWith "unmodeled" then oodE err else err) : M (ActSt × AR)) := by
  rw [functionCallD3_eq]
  refine simx_hook (simx_functionCall cfg c st res m args g d hc) fun a ha => ?_
  have hR := HooksR_d3 (s := e.store) (root := e.preRoot) cfg c st res (.fcall m args g d)
  rw [actCtx_ws hc] at hR
  unfold R at hR
  rw [← functionCallD3_eq] at ha
  change D3.functionCallD3 cfg c (st.wt (T e)) res (.fcall m args g d) = _ at hR
  rw [hR] at ha
  cases hev : LM.ev e.store e.preRoot ((D3.d3HooksL cfg).functionCall c st res (.fcall m args g d)) with
  | error err => rw [hev] at ha; cases ha
  | ok q => rw [hev] at ha; cases ha; rfl

end hook

/-! ## The action dispatch -/

/-- The trivial recorder invariant of `NS`. -/
abbrev PT : Recording → Prop := fun _ => True

theorem pt_frame : PFrame PT := fun _ _ _ _ _ => trivial
theorem pt_rec {e : Env} : ∀ r keys, PT r → PT { r with recorder := recordReads e keys r.recorder } :=
  fun _ _ _ => trivial
theorem pt_rem : RemClosed PT := fun _ _ _ => trivial

section act
variable {e : Env}

/-- **`ActSim` for `NS`** (no `RemClosed` obligation: `P := True`; G7 is an escape). -/
theorem actSimNS (cfg : NearCfg) (c : ActCtx) (st : ActSt) (act : Act) (hc : c.env = e) :
    SimX e PT (fun p => (p.1.wt (T e), p.2)) (D2.applyAction (D3.d3Hooks cfg) c (st.wt (T e)) act)
      (StorageExecutionNS.applyAction cfg c st act) := by
  cases act with
  | delegate raw d =>
    exact SimX.of (Sim.congr_left rfl (sim_ordinary pt_rec pt_rem c st _ hc))
  | base ba =>
    rcases ba with ⟨raw, b⟩
    cases b with
    | fcall m args g d =>
      unfold D2.applyAction StorageExecutionNS.applyAction
      dsimp only
      refine SimX.ite _ (fun _ => SimX.of (Sim.pure rfl)) (fun _ => ?_)
      refine SimX.ite _ (fun _ => SimX.of (Sim.pure rfl)) (fun _ => ?_)
      exact fcSimNS cfg c st _ m args g d hc
    | deployGlobal x =>
      unfold StorageExecutionNS.applyAction; exact SimX.esc_run _ esc_escG7 fun _ => rfl
    | useGlobal x =>
      unfold StorageExecutionNS.applyAction; exact SimX.esc_run _ esc_escG7 fun _ => rfl
    | stateInit x =>
      unfold StorageExecutionNS.applyAction; exact SimX.esc_run _ esc_escG7 fun _ => rfl
    | _ => exact SimX.of (Sim.congr_left rfl (sim_ordinary pt_rec pt_rem c st _ hc))

end act

#print axioms code_rel
#print axioms tail_rel
#print axioms simx_functionCall
#print axioms fcSimNS
#print axioms actSimNS

/-! ## The receipt level (the §13 walk, for `NS`, up to the escapes) -/

set_option hygiene false in
/-- `o4r_walk` for `SimX` and `NS`. -/
macro "o4rx_walk" : tactic => `(tactic|
  repeat (first
    | (exact SimX.of (Sim.pure rfl))
    | (exact SimX.of (Sim.ok rfl))
    | (exact SimX.of (Sim.throw _))
    | (exact SimX.of (Sim.error _))
    | (exact SimX.of (throw_bind _))
    | (exact ih _ _ _ (by rfl))
    | (exact ih _ _ (by rfl))
    | (refine SimX.bind_id (SimX.of (Sim.okR _ _)) fun _ => ?_)
    | (with_reducible refine SimX.bind (SimX.of (Sim.pure (φ := fun p : Ovl × Nat => (p.1.wt (T e), p.2)) (by with_unfolding_all exact rfl))) fun _ => ?_)
    | (with_reducible refine SimX.bind_id (α := List Rcpt × List Rcpt) (SimX.of (Sim.pure (by with_unfolding_all exact rfl))) fun _ => ?_)
    | (refine SimX.bind_id (SimX.of (Sim.liftE _)) fun _ => ?_)
    | (refine SimX.book (c := ()) pt_frame (Book.modify_frame _ (fun _ => rfl) (fun _ => rfl)) ?_)
    | (with_reducible refine SimX.get_all fun _ => ?_)
    | (refine SimX.bind_id (SimX.of (Sim.logged (R_get' _ (by rfl) _ _) pt_rec)) fun _ => ?_)
    | (refine SimX.bind_id (SimX.of (Sim.logged (R_getAcct' _ (by first | rfl | (split <;> rfl)) _) pt_rec)) fun _ => ?_)
    | (refine SimX.bind_id (SimX.of (Sim.logged (R_contains' _ (by rfl) _ _) pt_rec)) fun _ => ?_)
    | (refine SimX.book (c := ()) pt_frame Book.startReceipt ?_)
    | (refine SimX.book (c := ()) pt_frame (Book.modifyPipe _) ?_)
    | (refine SimX.book (c := ()) pt_frame (Book.modifyDetail _) ?_)
    | (refine SimX.bind (simx_actionLoop cfg _ _ _ _ _ _ _ _ _ (by rfl)) fun _ => ?_)
    | (with_reducible refine SimX.bind (SimX.of (Sim.pure (φ := fun o : Ovl => o.wt (T e)) (by with_unfolding_all exact rfl))) fun _ => ?_)
    | (refine SimX.bind (SimX.foldlM' (φ := fun p : Ovl × Nat => (p.1.wt (T e), p.2)) (fun _ _ => ?_) _ rfl) fun _ => ?_)
    | (refine SimX.bind (simx_applyActionReceipt cfg _ _ _ _ (by rfl)) fun _ => ?_)
    | (exact SimX.of (Sim.excl _ (by decide)))
    | (exact SimX.of (Sim.excl_bind _ (by decide)))
    | (refine SimX.bind (SimX.of (sim_emitReceipts pt_rec _ _ _ _ _ (by rfl))) fun _ => ?_)
    | (refine SimX.ite _ (fun _ => ?_) (fun _ => ?_))
    | (refine SimX.ite_right _ (fun _ => ?_) (fun _ => ?_))
    | (split <;> (rename_i hsplit; (try dsimp only at hsplit); (try simp only [hsplit]); (try dsimp only)))))

section walk
variable {e : Env}

theorem simx_actionLoop (cfg : NearCfg)
    (r : Rcpt) (a : ActionR) (inputs : List (Option Bytes)) (deployed attempted : List Bytes) :
    ∀ (i : Nat) (acts : List Act) (acc : ActSt × AR) (accO : ActSt × AR), accO = (acc.1.wt (T e), acc.2) →
    SimX e PT (fun p => (p.1.wt (T e), p.2))
      (D2.actionLoop (D3.d3Hooks cfg) e r a inputs deployed attempted i acts accO)
      (StorageExecutionNS.actionLoop cfg e r a inputs deployed attempted i acts acc)
  | i, [], acc, accO, h => by
    subst h; unfold D2.actionLoop StorageExecutionNS.actionLoop; exact SimX.of (Sim.ok rfl)
  | i, act :: rest, (st, res), accO, h => by
    subst h
    have ih := simx_actionLoop cfg r a inputs deployed attempted (i + 1) rest
    unfold D2.actionLoop StorageExecutionNS.actionLoop
    simp only []
    refine SimX.book (c := ()) pt_frame (Book.modify_frame _ (fun _ => rfl) (fun _ => rfl)) ?_
    refine SimX.bind (actSimNS cfg _ _ _ rfl) fun p => ?_
    rcases p with ⟨st', ar⟩
    dsimp only
    o4rx_walk
    all_goals done

set_option maxHeartbeats 40000000 in
theorem simx_applyActionReceipt (cfg : NearCfg) (rs rsO : RS) (r : Rcpt) (a : ActionR) (h : rsO = rs.wt (T e)) :
    SimX e PT (fun p => (p.1.wt (T e), p.2)) (D2.applyActionReceipt (D3.d3Hooks cfg) e rsO r a)
      (StorageExecutionNS.applyActionReceipt cfg e rs r a) := by
  subst h
  unfold D2.applyActionReceipt StorageExecutionNS.applyActionReceipt
  simp only [StorageExecution.getR, StorageExecution.getAcctR]
  refine SimX.bind (φ := fun p : Ovl × List (Option Bytes) => (p.1.wt (T e), p.2))
    (SimX.foldlM' (fun b c => ?_) _ rfl) fun p => ?_
  · rcases b with ⟨o, ins⟩
    dsimp only
    o4rx_walk
    all_goals done
  · rcases p with ⟨o, ins⟩
    dsimp only
    o4rx_walk
    all_goals done

theorem simx_processReceipt (cfg : NearCfg) (rs rsO : RS) (r : Rcpt) (h : rsO = rs.wt (T e)) :
    SimX e PT (fun p => (p.1.wt (T e), p.2)) (D2.processReceipt (D3.d3Hooks cfg) e rsO r)
      (StorageExecutionNS.processReceipt cfg e rs r) := by
  subst h
  unfold D2.processReceipt StorageExecutionNS.processReceipt
  simp only [StorageExecution.getR, StorageExecution.containsR, StorageExecution.decodeStoredRcptR,
    Bool.false_eq_true, ↓reduceIte]
  o4rx_walk
  all_goals o4rx_walk
  all_goals done

theorem simx_processWithTotals (cfg : NearCfg) (rs rsO : RS) (r : Rcpt) (h : rsO = rs.wt (T e)) :
    SimX e PT (·.wt (T e)) (D2.processWithTotals (D3.d3Hooks cfg) e rsO r)
      (StorageExecutionNS.processWithTotals cfg e rs r) := by
  subst h
  unfold D2.processWithTotals StorageExecutionNS.processWithTotals
  refine SimX.book (c := ()) pt_frame (Book.modifyPipe _) ?_
  refine SimX.bind (simx_processReceipt cfg _ _ _ rfl) fun p => ?_
  rcases p with ⟨rs', o⟩
  dsimp only
  o4rx_walk
  all_goals done

theorem simx_drain (cfg : NearCfg) :
    ∀ (fuel : Nat) (rs rsO : RS), rsO = rs.wt (T e) →
    SimX e PT (·.wt (T e)) (D2.processWithInstant.drain (D3.d3Hooks cfg) e fuel rsO)
      (StorageExecutionNS.processWithInstant.drain cfg e fuel rs)
  | 0, rs, rsO, h => by
    unfold D2.processWithInstant.drain StorageExecutionNS.processWithInstant.drain; exact SimX.of (Sim.error _)
  | fuel + 1, rs, rsO, h => by
    subst h
    unfold D2.processWithInstant.drain StorageExecutionNS.processWithInstant.drain
    dsimp only
    have hi : (rs.wt (T e)).instant = rs.instant := rfl
    rw [hi]
    cases rs.instant with
    | nil => exact SimX.of (Sim.ok rfl)
    | cons ir more =>
      exact SimX.bind (simx_processWithTotals cfg _ _ _ rfl) fun rs' => simx_drain cfg fuel rs' _ rfl

/-- **`PWISim` for `NS`.** -/
theorem simx_processWithInstant (cfg : NearCfg) (rs rsO : RS) (r : Rcpt) (h : rsO = rs.wt (T e)) :
    SimX e PT (·.wt (T e)) (D2.processWithInstant (D3.d3Hooks cfg) e rsO r)
      (StorageExecutionNS.processWithInstant cfg e rs r) := by
  subst h
  unfold D2.processWithInstant StorageExecutionNS.processWithInstant
  exact SimX.bind (simx_processWithTotals cfg _ _ _ rfl) fun rs' => simx_drain cfg _ rs' _ rfl

end walk

#print axioms simx_processWithInstant

end NearSpecV3.Successor.O4E
