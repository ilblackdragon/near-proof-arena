import NearSpecV3.Logged.WasmHRHost
import NearSpecV3.Logged.WasmStepE

/-!
# The WASM machine with the trie store read through `SM`

`runL` is `Exec.run` on states whose store field is erased (`E dummy`): a step that calls one of the
seven storage host functions (`stepPre`) runs that host's mirror (`hostCallL`, reads through
`SM.get'`); every other step is `Exec.step` itself (`E_step`: it commutes with the erasure). On a store
`g` agreeing with the states' store `σ`, `runL` computes `run` (`runL_spec`); the same for
`callEntryL` and `runCallL`.
-/

namespace NearSpecV3.Logged.W

open NearSpecV3.Wasm NearSpecV3.Wasm.TTN

/-! ## `stepPre` commutes with the erasure -/

section
variable {σ : TTN.Store} {s : St}

theorem E_callPre (p : Prepared) (fi : Nat) :
    callPre p (E σ s) fi = (callPre p s fi).map (fun q => (E σ q.1, q.2)) := by
  unfold callPre; split
  · split <;> rfl
  · rfl

theorem E_execPre (p : Prepared) (f : Frame) (i : Instr) :
    execPre p (E σ s) f i = (execPre p s f i).map (fun q => (E σ q.1, q.2)) := by
  unfold execPre
  cases i with
  | call fi => simp only; rw [E_setFrame, E_callPre]
  | callIndirect ty x =>
    simp only; rw [E_popN]; simp only [E_table]
    split
    · split
      · split
        · rfl
        · rw [E_setFrame, E_callPre]
      · rfl
    · rfl
  | _ => rfl

theorem E_stepPre (p : Prepared) : stepPre p (E σ s) = (stepPre p s).map (fun q => (E σ q.1, q.2)) := by
  unfold stepPre
  rw [E_frames]
  split
  · rfl
  rename_i f fs hf
  split
  · rfl
  split
  · rfl
  split
  · rfl
  · exact E_execPre p f _
  · rw [E_topCount, E_charge]
    generalize charge s _ _ = r
    cases r with
    | cont s' => exact E_execPre p f _
    | _ => rfl

end

/-! ## Results fixed by an erasure -/

def mapRun (f : St → St) : Run → Run
  | .line l => .line l
  | .done s e => .done (f s) e

/-- The states of `r` have store `σ` (`r` is fixed by `E σ`). -/
def ResOK (σ : TTN.Store) (r : Res) : Prop := mapRes (E σ) r = r

theorem StOK_iff_E {σ : TTN.Store} {t : St} : StOK σ t ↔ E σ t = t :=
  ⟨E_of_StOK, fun h => h ▸ StOK_E t⟩

theorem E_E (σ τ : TTN.Store) (t : St) : E σ (E τ t) = E σ t := by
  unfold E; cases t.real <;> rfl

theorem ResOK_mapRes (σ : TTN.Store) (r : Res) : ResOK σ (mapRes (E σ) r) := by
  unfold ResOK; cases r <;> simp only [mapRes, E_E]

theorem mapRes_mapRes (σ τ : TTN.Store) (r : Res) : mapRes (E σ) (mapRes (E τ) r) = mapRes (E σ) r := by
  cases r <;> simp only [mapRes, E_E]

/-! ## The storage host table -/

theorem hostCallL_none (name : String) (h : storageHosts.contains name = false) : hostCallL name = none := by
  unfold storageHosts at h
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
    ne_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  rw [hostCallL.eq_8 name (fun e => h1 e) (fun e => h2 e) (fun e => h3 e) (fun e => h4 e) (fun e => h5 e)
    (fun e => h6 e) (fun e => h7 e)]

section
variable {σ : TTN.Store} {g : NearSpec.Bytes → Option NearSpec.Bytes}

theorem storageHost_HP (hσ : StoreAgrees σ g) (name : String) (h : storageHosts.contains name = true) :
    ∃ y x, hostCallL name = some y ∧ hostCall name = some x ∧ ∀ t, StOK σ t → HP σ g t y x := by
  unfold storageHosts at h
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h | h | h | h | h | h <;> subst h
  · exact ⟨_, _, hostCallL.eq_1, hostCall.eq_35, fun t ht => HP_storage_write hσ t ht _ _ hostCallL.eq_1 hostCall.eq_35⟩
  · exact ⟨_, _, hostCallL.eq_2, hostCall.eq_36, fun t ht => HP_storage_read hσ t ht _ _ hostCallL.eq_2 hostCall.eq_36⟩
  · exact ⟨_, _, hostCallL.eq_3, hostCall.eq_37,
      fun t ht => HP_storage_remove hσ t ht _ _ hostCallL.eq_3 hostCall.eq_37⟩
  · exact ⟨_, _, hostCallL.eq_4, hostCall.eq_38,
      fun t ht => HP_storage_has_key hσ t ht _ _ hostCallL.eq_4 hostCall.eq_38⟩
  · exact ⟨_, _, hostCallL.eq_5, hostCall.eq_64,
      fun t ht => HP_yield_create_with_id hσ t ht _ _ hostCallL.eq_5 hostCall.eq_64⟩
  · exact ⟨_, _, hostCallL.eq_6, hostCall.eq_62,
      fun t ht => HP_yield_resume hσ t ht _ _ hostCallL.eq_6 hostCall.eq_62⟩
  · exact ⟨_, _, hostCallL.eq_7, hostCall.eq_68,
      fun t ht => HP_yield_resume_with_yield_id hσ t ht _ _ hostCallL.eq_7 hostCall.eq_68⟩

end

/-! ## A host call of a storage host function -/

def callHostL (s : St) (name : String) : SM NearSpec.Bytes Res :=
  if s.real.isSome && realOodHosts.contains name then
    pure (.unmodeled s!"out-of-domain host function {name} called") else
  match sync s with
  | .error e => pure (.unmodeled e)
  | .ok s =>
    match hostCallL name with
    | none => pure (.unmodeled s!"host function {name} not modelled in D3α")
    | some h => do
      let p ← (h.run).run s
      match p.1 with
      | .ok _ => pure (.cont { p.2 with gas := { p.2.gas with g := p.2.gas.remaining } })
      | .error e => pure (if e.startsWith "unmodeled" then .unmodeled e else .abort p.2 e)

section
variable {σ : TTN.Store} {g : NearSpec.Bytes → Option NearSpec.Bytes}

theorem StOK_sync {s s' : St} (ht : StOK σ s) (h : sync s = .ok s') : StOK σ s' := by
  have e := @E_sync σ s
  rw [E_of_StOK ht, h] at e
  simp only [Except.map] at e
  have e2 : s' = E σ s' := by injection e
  rw [e2]; exact StOK_E _

theorem callHostL_spec (hσ : StoreAgrees σ g) {s : St} (ht : StOK σ s) (name : String)
    (hn : storageHosts.contains name = true) :
    SM.run g (callHostL (E dummy s) name) = .ok (mapRes (E dummy) (callHost s name)) ∧
      ResOK σ (callHost s name) := by
  unfold callHostL callHost
  rw [E_real_isSome]
  split
  · exact ⟨rfl, rfl⟩
  rw [E_sync]
  cases hs : sync s with
  | error e => exact ⟨rfl, rfl⟩
  | ok s' =>
    have hs' := StOK_sync ht hs
    simp only [exmap_ok]
    obtain ⟨y, x, hy, hx, hp⟩ := storageHost_HP hσ name hn
    rw [hy, hx]; dsimp only
    obtain ⟨h1, h2⟩ := hp s' hs'
    rw [SM.run_bind', h1]
    cases hr : x.run s' with
    | ok a t =>
      rw [hr] at h2
      refine ⟨rfl, ?_⟩
      show mapRes (E σ) (.cont _) = _
      have h2' : StOK σ t := h2
      exact congrArg Res.cont (E_of_StOK (StOK_real h2' rfl))
    | error e t =>
      rw [hr] at h2
      have h2' : StOK σ t := h2
      by_cases hu : e.startsWith "unmodeled" = true
      · refine ⟨?_, ?_⟩
        · show Except.ok (if e.startsWith "unmodeled" = true then _ else _) = _
          simp only [hu, ↓reduceIte, mapRes]
        · show mapRes (E σ) (if e.startsWith "unmodeled" = true then _ else _) = _
          simp only [hu, ↓reduceIte, mapRes]
      · refine ⟨?_, ?_⟩
        · show Except.ok (if e.startsWith "unmodeled" = true then _ else _) = _
          simp only [hu, ↓reduceIte, mapRes, Bool.false_eq_true]; rfl
        · show mapRes (E σ) (if e.startsWith "unmodeled" = true then _ else _) = _
          simp only [hu, ↓reduceIte, mapRes, Bool.false_eq_true]
          rw [E_of_StOK h2']

end

/-! ## The machine loop -/

theorem callPre_storage {p : Prepared} {s s1 : St} {fi : Nat} {n : String} (h : callPre p s fi = some (s1, n)) :
    storageHosts.contains n = true := by
  unfold callPre at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

theorem stepPre_storage {p : Prepared} {s s1 : St} {n : String} (h : stepPre p s = some (s1, n)) :
    storageHosts.contains n = true := by
  have hexec : ∀ s' f i, execPre p s' f i = some (s1, n) → storageHosts.contains n = true := by
    intro s' f i he
    unfold execPre at he
    split at he
    · exact callPre_storage he
    · simp only at he
      split at he
      · split at he
        · split at he
          · cases he
          · exact callPre_storage he
        · cases he
      · cases he
    · cases he
  unfold stepPre at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  · exact hexec _ _ _ h
  · split at h
    · exact hexec _ _ _ h
    · cases h

/-- One machine step: a storage host call through `SM`, else `Exec.step`. -/
def stepL (cfg : NearCfg) (p : Prepared) (s : St) : SM NearSpec.Bytes Res :=
  match stepPre p s with
  | some (s1, name) => callHostL s1 name
  | none => pure (step cfg p s)

def runL (cfg : NearCfg) (p : Prepared) : Nat → St → SM NearSpec.Bytes Res
  | 0, _ => pure (.unmodeled "fuel exhausted")
  | n + 1, s => stepL cfg p s >>= fun r =>
    match r with
    | .cont s => runL cfg p n s
    | r => pure r

section
variable {σ : TTN.Store} {g : NearSpec.Bytes → Option NearSpec.Bytes}

theorem ResOK_cont {r : Res} {s : St} (h : ResOK σ r) (hr : r = .cont s) : StOK σ s := by
  subst hr; unfold ResOK mapRes at h; injection h with h; rw [← h]; exact StOK_E _

theorem runL_spec (hσ : StoreAgrees σ g) (cfg : NearCfg) (p : Prepared) :
    ∀ (n : Nat) (s : St), StOK σ s →
      SM.run g (runL cfg p n (E dummy s)) = .ok (mapRes (E dummy) (run cfg p n s)) ∧ ResOK σ (run cfg p n s)
  | 0, s, _ => ⟨rfl, rfl⟩
  | n + 1, s, ht => by
    unfold runL run
    -- the step: its mirror result and the fact that it keeps the store
    have hstep : SM.run g (stepL cfg p (E dummy s)) = .ok (mapRes (E dummy) (step cfg p s)) ∧
        ResOK σ (step cfg p s) := by
      unfold stepL
      rw [E_stepPre]
      cases hsp : stepPre p s with
      | none =>
        refine ⟨?_, ?_⟩
        · show Except.ok (step cfg p (E dummy s)) = _
          rw [E_step cfg p hsp]
        · have e := E_step (σ := σ) cfg p hsp
          rw [E_of_StOK ht] at e
          unfold ResOK; exact e.symm
      | some q =>
        obtain ⟨s1, name⟩ := q
        have hs1 : StOK σ s1 := by
          have e := @E_stepPre σ s p
          rw [E_of_StOK ht, hsp] at e
          simp only [Option.map_some] at e
          have e2 : s1 = E σ s1 := by injection e with e; injection e
          rw [e2]; exact StOK_E _
        rw [step_of_stepPre cfg p s s1 name hsp]
        exact callHostL_spec hσ hs1 name (stepPre_storage hsp)
    obtain ⟨h1, h2⟩ := hstep
    rw [SM.run_bind', h1]
    generalize hr : step cfg p s = r at h2 ⊢
    cases r with
    | cont s' => exact runL_spec hσ cfg p n s' (ResOK_cont h2 rfl)
    | fin s' => exact ⟨rfl, h2⟩
    | abort s' e => exact ⟨rfl, h2⟩
    | unmodeled w => exact ⟨rfl, h2⟩

end

/-! ## A wasm entry and a whole call -/

def entrySt (s : St) : St := { s with gas := { s.gas with g := s.gas.remaining }, stack := #[], frames := [] }

theorem E_entrySt (σ : TTN.Store) (s : St) : entrySt (E σ s) = E σ (entrySt s) := rfl

def enterRunL (cfg : NearCfg) (p : Prepared) (fuel : Nat) (s : St) (fi : Nat) : SM NearSpec.Bytes Res :=
  match enter p s fi with
  | .cont s => runL cfg p fuel s
  | r => pure r

def entryResult (r : Res) : Except String (St × Option String) :=
  match r with
  | .fin s => (sync s).map (·, none)
  | .abort s e => (sync s).map (·, some e)
  | .unmodeled why => .error why
  | .cont _ => .error "cont"

def callEntryL (cfg : NearCfg) (p : Prepared) (fuel : Nat) (s : St) (fi : Nat) :
    SM NearSpec.Bytes (Except String (St × Option String)) :=
  enterRunL cfg p fuel (entrySt s) fi >>= fun r => pure (entryResult r)

def mapEntry (f : St → St) (x : Except String (St × Option String)) : Except String (St × Option String) :=
  x.map (fun q => (f q.1, q.2))

section
variable {σ : TTN.Store} {g : NearSpec.Bytes → Option NearSpec.Bytes}

theorem callEntry_eq (cfg : NearCfg) (p : Prepared) (fuel : Nat) (s : St) (fi : Nat) :
    callEntry cfg p fuel s fi =
      entryResult (match enter p (entrySt s) fi with
        | .cont s => run cfg p fuel s
        | r => r) := by
  unfold callEntry entryResult entrySt; rfl

theorem entryResult_E (r : Res) : entryResult (mapRes (E dummy) r) = mapEntry (E dummy) (entryResult r) := by
  cases r with
  | cont s => rfl
  | fin s => simp only [mapRes, entryResult, mapEntry, E_sync]; cases sync s <;> rfl
  | abort s e => simp only [mapRes, entryResult, mapEntry, E_sync]; cases sync s <;> rfl
  | unmodeled w => rfl

theorem callEntryL_spec (hσ : StoreAgrees σ g) (cfg : NearCfg) (p : Prepared) (fuel : Nat) {s : St}
    (ht : StOK σ s) (fi : Nat) :
    SM.run g (callEntryL cfg p fuel (E dummy s) fi) = .ok (mapEntry (E dummy) (callEntry cfg p fuel s fi)) := by
  unfold callEntryL enterRunL
  rw [callEntry_eq, E_entrySt, E_enter]
  have hs0 : StOK σ (entrySt s) := StOK_real ht rfl
  have hok : ResOK σ (enter p (entrySt s) fi) := by
    have e := E_enter (σ := σ) (s := entrySt s) p fi
    rw [E_of_StOK hs0] at e
    exact e.symm
  generalize enter p (entrySt s) fi = r at hok ⊢
  cases r with
  | cont s' =>
    simp only [mapRes, SM.run_bind']
    rw [(runL_spec hσ cfg p fuel s' (ResOK_cont hok rfl)).1]
    show Except.ok (entryResult _) = _
    rw [entryResult_E]
  | fin s' => show Except.ok (entryResult _) = _; rw [entryResult_E]
  | abort s' e => show Except.ok (entryResult _) = _; rw [entryResult_E]
  | unmodeled w => rfl

end

theorem entryResult_StOK {r : Res} (h : ResOK σ r) {q : St × Option String} (hq : entryResult r = .ok q) :
    StOK σ q.1 := by
  cases r with
  | fin s =>
    have hs : StOK σ s := by unfold ResOK mapRes at h; injection h with h; rw [← h]; exact StOK_E _
    simp only [entryResult] at hq
    cases hy : sync s with
    | error e => rw [hy] at hq; cases hq
    | ok s' => rw [hy] at hq; cases hq; exact StOK_sync hs hy
  | abort s e =>
    have hs : StOK σ s := by unfold ResOK mapRes at h; injection h with h; rw [← h]; exact StOK_E _
    simp only [entryResult] at hq
    cases hy : sync s with
    | error e => rw [hy] at hq; cases hq
    | ok s' => rw [hy] at hq; cases hq; exact StOK_sync hs hy
  | cont s => cases hq
  | unmodeled w => cases hq

theorem callEntry_StOK (hσ : StoreAgrees σ g) (cfg : NearCfg) (p : Prepared) (fuel : Nat) {s : St}
    (ht : StOK σ s) (fi : Nat) {q : St × Option String} (hq : callEntry cfg p fuel s fi = .ok q) :
    StOK σ q.1 := by
  rw [callEntry_eq] at hq
  have hs0 : StOK σ (entrySt s) := StOK_real ht rfl
  have hok : ResOK σ (enter p (entrySt s) fi) := by
    have e := E_enter (σ := σ) (s := entrySt s) p fi
    rw [E_of_StOK hs0] at e
    exact e.symm
  generalize enter p (entrySt s) fi = r at hok hq
  cases r with
  | cont s' => exact entryResult_StOK (runL_spec (g := g) hσ cfg p fuel s' (ResOK_cont hok rfl)).2 hq
  | _ => exact entryResult_StOK hok hq

def afterStartL (cfg : NearCfg) (p : Prepared) (fuel : Nat) (s : St) :
    SM NearSpec.Bytes (Except String (St × Option String)) :=
  match p.m.start with
  | some st => callEntryL cfg p fuel s st
  | none => pure (.ok (s, none))

def mainL (cfg : NearCfg) (p : Prepared) (fuel : Nat) (mi : Nat) :
    Except String (St × Option String) → SM NearSpec.Bytes Run
  | .error why => pure (.line s!"unmodeled {why}")
  | .ok (s, some e) => pure (.done s (some e))
  | .ok (s, none) => callEntryL cfg p fuel s mi >>= fun b => match b with
    | .error why => pure (.line s!"unmodeled {why}")
    | .ok (s, e) => pure (.done s e)

/-- The contract-loading charge of `runCall`. -/
def loadedOf (gs : Gas) (code : ByteArray) : Gas × Option String :=
  match payPer gs C.contractLoadingBytes code.size with
  | (gs, none) => payBase gs C.contractLoadingBase
  | r => r

/-- `Exec.runCall … (real := some real)`, with the machine run through `SM` (`callEntryL`). -/
def runCallL (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (fuel : Nat)
    (blockLevel : Bool) (full : Bool) (real : TTN.RealStore) : SM NearSpec.Bytes Run :=
  let emptySt (gs : Gas) : St :=
    { pages := #[], globals := #[], table := #[], tableMax := 0, elems := #[], datas := #[],
      stackRem := 0, gas := gs, ctx := ctx }
  let ext (s : St) : String := if full then fullExtra s else ""
  let nop (e : String) : Run := .line (s!"abort 0 0 {e}" ++ ext (emptySt (Gas.init ctx.prepaidGas)))
  if method.isEmpty then pure (nop "MethodResolveError(MethodEmptyName)") else
  match prepare cfg code blockLevel with
  | .outOfDomain why => pure (.line s!"out-of-domain {why}")
  | .unmodeled why => pure (.line s!"unmodeled {why}")
  | .prepErr v _ => pure (nop s!"CompilationError(PrepareError({v}))")
  | .compileErr k _ =>
    pure (nop s!"CompilationError(WasmtimeCompileError \{ msg: \"failed to compile: wasm[0]::function[{k}]\" })")
  | .ok p =>
    match loadedOf (Gas.init ctx.prepaidGas) code with
    | (gs, some _) => pure (.line (s!"abort {gs.burnt} {gs.used} {errGasExceeded}" ++ ext (emptySt gs)))
    | (gs, none) =>
      match link p with
      | .linkError msg =>
        pure (.line (s!"abort {gs.burnt} {gs.used} LinkError \{ msg: \"{msg}\" }" ++ ext (emptySt gs)))
      | .invariant why => pure (.line s!"unmodeled invariant: {why}")
      | .ok =>
        match resolve p method with
        | .notFound => pure (nop "MethodResolveError(MethodNotFound)")
        | .invalidSignature => pure (nop "MethodResolveError(MethodInvalidSignature)")
        | .invariant why => pure (.line s!"unmodeled invariant: {why}")
        | .ok mi =>
          match instantiate cfg p gs with
          | .error e => pure (.line (s!"abort {gs.burnt} {gs.used} {e}" ++ ext (emptySt gs)))
          | .ok s =>
            let s := { s with ctx := ctx, balance := ctx.accountBalance + ctx.attachedDeposit,
                              storageUsage := ctx.storageUsage, real := some real }
            afterStartL cfg p fuel s >>= mainL cfg p fuel mi

section
variable {σ : TTN.Store} {g : NearSpec.Bytes → Option NearSpec.Bytes}

theorem mainL_spec (hσ : StoreAgrees σ g) (cfg : NearCfg) (p : Prepared) (fuel mi : Nat) {s : St}
    (ht : StOK σ s) :
    SM.run g (afterStartL cfg p fuel (E dummy s) >>= mainL cfg p fuel mi) =
      .ok (mapRun (E dummy) (match (match p.m.start with
          | some st => callEntry cfg p fuel s st
          | none => .ok (s, none)) with
        | .error why => .line s!"unmodeled {why}"
        | .ok (s, some e) => .done s (some e)
        | .ok (s, none) =>
          match callEntry cfg p fuel s mi with
          | .error why => .line s!"unmodeled {why}"
          | .ok (s, e) => .done s e)) := by
  have hA : SM.run g (afterStartL cfg p fuel (E dummy s)) = .ok (mapEntry (E dummy) (match p.m.start with
      | some st => callEntry cfg p fuel s st
      | none => .ok (s, none))) := by
    unfold afterStartL
    cases p.m.start with
    | some st => exact callEntryL_spec hσ cfg p fuel ht st
    | none => rfl
  have hAok : ∀ q, (match p.m.start with
      | some st => callEntry cfg p fuel s st
      | none => .ok (s, none)) = .ok q → StOK σ q.1 := by
    intro q hq
    cases hst : p.m.start with
    | some st => rw [hst] at hq; exact callEntry_StOK hσ cfg p fuel ht st hq
    | none => rw [hst] at hq; cases hq; exact ht
  rw [SM.run_bind', hA]
  generalize (match p.m.start with
      | some st => callEntry cfg p fuel s st
      | none => .ok (s, none)) = a at hAok ⊢
  cases a with
  | error why => rfl
  | ok q =>
    obtain ⟨s1, e⟩ := q
    have hs1 : StOK σ s1 := hAok _ rfl
    cases e with
    | some e => rfl
    | none =>
      show SM.run g (callEntryL cfg p fuel (E dummy s1) mi >>= _) = _
      rw [SM.run_bind', callEntryL_spec hσ cfg p fuel hs1 mi]
      dsimp only
      cases callEntry cfg p fuel s1 mi with
      | error why => rfl
      | ok q => rfl

set_option simprocs false in
theorem runCallL_spec (hσ : StoreAgrees σ g) (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (fuel : Nat) (blockLevel full : Bool) (real : TTN.RealStore) (hr : real.store = σ) :
    SM.run g (runCallL cfg code method ctx fuel blockLevel full (dr real)) =
      .ok (mapRun (E dummy) (runCall cfg code method ctx fuel blockLevel full (some real))) := by
  unfold runCallL runCall
  simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ite_false]
  by_cases hm : method.isEmpty = true
  · simp only [hm, ite_true]; rfl
  simp only [hm, ite_false, Bool.false_eq_true]
  cases prepare cfg code blockLevel with
  | ok p =>
    dsimp only
    conv => rhs; arg 1; arg 2; arg 2; change loadedOf (Gas.init ctx.prepaidGas) code
    cases loadedOf (Gas.init ctx.prepaidGas) code with
    | mk g2 e2 =>
      cases e2 with
      | some e => rfl
      | none =>
        dsimp only
        cases link p with
        | ok =>
          dsimp only
          cases resolve p method with
          | ok mi =>
            dsimp only
            cases instantiate cfg p g2 with
            | error e => rfl
            | ok s0 =>
              have hst : StOK σ ({ s0 with ctx := ctx, balance := ctx.accountBalance + ctx.attachedDeposit, storageUsage := ctx.storageUsage, real := some real } : St) := by
                intro r h; cases h; exact hr
              exact mainL_spec hσ cfg p fuel mi hst
          | _ => rfl
        | _ => rfl
  | _ => rfl
end

end NearSpecV3.Logged.W
