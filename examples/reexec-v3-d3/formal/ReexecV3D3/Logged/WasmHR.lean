import ReexecV3D3.Logged.WasmHostL
import ReexecV3D3.Logged.WasmCRHostCall
import ReexecV3D3.Logged.Lockstep

/-!
# Storage host mirrors = originals

`StOK σ t`: the trie store of `t` (if any) is `σ`. `HP σ g t y x`: the mirror `y`, run on the erased
state `E dummy t` against the store `g`, gives the original's result on `t` (state erased), and the
original's final state still has store `σ`. Rules for binds, `get`/`set`/`modify`, lifted store-free
host code (`HP_liftH`, from `CR`), and the store operations (`HP_realOp`, `HP_realGet`, `HP_realHas`).
-/

namespace ReexecV3D3.Logged.W

open NearSpecV3.Wasm NearSpecV3.Wasm.TTN

theorem CR_realSetH (σ : TTN.Store) (r : TTN.RealStore) (k : ByteArray) (v : Option ByteArray) :
    CR σ (realSetH r k v) (realSetH r k v) := by
  unfold realSetH; cr

theorem CR_observeH (σ : TTN.Store) : CR σ observeH observeH := by
  unfold observeH
  apply CR_get_bind; intro t
  show CR σ (match t.real with
    | some r => if TTN.overLimit r = true then hErr _ else pure ()
    | none => pure ()) (match t.real.map (fun r => { r with store := σ }) with
    | some r => if TTN.overLimit r = true then hErr _ else pure ()
    | none => pure ())
  cases t.real with
  | none => exact CR_pure _
  | some r => exact CR_ite _ _ rfl (CR_hErr σ _) (CR_pure _)

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_realSetH)
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_observeH)

def StOK (σ : TTN.Store) (t : St) : Prop := ∀ r, t.real = some r → r.store = σ

def finalSt {α : Type} : EStateM.Result String St α → St
  | .ok _ s => s
  | .error _ s => s

def HP {α : Type} (σ : TTN.Store) (g : NearSpec.Bytes → Option NearSpec.Bytes) (t : St) (y : HMM α) (x : HM α) :
    Prop :=
  SM.run g ((y.run).run (E dummy t)) = .ok (toPair (mapSt (E dummy) (x.run t))) ∧ StOK σ (finalSt (x.run t))

section
variable {σ : TTN.Store} {g : NearSpec.Bytes → Option NearSpec.Bytes}

theorem E_of_StOK {t : St} (h : StOK σ t) : E σ t = t := by
  unfold E; cases hr : t.real with
  | none => cases t; simp_all
  | some r => have := h r hr; cases t; cases r; simp_all

theorem StOK_E (t : St) : StOK σ (E σ t) := by
  intro r hr; unfold E at hr; cases h : t.real <;> simp [h] at hr; subst hr; rfl

theorem finalSt_mapSt {α : Type} (f : St → St) (r : EStateM.Result String St α) :
    finalSt (mapSt f r) = f (finalSt r) := by cases r <;> rfl

theorem HMM_run_bind {α β : Type} (y : HMM α) (f : α → HMM β) (s : St) :
    ((y >>= f).run).run s = SM.bind (((y.run).run s)) (fun p => match p.1 with
      | .ok a => ((f a).run).run p.2
      | .error e => pure (.error e, p.2)) := by
  show SM.bind _ _ = SM.bind _ _
  congr 1; funext p; obtain ⟨a, s⟩ := p; cases a <;> rfl

theorem HM_run_bind {α β : Type} (x : HM α) (f : α → HM β) (t : St) :
    (x >>= f).run t = match x.run t with
      | .ok a s => (f a).run s
      | .error e s => .error e s := by
  show EStateM.bind x f t = _
  unfold EStateM.bind EStateM.run; cases x t <;> rfl

theorem HP_bind {α β : Type} {t : St} {y : HMM α} {x : HM α} {f' : α → HMM β} {f : α → HM β}
    (h1 : HP σ g t y x) (h2 : ∀ a t', StOK σ t' → HP σ g t' (f' a) (f a)) : HP σ g t (y >>= f') (x >>= f) := by
  obtain ⟨r1, s1⟩ := h1
  unfold HP
  rw [HMM_run_bind, SM.run_bind, r1, HM_run_bind]
  cases hx : x.run t with
  | ok a t1 =>
    rw [hx] at s1
    exact h2 a t1 s1
  | error e t1 =>
    rw [hx] at s1
    exact ⟨rfl, s1⟩

theorem HP_pure {α : Type} {t : St} (ht : StOK σ t) (a : α) : HP σ g t (pure a) (pure a) := ⟨rfl, ht⟩

theorem HP_pure' {α : Type} {t : St} (ht : StOK σ t) {a b : α} (h : a = b) : HP σ g t (pure a) (pure b) :=
  h ▸ ⟨rfl, ht⟩

theorem HP_throw {α : Type} {t : St} (ht : StOK σ t) (e : String) : HP σ g t (throw e : HMM α) (throw e) :=
  ⟨rfl, ht⟩

theorem HP_get_bind {β : Type} {t : St} {f' : St → HMM β} {f : St → HM β} (h : HP σ g t (f' (E dummy t)) (f t)) :
    HP σ g t (get >>= f') (get >>= f) := h

theorem HP_set {t : St} (u v : St) (hv : v = E dummy u) (hu : StOK σ u) : HP σ g t (set v) (set u) := by
  subst hv; exact ⟨rfl, hu⟩

theorem HP_modify {t : St} (f' f : St → St) (hf : f' (E dummy t) = E dummy (f t)) (hs : StOK σ (f t)) :
    HP σ g t (modify f') (modify f) := by
  constructor
  · show SM.run g (pure (Except.ok (), f' (E dummy t))) = _
    rw [hf]; rfl
  · exact hs

theorem HP_liftH {α : Type} {t : St} {h : HM α} (h1 : CR dummy h h) (h2 : CR σ h h) (ht : StOK σ t) :
    HP σ g t (liftH h) h := by
  constructor
  · show SM.run g (pure (toPair (h.run (E dummy t)))) = _
    rw [h1.h t]; rfl
  · have := h2.h t
    rw [E_of_StOK ht] at this
    rw [this, finalSt_mapSt]; exact StOK_E _

theorem liftW_run {γ : Type} (w : WM γ) (s : St) :
    ((liftW w).run).run s = SM.bind w (fun a => pure (Except.ok a, s)) := by
  show SM.bind (SM.bind w fun a => pure (a, s)) (fun p => pure (Except.ok p.1, p.2)) = _
  rw [← SM.bind_eq, ← SM.bind_eq, bind_assoc]; rfl

theorem HP_liftW_bind {γ β : Type} {t : St} {w : WM γ} {v : γ} {k' : γ → HMM β} {x : HM β}
    (hw : SM.run g w = .ok v) (h : HP σ g t (k' v) x) : HP σ g t (liftW w >>= k') x := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2⟩
  rw [HMM_run_bind, liftW_run, SM.run_bind, SM.run_bind, hw]
  exact h1

theorem E_real (t : St) : (E σ t).real = t.real.map (fun r => { r with store := σ }) := rfl

/-- The erased store record. -/
def dr (r : RealStore) : RealStore := { r with store := dummy }

theorem E_real' (t : St) : (E dummy t).real = t.real.map dr := rfl

theorem spec_write (hσ : StoreAgrees σ g) (r : RealStore) (hr : r.store = σ) (key : ByteArray) (gs : Gas) :
    SM.run g (storageWriteL' (dr r) key gs) = .ok (storageWrite r key gs) :=
  writeLikeL_spec hσ _ r hr dummy key gs
theorem spec_remove (hσ : StoreAgrees σ g) (r : RealStore) (hr : r.store = σ) (key : ByteArray) (gs : Gas) :
    SM.run g (storageRemoveL' (dr r) key gs) = .ok (storageRemove r key gs) :=
  writeLikeL_spec hσ _ r hr dummy key gs
theorem spec_read (hσ : StoreAgrees σ g) (r : RealStore) (hr : r.store = σ) (key : ByteArray) (gs : Gas) :
    SM.run g (storageReadL (dr r) key gs) = .ok (storageRead r key gs) :=
  storageReadL_spec hσ r hr dummy key gs
theorem spec_has (hσ : StoreAgrees σ g) (r : RealStore) (hr : r.store = σ) (key : ByteArray) (gs : Gas) :
    SM.run g (storageHasKeyL (dr r) key gs) = .ok (storageHasKey r key gs) :=
  storageHasKeyL_spec hσ r hr dummy key gs

theorem HP_realOp {t : St} (ht : StOK σ t) (r : RealStore) (hr : r.store = σ)
    (fL : RealStore → ByteArray → Gas → WM Out) (f : RealStore → ByteArray → Gas → Out)
    (hf : ∀ key gs, SM.run g (fL (dr r) key gs) = .ok (f r key gs)) (k : ByteArray) :
    HP σ g t (realOpHL (dr r) fL k) (realOpH r f k) := by
  unfold realOpHL realOpH
  apply HP_get_bind
  simp only [E_gas]
  apply HP_liftW_bind (hf _ _)
  refine HP_bind (HP_modify _ _ rfl ?_) ?_
  · intro r' h'; cases h'; exact hr
  · intro _ t' ht'
    show HP σ g t' (match (f r (r.pfx ++ k) t.gas).err with
      | some e => throw e
      | none => pure (f r (r.pfx ++ k) t.gas).old) _
    cases (f r (r.pfx ++ k) t.gas).err with
    | some e => exact HP_throw ht' e
    | none => exact HP_pure ht' _

theorem HP_realGet {t : St} (ht : StOK σ t) (hσ : StoreAgrees σ g) (k : ByteArray) :
    HP σ g t (realGetHL k) (realGetH k) := by
  unfold realGetHL realGetH
  apply HP_get_bind
  rw [E_real]
  cases hr : t.real with
  | none => exact HP_throw ht _
  | some r =>
    have hrs := ht r hr
    simp only [Option.map_some]
    cases r.overlay.get? k with
    | some v => exact HP_pure ht _
    | none =>
      simp only
      apply HP_liftW_bind (lookupL_spec hσ _ _)
      rw [hrs]
      cases lookup σ r.root k with
      | error e => exact HP_throw ht _
      | ok l =>
        simp only
        cases l.value with
        | none => exact HP_pure ht _
        | some p =>
          obtain ⟨len, vh⟩ := p
          simp only
          apply HP_liftW_bind (run_getBA hσ vh)
          cases σ vh with
          | some v => exact HP_pure ht _
          | none => exact HP_throw ht _

theorem HP_realHas {t : St} (ht : StOK σ t) (hσ : StoreAgrees σ g) (k : ByteArray) :
    HP σ g t (realHasHL k) (realHasH k) := by
  unfold realHasHL realHasH
  apply HP_get_bind
  rw [E_real]
  cases hr : t.real with
  | none => exact HP_throw ht _
  | some r =>
    have hrs := ht r hr
    simp only [Option.map_some]
    cases r.overlay.get? k with
    | some v => exact HP_pure ht _
    | none =>
      simp only
      apply HP_liftW_bind (lookupL_spec hσ _ _)
      rw [hrs]
      cases lookup σ r.root k with
      | error e => exact HP_throw ht _
      | ok l => exact HP_pure ht _

theorem HP_liftH_eq {α : Type} {t : St} {h' h : HM α} (he : h' = h) (h1 : CR dummy h h) (h2 : CR σ h h)
    (ht : StOK σ t) : HP σ g t (liftH h') h := by subst he; exact HP_liftH h1 h2 ht

theorem HP_pure_bind {α β : Type} {t : St} (a : α) {f' : α → HMM β} {f : α → HM β}
    (h : HP σ g t (f' a) (f a)) : HP σ g t (pure a >>= f') (pure a >>= f) := h

theorem HP_pure_bind' {α β : Type} {t : St} {a b : α} {f' : α → HMM β} {f : α → HM β} (hab : b = a)
    (h : HP σ g t (f' a) (f a)) : HP σ g t (pure a >>= f') (pure b >>= f) := by subst hab; exact h

/-- `do` join points: relate the two once, instead of inlining them into every branch. -/
theorem HP_jp {β γ δ : Type} {t : St} {v' : γ → HMM β} {v : γ → HM β} {b' : (γ → HMM β) → HMM δ}
    {b : (γ → HM β) → HM δ} (hv : ∀ a t', StOK σ t' → HP σ g t' (v' a) (v a))
    (hb : ∀ j' j, (∀ a t', StOK σ t' → HP σ g t' (j' a) (j a)) → HP σ g t (b' j') (b j)) :
    HP σ g t (have j' := v'; b' j') (have j := v; b j) := hb v' v hv

theorem HP_ite {α : Type} {t : St} (c c' : Prop) [Decidable c] [Decidable c'] (hc : c = c')
    {y1 y2 : HMM α} {x1 x2 : HM α} (h1 : c → HP σ g t y1 x1) (h2 : ¬c → HP σ g t y2 x2) :
    HP σ g t (if c then y1 else y2) (if c' then x1 else x2) := by
  subst hc; by_cases hc : c
  · simp only [hc, ite_true]; exact h1 hc
  · simp only [hc, ite_false]; exact h2 hc

theorem StOK_real {t u : St} (ht : StOK σ t) (h : u.real = t.real) : StOK σ u := fun r hr => ht r (h ▸ hr)

end

open Lean Elab Tactic Meta in
/-- On a goal mentioning `(E σ t).real`: rewrite it to `t.real.map _` and case on `t.real`, recording
`r.store = σ` (from the `StOK` hypothesis on `t`) in the `some r` case. -/
elab "hp_real" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let some e := tgt.find? (fun e => e.isAppOfArity ``St.real 1 && (e.appArg!.isAppOfArity ``E 2) &&
      e.appArg!.appArg!.isFVar)
    | throwError "hp_real: no (E σ t).real"
  let t := e.appArg!.appArg!
  let tS ← Term.exprToSyntax t
  evalTactic (← `(tactic| rw [E_real']))
  evalTactic (← `(tactic| rcases hrr : St.real $tS with _ | r))
  let gs ← getGoals
  match gs with
  | [g1, g2] =>
    setGoals [g2]
    evalTactic (← `(tactic| have hrs := (by assumption : StOK _ $tS) _ hrr))
    evalTactic (← `(tactic| simp only [Option.map_some]))
    let g2' ← getGoals
    setGoals [g1]
    evalTactic (← `(tactic| simp only [Option.map_none]))
    let g1' ← getGoals
    setGoals (g1' ++ g2')
  | _ => pure ()

open Lean Elab Tactic Meta in
elab "is_cr_goal" : tactic => do
  let tgt ← whnfR (← instantiateMVars (← getMainTarget))
  unless tgt.isAppOf ``CR do throwError "not a CR goal"

open Lean Elab Tactic Meta in
/-- Case on the store field of the (first) machine state of the goal, then close by `simp_all`. -/
elab "real_case" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let lctx ← getLCtx
  let some t := tgt.find? (fun e => e.isFVar && (match lctx.find? e.fvarId! with
      | some d => d.type.isConstOf ``St
      | none => false))
    | throwError "real_case: no state"
  let tS ← Term.exprToSyntax t
  evalTactic (← `(tactic| have hst := (by assumption : StOK _ $tS)))
  evalTactic (← `(tactic| simp only [StOK, E, dr] at hst ⊢))
  evalTactic (← `(tactic| (rcases hrc : St.real $tS with _ | r <;> simp_all [TTN.removeRecord])))

open Lean Elab Tactic Meta in
elab "is_stok_goal" : tactic => do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.isAppOf ``StOK do throwError "not a StOK goal"

open Lean Elab Tactic Meta in
/-- `intro`, only on a syntactic `∀`/`→` goal (never unfolding a definition such as `StOK`). -/
elab "intro_pi" : tactic => do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.isForall do throwError "intro_pi: not a pi"
  evalTactic (← `(tactic| intro))

open Lean Elab Tactic Meta in
/-- On `HP σ g t (j' a) (j a)` with `j'` a local (a join point): apply its hypothesis. -/
elab "hp_jp_use" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.isAppOfArity ``HP 6 do throwError "hp_jp_use: not HP"
  let y := tgt.getArg! 4
  unless y.getAppFn.isFVar do throwError "hp_jp_use: not a join point"
  evalTactic (← `(tactic| ((apply_assumption) <;> assumption)))

open Lean Elab Tactic Meta in
elab "is_jp_goal" : tactic => do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.isAppOfArity ``HP 6 do throwError "is_jp_goal: not HP"
  let y := tgt.getArg! 4
  unless y.isLet || y.isAppOf ``letFun do throwError "is_jp_goal: no join point"

syntax "hp_step" : tactic
macro_rules | `(tactic| hp_step) => `(tactic| first
  | contradiction
  | intro_pi
  | (is_cr_goal; cr; done)
  | ((with_reducible apply HP_get_bind); cr_rwE; (try dsimp only [E_stack, E_frames, E_pages, E_globals, E_table,
      E_tableMax, E_elems, E_datas, E_stackRem, E_gas, E_ctx, E_ret, E_balance, E_storageUsage, E_registers,
      E_regUsage, E_logs, E_totalLogLen, E_promises, E_trie, E_actions, E_dataCount, E_subsidized,
      E_memBytes, E_readByte, E_trieGet, E_dataIdOf, E_receiptReceiver]);
      (try simp only [E_real_isSome, E_readBytes, E_readLE, E_popN]))
  | hp_real
  | (with_reducible apply HP_pure_bind)
  | ((with_reducible refine HP_pure_bind' ?_ ?_); rfl)
  | (with_reducible refine HP_bind (HP_liftH ?_ ?_ (by assumption)) ?_)
  | (with_reducible refine HP_liftH ?_ ?_ (by assumption))
  | ((with_reducible refine HP_bind (HP_liftH_eq ?_ ?_ ?_ (by assumption)) ?_); rfl)
  | ((with_reducible refine HP_liftH_eq ?_ ?_ ?_ (by assumption)); rfl)
  | ((with_reducible refine HP_pure' (by assumption) ?_); rfl)
  | (with_reducible exact HP_throw (by assumption) _)
  | (with_reducible refine HP_bind (HP_realOp (by assumption) _ (by assumption) _ _ ?_ _) ?_)
  | (with_reducible refine HP_bind (HP_realHas (by assumption) (by assumption) _) ?_)
  | (with_reducible refine HP_bind (HP_realGet (by assumption) (by assumption) _) ?_)
  | ((with_reducible refine HP_bind (HP_modify _ _ ?_ ?_) ?_); first | rfl | real_case)
  | ((with_reducible refine HP_bind (HP_set _ _ ?_ ?_) ?_); rfl)
  | ((with_reducible refine HP_set _ _ ?_ ?_); rfl)
  | ((with_reducible refine HP_modify _ _ ?_ ?_); first | rfl | real_case)
  | ((with_reducible apply HP_ite _ _ ?_) <;> first | rfl | intro)
  | (exact StOK_real (by assumption) rfl)
  | (is_stok_goal; real_case)
  | (exact spec_write (by assumption) _ (by assumption))
  | (exact spec_write (by assumption) _ (by assumption) _ _)
  | (exact spec_remove (by assumption) _ (by assumption))
  | (exact spec_remove (by assumption) _ (by assumption) _ _)
  | (exact spec_read (by assumption) _ (by assumption))
  | (exact spec_read (by assumption) _ (by assumption) _ _)
  | (exact spec_has (by assumption) _ (by assumption))
  | (exact spec_has (by assumption) _ (by assumption) _ _)
  | (is_jp_goal; (with_reducible apply HP_jp) <;> intro _ _ _)
  | hp_jp_use
  | (dsimp only)
  | lk_split)

macro "hp" : tactic => `(tactic| repeat (any_goals hp_step))

end ReexecV3D3.Logged.W
