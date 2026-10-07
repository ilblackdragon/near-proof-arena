import ReexecV3D3.Logged.WasmRun
import ReexecV3D3.Logged.D2Check
import ReexecV3D3.Logged.Runtime.D3Check
import ReexecV3D3.Logged.D3L

/-! # `functionCallL` = `functionCall`, `checkD3L` = `checkD3` -/

namespace ReexecV3D3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.D3 NearSpecV3.Wasm

section
variable {s : HStore} {root : Bytes}

theorem ev_getB_codeOf (e : Env) (h : Bytes) : LM.ev s root (LM.getB h) = .ok ((e.ws s).codeOf h) := rfl

theorem ev_codeAvailableL (c : ActCtx) (st : ActSt) (h : Bytes) :
    LM.ev s root (codeAvailableL c st h) = .ok (codeAvailable (c.ws s) (st.wt (preT s root)) h) := by
  unfold codeAvailableL codeAvailable
  cases (st.deploys ++ c.deployed).find? (fun code => sha256 code == h) <;> rfl

/-- The WASM call: the mirror's result is the original's with the states' store erased. -/
theorem R_bind_runCallL {β α : Type} (cfg : NearCfg) (code : ByteArray) (m : String) (ctx : CallCtx)
    (fuel : Nat) (realM : TTN.RealStore) {k : Run → LM β} {o : Except String α} {φ : β → α}
    (h : R s root (k (W.mapRun (W.E W.dummy) (runCall cfg code m ctx fuel true false
      (some { realM with store := fun hb => (hGet s (ofBA hb)).map toBA })))) o φ) :
    R s root (LM.lift (W.runCallL cfg code m ctx fuel true false (W.dr realM)) >>= k) o φ := by
  refine R_bind_ok ?_ h
  rw [LM.ev_lift]
  exact W.runCallL_spec (σ := fun hb => (hGet s (ofBA hb)).map toBA) (fun _ => rfl) cfg code m ctx fuel true
    false { realM with store := fun hb => (hGet s (ofBA hb)).map toBA } rfl

end

section
variable {s : HStore} {root : Bytes}

/-- `ForInStep` with the revealed trie put back into an `Ovl × Nat` loop state. -/
def stepWt (T : PTrie) : ForInStep (Ovl × Nat) → ForInStep (Ovl × Nat)
  | .done p => .done (p.1.wt T, p.2)
  | .yield p => .yield (p.1.wt T, p.2)

theorem R_forIn_ovl {γ : Type} (l : List γ) (p : Ovl × Nat)
    {f : γ → Ovl × Nat → Except String (ForInStep (Ovl × Nat))} {f' : γ → Ovl × Nat → LM (ForInStep (Ovl × Nat))}
    (h : ∀ x q, R s root (f' x q) (f x (q.1.wt (preT s root), q.2)) (stepWt (preT s root))) :
    R s root (forIn l p f') (forIn l (p.1.wt (preT s root), p.2) f) (fun q => (q.1.wt (preT s root), q.2)) := by
  induction l generalizing p with
  | nil => exact R_pure rfl
  | cons x xs ih =>
    simp only [List.forIn_cons]
    apply R_bind (h x p)
    intro r
    cases r with
    | done q => exact R_pure rfl
    | yield q => exact ih q

theorem R_forIn_ovl_arr {γ : Type} (l : Array γ) (o : Ovl) (n : Nat)
    {f : γ → Ovl × Nat → Except String (ForInStep (Ovl × Nat))} {f' : γ → Ovl × Nat → LM (ForInStep (Ovl × Nat))}
    (h : ∀ x q, R s root (f' x q) (f x (q.1.wt (preT s root), q.2)) (stepWt (preT s root))) :
    R s root (forIn l (o, n) f') (forIn l (o.wt (preT s root), n) f) (fun q => (q.1.wt (preT s root), q.2)) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact R_forIn_ovl l.toList (o, n) h

theorem foldl_hom_wt_arr {β : Type} {t : PTrie} {g : Ovl → β → Ovl} {l : Array β} {init oinit : Ovl}
    (h1 : oinit = init.wt t) (hg : ∀ o b, g (o.wt t) b = (g o b).wt t) :
    Array.foldl g oinit l = (Array.foldl g init l).wt t := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]; exact foldl_hom_wt h1 hg

theorem R_forIn_ovl_arr' {γ : Type} (l : Array γ) (o : Ovl) (n : Nat) {oO : Ovl} (hO : oO = o.wt (preT s root))
    {f : γ → Ovl × Nat → Except String (ForInStep (Ovl × Nat))} {f' : γ → Ovl × Nat → LM (ForInStep (Ovl × Nat))}
    (h : ∀ x q, R s root (f' x q) (f x (q.1.wt (preT s root), q.2)) (stepWt (preT s root))) :
    R s root (forIn l (o, n) f') (forIn l (oO, n) f) (fun q => (q.1.wt (preT s root), q.2)) := by
  subst hO; exact R_forIn_ovl_arr l o n h

end

macro_rules | `(tactic| lk_step) => `(tactic| apply R_bind_ok (ev_codeAvailableL _ _ _))
macro_rules | `(tactic| lk_step) => `(tactic| apply R_bind_ok (LM.ev_getB _ _ _))

open Lean in
/-- The closed `Exec.runCall …` subterms of `e`. -/
partial def collectRunCall (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := if e.isAppOfArity ``NearSpecV3.Wasm.runCall 8 && !e.hasLooseBVars then acc.push e else acc
  match e with
  | .app f a => collectRunCall a (collectRunCall f acc)
  | .lam _ t b _ => collectRunCall b (collectRunCall t acc)
  | .forallE _ t b _ => collectRunCall b (collectRunCall t acc)
  | .letE _ t v b _ => collectRunCall b (collectRunCall v (collectRunCall t acc))
  | .mdata _ b => collectRunCall b acc
  | .proj _ _ b => collectRunCall b acc
  | _ => acc

open Lean Elab Tactic Meta in
/-- Generalize the `Exec.runCall …` of the goal (both sides must carry the same one). -/
elab "gen_runCall" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let all := collectRunCall tgt
  unless tgt.isAppOf ``R && (collectRunCall tgt.getAppArgs[4]!).size ≥ 1 &&
      (collectRunCall tgt.getAppArgs[5]!).size ≥ 1 do
    throwError "gen_runCall: not on both sides"
  let e := (collectRunCall tgt.getAppArgs[4]!)[0]!
  -- the original's copies are equal up to its own `match` auxiliaries: replace them by the mirror's
  let mut g ← getMainGoal
  for b in all do
    if b != e then
      unless (← isDefEq b e) do throwError "gen_runCall: the runCall terms differ"
  let tgt' := tgt.replace (fun x => if x.isAppOfArity ``NearSpecV3.Wasm.runCall 8 && !x.hasLooseBVars then some e else none)
  g ← g.replaceTargetDefEq tgt'
  let (fvs, g2) ← g.generalize #[{ expr := e, xName? := some `rr }]
  replaceMainGoal [g2]
  withMainContext do
    let x := mkIdent (← fvs[0]!.getUserName)
    evalTactic (← `(tactic| cases $x:ident))
    evalTactic (← `(tactic| all_goals (try dsimp only [W.mapRun])))

/-- Case on the WASM call's result (`gen_runCall`). -/
macro "lk_run" : tactic => `(tactic| gen_runCall)

open Lean Elab Tactic Meta in
/-- The original side is (now) a `match` on an `Exec.runCall …`. -/
elab "orig_at_runCall" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.isAppOf ``R do throwError "no"
  let o := tgt.getAppArgs[5]!
  let env ← getEnv
  unless isMatcherAppCore env o do throwError "orig not a match"
  let some m ← matchMatcherApp? o | throwError "no"
  unless m.discrs.any (fun d => d.isAppOf ``NearSpecV3.Wasm.runCall) do throwError "orig not at runCall"

open Lean Elab Tactic Meta in
/-- On a goal mentioning `E dummy t` (a final machine state of the mirror): unfold the erasure and case
on `t`'s store field, so the store disappears from both sides. -/
elab "lk_destr" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some e := tgt.find? (fun x => x.isAppOfArity ``W.E 2 && x.appArg!.isFVar)
    | throwError "lk_destr: no erased state"
  let tS ← Term.exprToSyntax e.appArg!
  evalTactic (← `(tactic| dsimp only [W.E, W.dr]))
  evalTactic (← `(tactic| (cases hrl : St.real $tS <;> dsimp only [Option.map])))

theorem ovl_write_hom {t : PTrie} (o : Ovl) (b : ByteArray × Option ByteArray) :
    (match b.snd with
      | some v => (o.wt t).set (ofBA b.fst) (ofBA v)
      | none => (o.wt t).remove (ofBA b.fst)) =
    (match b.snd with
      | some v => o.set (ofBA b.fst) (ofBA v)
      | none => o.remove (ofBA b.fst)).wt t := by
  obtain ⟨k, v⟩ := b; cases v <;> rfl

macro_rules | `(tactic| lk_eq) => `(tactic| (apply foldl_hom_wt_arr; (first | rfl | lk_eq); (intro o b; exact ovl_write_hom o b)))

macro "lk3" : tactic => `(tactic| repeat (any_goals (first | lk_run | lk_destr | (orig_at_runCall; apply R_bind_runCallL; try dsimp only) | (refine R_bind (R_forIn_ovl_arr' _ _ _ ?_ (fun _ _ => ?_)) ?_) | lk_step)))

section
variable {s : HStore} {root : Bytes}

set_option maxHeartbeats 10000000 in
theorem R_functionCall (cfg : NearCfg) (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) :
    R s root (functionCallL cfg c st ar b) (functionCall cfg (c.ws s) (st.wt (preT s root)) ar b)
      (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold functionCall functionCallL
  simp only [Env.codeOf]
  lk3

end

section
variable {s : HStore} {root : Bytes}

theorem R_functionCallD3 (cfg : NearCfg) (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) :
    R s root (functionCallD3L cfg c st ar b) (functionCallD3 cfg (c.ws s) (st.wt (preT s root)) ar b)
      (fun p => (p.1.wt (preT s root), p.2)) := by
  have h := R_functionCall (s := s) (root := root) cfg c st ar b
  unfold R at h ⊢
  unfold functionCallD3 functionCallD3L
  rw [h]
  show _ = (SM.run (hGet s) (SM.tryCatch (functionCallL cfg c st ar b root) _)).map _
  rw [SM.run_tryCatch]
  unfold LM.ev
  cases SM.run (hGet s) (functionCallL cfg c st ar b root) with
  | ok a => rfl
  | error e =>
    simp only [Except.map]
    split <;> rfl

theorem HooksR_d3 (cfg : NearCfg) : HooksR s root s (d3Hooks cfg) (d3HooksL cfg) := by
  intro c st ar b
  exact R_functionCallD3 cfg c st ar b

end

end ReexecV3D3.Logged

namespace ReexecV3D3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.D3

/-- **The logged D3 checker computes `checkD3`.** -/
theorem checkD3L_eq (cb wb : Bytes) : SM.run (storesOf wb) (checkD3L cb wb) = checkD3 cb wb := by
  have h := checkD2Core_logged (d3Hooks Wasm.pv86) (d3HooksL Wasm.pv86) (fun _ _ _ => HooksR_d3 _) true cb wb
    (some gAlpha)
  unfold RK at h; exact h.symm

end ReexecV3D3.Logged
