import NearSpecV3.Logged.WasmCRHostCall
import NearSpecV3.Logged.Lockstep

/-!
# Machine steps that call no storage host function commute with `E σ` (`step_E`)

`mapRes f` applies `f` to the state of a step result. Equivariance lemmas for the machine helpers,
then `exec`, `callHost` (non-storage names, from `CR_hostCall`) and `step` (`stepPre = none`).
-/
namespace NearSpecV3.Logged.W
open NearSpecV3.Wasm

def mapRes (f : St → St) : Res → Res
  | .cont s => .cont (f s)
  | .fin s => .fin (f s)
  | .abort s e => .abort (f s) e
  | .unmodeled w => .unmodeled w


section
variable (f : St → St)
theorem mapRes_cont (s : St) : mapRes f (.cont s) = .cont (f s) := rfl
theorem mapRes_fin (s : St) : mapRes f (.fin s) = .fin (f s) := rfl
theorem mapRes_abort (s : St) (e : String) : mapRes f (.abort s e) = .abort (f s) e := rfl
theorem mapRes_unmodeled (w : String) : mapRes f (.unmodeled w) = .unmodeled w := rfl
theorem exmap_ok (s : St) : Except.map (ε := String) f (.ok s) = .ok (f s) := rfl
theorem exmap_error (e : String) : Except.map (ε := String) f (.error e) = .error e := rfl
end

/-- Fold a structure literal over `E σ s`'s store field back into `E σ`. -/
theorem E_mk (σ : TTN.Store) (s : St) (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a24) :
    St.mk a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 (E σ s).real a24 =
      E σ (St.mk a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 s.real a24) := rfl

open Lean Elab Tactic Meta in
/-- On a `mapRes f X` / `Except.map f X` with `X` a call (not a `match`/`if`): generalize `X` and
case on it, so the two sides' `match`es on `X` and on its image split together. -/
elab "se_gen" : tactic => do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let heads : List Name := [``sync, ``charge, ``memCopy, ``memFill, ``memInit, ``tableInit, ``execNum,
    ``enter, ``doReturn, ``doBr, ``callHost, ``callFunc, ``exec, ``step]
  let ok (x : Expr) : Bool :=
    !x.hasLooseBVars && heads.any (fun n => x.isAppOf n)
  let some e := tgt.find? (fun e => (e.isAppOfArity ``mapRes 2 || e.isAppOfArity ``Except.map 5) && ok e.appArg!)
    | throwError "se_gen: nothing to generalize"
  let (xs, g') ← g.generalize #[{ expr := e.appArg!, xName? := some `r }]
  let gs ← g'.cases xs[0]!
  replaceMainGoal (gs.map (·.mvarId)).toList

syntax "se_step" : tactic
macro_rules | `(tactic| se_step) => `(tactic| first
  | rfl
  | rw [E_readByte']
  | rw [E_trieGet']
  | rw [E_dataIdOf']
  | rw [E_receiptReceiver']
  | rw [E_stack]
  | rw [E_frames]
  | rw [E_pages]
  | rw [E_globals]
  | rw [E_table]
  | rw [E_tableMax]
  | rw [E_elems]
  | rw [E_datas]
  | rw [E_stackRem]
  | rw [E_gas]
  | rw [E_ctx]
  | rw [E_ret]
  | rw [E_balance]
  | rw [E_storageUsage]
  | rw [E_registers]
  | rw [E_regUsage]
  | rw [E_logs]
  | rw [E_totalLogLen]
  | rw [E_promises]
  | rw [E_trie]
  | rw [E_actions]
  | rw [E_dataCount]
  | rw [E_subsidized]
  | rw [E_memBytes]
  | rw [E_real_isSome]
  | rw [E_readBytes]
  | rw [E_readLE]
  | (simp only [E_stack, E_frames, E_pages, E_globals, E_table,
      E_tableMax, E_elems, E_datas, E_stackRem, E_gas, E_ctx, E_ret, E_balance, E_storageUsage, E_registers,
      E_regUsage, E_logs, E_totalLogLen, E_promises, E_trie, E_actions, E_dataCount, E_subsidized,
      E_memBytes, E_readByte, E_trieGet, E_dataIdOf, E_receiptReceiver, E_real_isSome, E_readBytes, E_readLE,
      E_popN, E_writeBytes, E_writeByte, mapRes_cont, mapRes_fin, mapRes_abort, mapRes_unmodeled, exmap_ok, exmap_error, ite_true, ite_false, dite_true, dite_false,
      ↓reduceIte, ↓reduceDIte, E_mk])
  | se_gen
  | lk_split
  | (rw [apply_ite (mapRes _)]; apply ite_congr rfl <;> intro)
  | (split <;> (rename_i hh; simp only [hh, ↓reduceIte, ite_true, ite_false])))
macro "se" : tactic => `(tactic| repeat (any_goals se_step))

section
variable {σ : TTN.Store} {s : St}
theorem E_setFrame (f : Frame) : setFrame (E σ s) f = E σ (setFrame s f) := by
  unfold setFrame; simp only [E_frames]; split <;> rfl
theorem E_pushV (v : Val) : pushV (E σ s) v = E σ (pushV s v) := rfl
theorem E_pushI32 (v : Nat) : pushI32 (E σ s) v = E σ (pushI32 s v) := rfl
theorem E_pushI64 (v : Nat) : pushI64 (E σ s) v = E σ (pushI64 s v) := rfl
theorem E_popV : popV (E σ s) = ((popV s).1, E σ (popV s).2) := rfl
theorem E_popRef : popRef (E σ s) = ((popRef s).1, E σ (popRef s).2) := by
  unfold popRef popV; simp only [E_stack]; cases s.stack.back?.getD (Val.i32 0) <;> rfl
theorem E_sync : sync (E σ s) = (sync s).map (E σ) := by
  unfold sync; se
theorem E_charge (fee : Fee) (c : Nat) : charge (E σ s) fee c = mapRes (E σ) (charge s fee c) := by
  unfold charge; simp only [E_sync]; se

macro_rules | `(tactic| se_step) => `(tactic| simp only [E_setFrame, E_pushV, E_pushI32, E_pushI64, E_popV, E_popRef, E_sync, E_charge])

theorem forIn_E {σ} : ∀ (l : List Nat) (f : Nat → St → St) (t : St)
    (_hf : ∀ x t, f x (E σ t) = E σ (f x t)),
    (forIn (m := Id) l (E σ t) fun x s => ForInStep.yield (f x s)) =
      E σ (forIn (m := Id) l t fun x s => ForInStep.yield (f x s))
  | [], _, _, _ => rfl
  | x :: xs, f, t, hf => by
    simp only [List.forIn_cons]
    rw [hf]
    exact forIn_E xs f _ hf

theorem E_writeLE (a w v : Nat) : writeLE (E σ s) a w v = E σ (writeLE s a w v) := by
  unfold writeLE
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  exact forIn_E _ _ _ (fun _ _ => rfl)

theorem E_memFill (d v n : Nat) : memFill (E σ s) d v n = mapRes (E σ) (memFill s d v n) := by
  unfold memFill
  rw [E_memBytes]
  split
  · rfl
  · simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
    have := forIn_E (σ := σ) (List.range' 0 [0:n].size 1) (fun i s => writeByte s (d + i) (UInt8.ofNat v)) s
      (fun _ _ => rfl)
    simp only [bind, pure] at this ⊢
    rw [this]; rfl

macro_rules | `(tactic| se_step) => `(tactic| simp only [E_writeLE, E_memFill])

theorem E_memCopy (d src n : Nat) : memCopy (E σ s) d src n = mapRes (E σ) (memCopy s d src n) := by
  unfold memCopy; se

theorem E_memInit (seg d src n : Nat) : memInit (E σ s) seg d src n = mapRes (E σ) (memInit s seg d src n) := by
  unfold memInit; se

theorem E_tableInit (seg d src n : Nat) :
    tableInit (E σ s) seg d src n = mapRes (E σ) (tableInit s seg d src n) := by
  unfold tableInit; se

macro_rules | `(tactic| se_step) => `(tactic| simp only [E_memCopy, E_memInit, E_tableInit])

theorem E_doReturn (p : Prepared) : doReturn p (E σ s) = mapRes (E σ) (doReturn p s) := by
  unfold doReturn; se

macro_rules | `(tactic| se_step) => `(tactic| simp only [E_doReturn])

theorem E_doBr (p : Prepared) (f : Frame) (l : Nat) : doBr p (E σ s) f l = mapRes (E σ) (doBr p s f l) := by
  unfold doBr; se

macro_rules | `(tactic| se_step) => `(tactic| simp only [E_doBr])

theorem E_enter (p : Prepared) (fi : Nat) : enter p (E σ s) fi = mapRes (E σ) (enter p s fi) := by
  unfold enter; se

macro_rules | `(tactic| se_step) => `(tactic| simp only [E_enter])

theorem E_execNum (op : Nat) : execNum (E σ s) op = (execNum s op).map (E σ) := by
  unfold execNum; se

theorem mapSt_E_run (h : HM Unit) (t : St) (hc : CR σ h h) : h.run (E σ t) = mapSt (E σ) (h.run t) := hc.h t

theorem E_callHost (name : String) (hn : storageHosts.contains name = false) :
    callHost (E σ s) name = mapRes (E σ) (callHost s name) := by
  unfold callHost
  rw [E_real_isSome]
  split
  · rfl
  rw [E_sync]
  generalize sync s = r
  cases r with
  | error e => rfl
  | ok s' =>
    simp only [exmap_ok]
    cases hc : hostCall name with
    | none => rfl
    | some h =>
      simp only
      rw [(CR_hostCall σ name h hc hn).h s']
      cases h.run s' with
      | ok a t => rfl
      | error e t => simp only [mapSt]; split <;> rfl

theorem E_callFunc (cfg : NearCfg) (p : Prepared) (fi : Nat) (h : callPre p s fi = none) :
    callFunc cfg p (E σ s) fi = mapRes (E σ) (callFunc cfg p s fi) := by
  unfold callFunc
  split
  · rename_i hfi
    unfold callPre at h; simp only [hfi, ↓reduceDIte] at h
    split at h
    · cases h
    · rename_i hc; exact E_callHost _ (by simpa using hc)
  · exact E_enter p fi

macro_rules | `(tactic| se_step) => `(tactic| simp only [E_execNum])
macro_rules | `(tactic| se_step) => `(tactic| first | rw [E_popN] | rw [E_popRef] | rw [E_popV])

set_option maxHeartbeats 10000000 in
theorem E_exec (cfg : NearCfg) (p : Prepared) (f : Frame) (pf : PFunc) (i : Instr)
    (h : execPre p s f i = none) :
    exec cfg p (E σ s) f pf i = mapRes (E σ) (exec cfg p s f pf i) := by
  cases i with
  | call fi =>
    simp only [exec]; rw [E_setFrame]
    exact E_callFunc cfg p fi h
  | callIndirect ty x =>
    simp only [exec, execPre] at h ⊢
    rw [E_popN]; simp only [E_table]
    split
    · rfl
    · rfl
    · rename_i fi hfi
      simp only [hfi] at h
      split
      · rename_i ft want hft hw
        simp only [hft, hw] at h
        split
        · rfl
        · rename_i hne
          simp only [hne] at h
          rw [E_setFrame]; exact E_callFunc cfg p fi h
      · rfl
  | _ => simp only [exec]; se

theorem E_topCount : topCount (E σ s) = topCount s := rfl

theorem E_step (cfg : NearCfg) (p : Prepared) (h : stepPre p s = none) :
    step cfg p (E σ s) = mapRes (E σ) (step cfg p s) := by
  unfold stepPre at h; unfold step
  rw [E_frames]
  split
  · rfl
  rename_i f fs hf
  simp only [hf] at h
  split
  · rfl
  rename_i pf hpf
  simp only [hpf] at h
  split
  · rfl
  rename_i ins hins
  simp only [hins] at h
  split
  · rfl
  · rename_i hg; simp only [hg] at h; exact E_exec cfg p f pf ins h
  · rename_i k fee hg
    simp only [hg] at h
    rw [E_topCount, E_charge]
    generalize charge s fee (if k = .linear then topCount s else 0) = r at h ⊢
    cases r with
    | cont s' => exact E_exec cfg p f pf ins h
    | _ => rfl

end
end NearSpecV3.Logged.W
