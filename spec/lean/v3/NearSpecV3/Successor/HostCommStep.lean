import NearSpecV3.Successor.HostCommArms

/-!
# W12 — machine steps and the interpreter flags (O2/O3)

`mapRes f` applies `f` to the state of a step result. Every machine helper commutes with every flag
map `setF oc og` (`F_exec`: every instruction but the two calls). Host calls are a *two-run* step:
`RR φ lower upper` says the lower run excludes (`.unmodeled`) or the upper run is the lower one with
`φ` applied to its state.

* `callHost_RR_curve`: with the curve-host selector switched on (`setF (some true) none`), a host
  call either excludes in the lower run (a curve name with no `hostCall` arm) or commutes.
* `callHost_RR_global`: with `globalActions` switched on from `false` on a trie-backed state, the
  lower run excludes every lifted name (`hostExcluded`) and commutes on the rest.
* `step_RR`, `run_RR`: the same for a whole run, from a per-call hypothesis.

Pattern: `Logged/WasmStepE.lean` (store map `E σ`), with the flag map in its place.
-/
namespace NearSpecV3.Successor.HostComm
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

/-- Fold a structure literal over `setF oc og s`'s flags back into `setF`. -/
theorem F_mk (oc og : Option Bool) (s : St) (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24) :
    St.mk a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
        (setF oc og s).globalActions (setF oc og s).curveHosts =
      setF oc og (St.mk a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
        s.globalActions s.curveHosts) := rfl

open Lean Elab Tactic Meta in
/-- On a `mapRes f X` / `Except.map f X` with `X` a call: generalize `X` and case on it, so the two
sides' `match`es on `X` and on its image split together. -/
elab "sf_gen" : tactic => do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let heads : List Name := [``sync, ``charge, ``memCopy, ``memFill, ``memInit, ``tableInit, ``execNum,
    ``execFloat, ``enter, ``doReturn, ``doBr, ``callHost, ``callFunc, ``exec, ``step]
  let ok (x : Expr) : Bool :=
    !x.hasLooseBVars && heads.any (fun n => x.isAppOf n)
  let some e := tgt.find? (fun e => (e.isAppOfArity ``mapRes 2 || e.isAppOfArity ``Except.map 5) && ok e.appArg!)
    | throwError "sf_gen: nothing to generalize"
  let (xs, g') ← g.generalize #[{ expr := e.appArg!, xName? := some `r }]
  let gs ← g'.cases xs[0]!
  replaceMainGoal (gs.map (·.mvarId)).toList

syntax "sf_step" : tactic
macro_rules | `(tactic| sf_step) => `(tactic| first
  | rfl
  | rw [F_readByte']
  | rw [F_stack]
  | rw [F_frames]
  | rw [F_pages]
  | rw [F_globals]
  | rw [F_table]
  | rw [F_tableMax]
  | rw [F_elems]
  | rw [F_datas]
  | rw [F_stackRem]
  | rw [F_gas]
  | rw [F_memBytes]
  | rw [F_readBytes]
  | rw [F_readLE]
  | (simp only [F_stack, F_frames, F_pages, F_globals, F_table,
      F_tableMax, F_elems, F_datas, F_stackRem, F_gas, F_ctx, F_ret, F_balance, F_storageUsage, F_registers,
      F_regUsage, F_logs, F_totalLogLen, F_promises, F_trie, F_actions, F_dataCount, F_real, F_subsidized,
      F_memBytes, F_readByte, F_readBytes, F_readLE,
      F_popN, F_writeBytes, F_writeByte, mapRes_cont, mapRes_fin, mapRes_abort, mapRes_unmodeled, exmap_ok,
      exmap_error, ite_true, ite_false, dite_true, dite_false, ↓reduceIte, ↓reduceDIte, F_mk])
  | sf_gen
  | lk_split
  | (rw [apply_ite (mapRes _)]; apply ite_congr rfl <;> intro)
  | (split <;> (rename_i hh; simp only [hh, ↓reduceIte, ite_true, ite_false])))
macro "sf" : tactic => `(tactic| repeat (any_goals sf_step))

section
variable {oc og : Option Bool} {s : St}
theorem F_setFrame (f : Frame) : setFrame (setF oc og s) f = setF oc og (setFrame s f) := by
  unfold setFrame; simp only [F_frames]; split <;> rfl
theorem F_pushV (v : Val) : pushV (setF oc og s) v = setF oc og (pushV s v) := rfl
theorem F_pushI32 (v : Nat) : pushI32 (setF oc og s) v = setF oc og (pushI32 s v) := rfl
theorem F_pushI64 (v : Nat) : pushI64 (setF oc og s) v = setF oc og (pushI64 s v) := rfl
theorem F_popV : popV (setF oc og s) = ((popV s).1, setF oc og (popV s).2) := rfl
theorem F_popRef : popRef (setF oc og s) = ((popRef s).1, setF oc og (popRef s).2) := by
  unfold popRef popV; simp only [F_stack]; cases s.stack.back?.getD (Val.i32 0) <;> rfl
theorem F_sync : sync (setF oc og s) = (sync s).map (setF oc og) := by
  unfold sync; sf
theorem F_charge (fee : Fee) (c : Nat) : charge (setF oc og s) fee c = mapRes (setF oc og) (charge s fee c) := by
  unfold charge; simp only [F_sync]; sf
theorem F_pushT (t : VT) (v : Nat) : pushT (setF oc og s) t v = setF oc og (pushT s t v) := by
  unfold pushT; split <;> rfl
theorem F_execFloat (op : Nat) :
    execFloat (setF oc og s) op = (execFloat s op).map (setF oc og) := by
  unfold execFloat
  by_cases h : (floatOperands op).size = 2
  · rw [if_pos h, if_pos h]
    cases hp : popN s with
    | mk b s1 =>
      cases hq : popN s1 with
      | mk a s2 =>
        simp only [hp, hq, F_popN, F_pushT]
        cases evalFloatOp op a b <;> rfl
  · rw [if_neg h, if_neg h]
    cases hp : popN s with
    | mk a s1 =>
      simp only [hp, F_popN, F_pushT]
      cases evalFloatOp op a 0 <;> rfl

macro_rules | `(tactic| sf_step) => `(tactic| simp only [F_setFrame, F_pushV, F_pushI32, F_pushI64, F_pushT, F_execFloat, F_popV, F_popRef, F_sync, F_charge])

theorem forIn_F : ∀ (l : List Nat) (f : Nat → St → St) (t : St)
    (_hf : ∀ x t, f x (setF oc og t) = setF oc og (f x t)),
    (forIn (m := Id) l (setF oc og t) fun x s => ForInStep.yield (f x s)) =
      setF oc og (forIn (m := Id) l t fun x s => ForInStep.yield (f x s))
  | [], _, _, _ => rfl
  | x :: xs, f, t, hf => by
    simp only [List.forIn_cons]
    rw [hf]
    exact forIn_F xs f _ hf

theorem F_writeLE (a w v : Nat) : writeLE (setF oc og s) a w v = setF oc og (writeLE s a w v) := by
  unfold writeLE
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  exact forIn_F _ _ _ (fun _ _ => rfl)

theorem F_memFill (d v n : Nat) : memFill (setF oc og s) d v n = mapRes (setF oc og) (memFill s d v n) := by
  unfold memFill
  rw [F_memBytes]
  split
  · rfl
  · simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
    have := forIn_F (oc := oc) (og := og) (List.range' 0 [0:n].size 1)
      (fun i s => writeByte s (d + i) (UInt8.ofNat v)) s (fun _ _ => rfl)
    simp only [bind, pure] at this ⊢
    rw [this]; rfl

macro_rules | `(tactic| sf_step) => `(tactic| simp only [F_writeLE, F_memFill])

theorem F_memCopy (d src n : Nat) : memCopy (setF oc og s) d src n = mapRes (setF oc og) (memCopy s d src n) := by
  unfold memCopy; sf

theorem F_memInit (seg d src n : Nat) : memInit (setF oc og s) seg d src n = mapRes (setF oc og) (memInit s seg d src n) := by
  unfold memInit; sf

theorem F_tableInit (seg d src n : Nat) :
    tableInit (setF oc og s) seg d src n = mapRes (setF oc og) (tableInit s seg d src n) := by
  unfold tableInit; sf

macro_rules | `(tactic| sf_step) => `(tactic| simp only [F_memCopy, F_memInit, F_tableInit])

theorem F_doReturn (p : Prepared) : doReturn p (setF oc og s) = mapRes (setF oc og) (doReturn p s) := by
  unfold doReturn; sf

macro_rules | `(tactic| sf_step) => `(tactic| simp only [F_doReturn])

theorem F_doBr (p : Prepared) (f : Frame) (l : Nat) : doBr p (setF oc og s) f l = mapRes (setF oc og) (doBr p s f l) := by
  unfold doBr; sf

macro_rules | `(tactic| sf_step) => `(tactic| simp only [F_doBr])

theorem F_enter (p : Prepared) (fi : Nat) : enter p (setF oc og s) fi = mapRes (setF oc og) (enter p s fi) := by
  unfold enter; sf

macro_rules | `(tactic| sf_step) => `(tactic| simp only [F_enter])

theorem F_execNum (op : Nat) : execNum (setF oc og s) op = (execNum s op).map (setF oc og) := by
  unfold execNum; sf

macro_rules | `(tactic| sf_step) => `(tactic| simp only [F_execNum])
macro_rules | `(tactic| sf_step) => `(tactic| first | rw [F_popN] | rw [F_popRef] | rw [F_popV])

theorem F_topCount : topCount (setF oc og s) = topCount s := rfl
end

/-! ## Two-run results

`RR X φ lower upper`: the upper run is the lower one mapped by `φ`, or the lower run stopped with an
exclusion message in `X` (the only messages where the two runs part). -/

def RR (X : String → Prop) (φ : St → St) (r r' : Res) : Prop :=
  r' = mapRes φ r ∨ ∃ w, X w ∧ r = .unmodeled w

theorem RR.map {X : String → Prop} {φ : St → St} (r : Res) : RR X φ r (mapRes φ r) := Or.inl rfl

theorem mapSt_run (φ : St → St) (h : HM Unit) (t : St) (hc : CR φ h h) : h.run (φ t) = mapSt φ (h.run t) := hc.h t

/-- The lower run's message when a curve name has no signed arm (`callHost`). -/
def curveMsg (name : String) : String := s!"host function {name} not modelled in D3α"

/-- The lower run's message when a lifted promise host is called on a trie-backed run (`callHost`). -/
def gaMsg (name : String) : String := s!"out-of-domain host function {name} called"

/-- O2's parting messages: a curve name that has a successor arm. -/
def XC (w : String) : Prop := ∃ name h, cryptoHostCall name = some h ∧ w = curveMsg name

/-- O3's parting messages: a name the global-actions flag lifts. -/
def XG (w : String) : Prop := ∃ name, globalPromiseHosts.contains name = true ∧ w = gaMsg name

/-- **O2, host call.** Switching the curve-host selector on: a host call is the lower call with the
selector set, or the lower call stopped at a curve name the successor table decides. -/
theorem callHost_RR_curve (s : St) (name : String) :
    RR XC (setF (some true) none) (callHost s name) (callHost (setF (some true) none s) name) := by
  unfold callHost
  rw [F_real, F_globalActions_none]
  by_cases hg : (s.real.isSome && realOodHosts.contains name &&
      !(s.globalActions && globalPromiseHosts.contains name)) = true
  · rw [if_pos hg, if_pos hg]; exact Or.inl rfl
  rw [if_neg hg, if_neg hg, F_sync]
  cases hsy : sync s with
  | error e => exact Or.inl rfl
  | ok s' =>
    simp only [exmap_ok]
    unfold dispatchArm
    cases hc : hostCall name with
    | some h =>
      simp only
      left
      rw [mapSt_run _ h s' (CR_hostCall_none (some true) name h hc)]
      cases h.run s' with
      | ok a t => rfl
      | error e t => simp only [mapSt]; split <;> rfl
    | none =>
      simp only
      have hcs : (setF (some true) none s').curveHosts = true := rfl
      rw [hcs]
      cases hch : s'.curveHosts
      · simp only [ite_true, Bool.false_eq_true, ite_false]
        cases hcc : cryptoHostCall name with
        | none => exact Or.inl rfl
        | some h => exact Or.inr ⟨_, ⟨name, h, hcc, rfl⟩, rfl⟩
      · simp only [ite_true]
        cases hcc : cryptoHostCall name with
        | none => exact Or.inl rfl
        | some h =>
          simp only
          left
          rw [mapSt_run _ h s' (CR_cryptoHostCall (some true) none name h hcc)]
          cases h.run s' with
          | ok a t => rfl
          | error e t => simp only [mapSt]; split <;> rfl

theorem globalPromiseHosts_realOod (name : String) (h : globalPromiseHosts.contains name = true) :
    realOodHosts.contains name = true := by
  have hall := globalPromiseHosts_subset_realOodHosts
  rw [List.all_eq_true] at hall
  exact hall name (List.contains_iff_mem.mp h)

/-- **O3, host call.** Switching `globalActions` on, from a trie-backed lower state with the flag
off: the lower call excludes every lifted name; every other call commutes. -/
theorem callHost_RR_global (s : St) (name : String)
    (hg : s.globalActions = false) (hr : s.real.isSome = true) :
    RR XG (setF none (some true)) (callHost s name) (callHost (setF none (some true) s) name) := by
  unfold callHost
  have hga : (setF none (some true) s).globalActions = true := rfl
  rw [F_real, hga, hg, hr]
  by_cases hro : realOodHosts.contains name = true
  · rw [if_pos (by rw [hro]; rfl)]
    cases hgp : globalPromiseHosts.contains name
    · rw [if_pos (by first | (rw [hro]; rfl) | rfl)]; exact Or.inl rfl
    · exact Or.inr ⟨_, ⟨name, hgp, rfl⟩, rfl⟩
  have hgp : globalPromiseHosts.contains name = false := by
    cases h : globalPromiseHosts.contains name
    · rfl
    · exact absurd (globalPromiseHosts_realOod name h) hro
  have hro' : realOodHosts.contains name = false := by simpa using hro
  rw [if_neg (by rw [hro']; simp), if_neg (by rw [hro']; simp)]
  rw [F_sync]
  cases hsy : sync s with
  | error e => exact Or.inl rfl
  | ok s' =>
    simp only [exmap_ok]
    have hd : dispatchArm (setF none (some true) s') name = dispatchArm s' name := rfl
    rw [hd]
    cases hc : dispatchArm s' name with
    | none => exact Or.inl rfl
    | some h =>
      simp only
      left
      rw [mapSt_run _ h s' (CR_dispatchArm none (some true) s' name h hc hgp)]
      cases h.run s' with
      | ok a t => rfl
      | error e t => simp only [mapSt]; split <;> rfl

/-! ## Instructions, steps and runs, from a per-call hypothesis -/

/-- The per-call hypothesis: on every lower state satisfying `Q`, a host call is a two-run step;
and `Q` survives the lower run's non-host moves. For O2 `Q` is `True`; for O3 it is "flag off and
trie-backed". -/
structure CallHyp (X : String → Prop) (oc og : Option Bool) (Q : St → Prop) : Prop where
  call : ∀ s name, Q s → RR X (setF oc og) (callHost s name) (callHost (setF oc og s) name)
  frame : ∀ s f, Q s → Q (setFrame s f)
  pop : ∀ s, Q s → Q (popN s).2
  charge : ∀ s fee c s', Q s → charge s fee c = .cont s' → Q s'

section
variable {X : String → Prop} {oc og : Option Bool} {Q : St → Prop}

theorem RR_callFunc (H : CallHyp X oc og Q) (cfg : NearCfg) (p : Prepared)
    (s : St) (fi : Nat) (hq : Q s) :
    RR X (setF oc og) (callFunc cfg p s fi) (callFunc cfg p (setF oc og s) fi) := by
  unfold callFunc
  split
  · exact H.call s _ hq
  · rw [F_enter]; exact RR.map _

set_option maxHeartbeats 10000000 in
theorem RR_exec (H : CallHyp X oc og Q) (cfg : NearCfg) (p : Prepared)
    (s : St) (f : Frame) (pf : PFunc) (i : Instr) (hq : Q s) :
    RR X (setF oc og) (exec cfg p s f pf i) (exec cfg p (setF oc og s) f pf i) := by
  cases i with
  | call fi =>
    simp only [exec]; rw [F_setFrame]
    exact RR_callFunc H cfg p _ fi (H.frame _ _ hq)
  | callIndirect ty x =>
    simp only [exec]
    rw [F_popN]; simp only [F_table]
    split
    · exact RR.map _
    · exact RR.map _
    · rename_i fi hfi
      split
      · split
        · exact RR.map _
        · rw [F_setFrame]; exact RR_callFunc H cfg p _ fi (H.frame _ _ (H.pop _ hq))
      · exact Or.inl rfl
  | _ => left; simp only [exec]; sf

theorem RR_step (H : CallHyp X oc og Q) (cfg : NearCfg) (p : Prepared)
    (s : St) (hq : Q s) :
    RR X (setF oc og) (step cfg p s) (step cfg p (setF oc og s)) := by
  unfold step
  rw [F_frames]
  split
  · exact RR.map _
  rename_i f fs hf
  split
  · exact Or.inl rfl
  rename_i pf hpf
  split
  · exact Or.inl rfl
  rename_i ins hins
  split
  · exact Or.inl rfl
  · exact RR_exec H cfg p s f pf ins hq
  · rename_i k fee hg
    rw [F_topCount, F_charge]
    cases hc : charge s fee (if k = .linear then topCount s else 0) with
    | cont s' =>
      simp only [mapRes_cont]
      exact RR_exec H cfg p s' f pf ins (H.charge _ _ _ _ hq hc)
    | fin s' => exact RR.map _
    | abort s' e => exact RR.map _
    | unmodeled w => exact Or.inl rfl

/-- **A whole run** is a two-run step, given that `Q` survives the lower run's continuing steps. -/
theorem RR_run (H : CallHyp X oc og Q) (cfg : NearCfg) (p : Prepared)
    (Hs : ∀ s s', Q s → step cfg p s = .cont s' → Q s') :
    ∀ n s, Q s → RR X (setF oc og) (run cfg p n s) (run cfg p n (setF oc og s))
  | 0, _, _ => Or.inl rfl
  | n + 1, s, hq => by
    unfold run
    rcases RR_step H cfg p s hq with he | ⟨w, hw, he⟩
    · rw [he]
      cases hs : step cfg p s with
      | cont s' => exact RR_run H cfg p Hs n s' (Hs s s' hq hs)
      | fin s' => exact RR.map _
      | abort s' e => exact RR.map _
      | unmodeled w => exact Or.inl rfl
    · rw [he]; exact Or.inr ⟨w, hw, rfl⟩

/-- Two-run relation on `callEntry`'s result. -/
def ER (X : String → Prop) (φ : St → St) (x y : Except String (St × Option String)) : Prop :=
  y = x.map (fun q => (φ q.1, q.2)) ∨ ∃ w, X w ∧ x = .error w

/-- `callEntry` after its state reset (`callEntry_eq_core` is `rfl`). -/
def entryCore (cfg : NearCfg) (p : Prepared) (fuel : Nat) (s0 : St) (fi : Nat) :
    Except String (St × Option String) :=
  let r := match enter p s0 fi with
    | .cont s => run cfg p fuel s
    | r => r
  match r with
  | .fin s => (sync s).map (·, none)
  | .abort s e => (sync s).map (·, some e)
  | .unmodeled why => .error why
  | .cont _ => .error "cont"

/-- `callEntry`'s state reset. -/
def entryReset (s : St) : St := { s with gas := { s.gas with g := s.gas.remaining }, stack := #[], frames := [] }

theorem callEntry_eq_core (cfg : NearCfg) (p : Prepared) (fuel : Nat) (s : St) (fi : Nat) :
    callEntry cfg p fuel s fi = entryCore cfg p fuel (entryReset s) fi := rfl

theorem entryReset_F (s : St) : entryReset (setF oc og s) = setF oc og (entryReset s) := rfl

theorem ER_entryCore (H : CallHyp X oc og Q) (cfg : NearCfg) (p : Prepared) (fuel : Nat) (s0 : St) (fi : Nat)
    (Hs : ∀ s s', Q s → step cfg p s = .cont s' → Q s')
    (He : ∀ s s', Q s → enter p s fi = .cont s' → Q s') (hq : Q s0) :
    ER X (setF oc og) (entryCore cfg p fuel s0 fi) (entryCore cfg p fuel (setF oc og s0) fi) := by
  unfold entryCore
  simp only []
  rw [F_enter]
  cases hen : enter p s0 fi with
  | cont s1 =>
    simp only [mapRes_cont]
    rcases RR_run H cfg p Hs fuel s1 (He s0 s1 hq hen) with he | ⟨w, hw, he⟩
    · rw [he]
      cases run cfg p fuel s1 with
      | fin s2 => left; simp only [mapRes_fin, F_sync]; cases sync s2 <;> rfl
      | abort s2 e => left; simp only [mapRes_abort, F_sync]; cases sync s2 <;> rfl
      | unmodeled w => left; rfl
      | cont s2 => left; rfl
    · rw [he]; exact Or.inr ⟨w, hw, rfl⟩
  | fin s1 => left; simp only [mapRes_fin, F_sync]; cases sync s1 <;> rfl
  | abort s1 e => left; simp only [mapRes_abort, F_sync]; cases sync s1 <;> rfl
  | unmodeled w => left; rfl

theorem ER_callEntry (H : CallHyp X oc og Q) (cfg : NearCfg) (p : Prepared) (fuel : Nat) (s : St) (fi : Nat)
    (Hs : ∀ s s', Q s → step cfg p s = .cont s' → Q s')
    (He : ∀ s s', Q s → enter p s fi = .cont s' → Q s') (hq : Q (entryReset s)) :
    ER X (setF oc og) (callEntry cfg p fuel s fi) (callEntry cfg p fuel (setF oc og s) fi) := by
  rw [callEntry_eq_core, callEntry_eq_core, entryReset_F]
  exact ER_entryCore H cfg p fuel _ fi Hs He hq
end

#print axioms callHost_RR_curve
#print axioms callHost_RR_global
#print axioms RR_run
#print axioms ER_callEntry

end NearSpecV3.Successor.HostComm
