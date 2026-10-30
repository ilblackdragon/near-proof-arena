import NearSpecV3.Successor.HostQStep
import NearSpecV3.Successor.TierO3

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O3 — the global-actions switch at the call level

The interpreter reads `globalActions` only through the state flag `St.globalActions`, which
`instantiate` copies from the configuration. On a trie-backed call (`real = some _`, which is what
`vmCall` passes) with the flag off:

* `instantiate_ga`, `instantiate_eq_instX`, `lowQ_inst`: instantiation commutes with the flag, and its result has the
  flag of the configuration and an empty action log.
* `runCall_global`, `runCallWithLimits_global`: the run with the flag on is the run with it off with
  the flag set in its final state, or the run with it off stopped at a lifted promise host
  (`XG`), which `runCall` reports as `unmodeled out-of-domain host function NAME called`.
* `runCall_globalG`, `runCallWithLimits_lowQ`, `vmCall_lowQ`: the final state of the run with the flag off satisfies `LowQ` (in
  particular its action log holds no raw action, `managerGlobal_eq_manager`).
* `lineOutcome_XG`: each of the ten parting lines is an exclusion of the recorded call.
* `vmF_global`: the recorded call's `vm` at the two flags is a two-run pair (`VmF`, `TierO2.lean`).
-/

namespace NearSpecV3.Successor.HostComm
open NearSpecV3.Successor
open NearSpecV3.Wasm

/-! ## Instantiation -/

set_option maxHeartbeats 16000000 in
theorem instLoops_X (q0 : St) (p : Prepared) (gs : Array Val) (elems : Array (Array (Option Nat)))
    (s0 : St) : instLoops p gs elems (setX q0 s0) = (instLoops p gs elems s0).map (setX q0) := by
  unfold instLoops
  simp only []
  rw [forIn_fst_arr (setX q0), ex_map_bind, ex_bind_map]
  · congr 1; funext q
    dsimp only
    rw [forIn_fst_arr (setX q0), ex_map_bind, ex_bind_map]
    · rfl
    · intro a s x
      simp only [X_memInit]
      repeat' (first | rfl | sf_gen | split)
  · intro a s x
    simp only [X_tableInit]
    repeat' (first | rfl | sf_gen | split)

theorem instInit_ga (cfg : NearCfg) (b : Bool) (p : Prepared) (gas : Gas) :
    instInit { cfg with globalActions := b } p gas = setF none (some b) (instInit cfg p gas) := rfl

/-- **Instantiation commutes with the flag.** -/
theorem instantiate_ga (cfg : NearCfg) (b : Bool) (p : Prepared) (gas : Gas) :
    instantiate { cfg with globalActions := b } p gas = (instantiate cfg p gas).map (setF none (some b)) := by
  rw [instantiate_eq_loops, instantiate_eq_loops, instInit_ga, instLoops_F]

/-- The instantiated state carries the configuration's flag and an empty action log. -/
theorem instantiate_fields (cfg : NearCfg) (p : Prepared) (gas : Gas) (s : St)
    (h : instantiate cfg p gas = .ok s) : s.globalActions = cfg.globalActions ∧ s.actions = #[] := by
  rw [instantiate_eq_loops] at h
  have e := instLoops_X (instInit cfg p gas) p
    (p.m.globals.foldl (fun acc g => acc.push (evalConst acc g.init)) #[])
    (p.m.elems.map (fun e => e.init.map (constRef (p.m.globals.foldl (fun acc g => acc.push (evalConst acc g.init)) #[]))))
    (instInit cfg p gas)
  rw [setX_self, h] at e
  injection e with e
  rw [e]
  exact ⟨rfl, rfl⟩

/-- `instantiate`, with its result written as an image of `setX` of the initial state. -/
def instX (cfg : NearCfg) (p : Prepared) (gas : Gas) : Except String St :=
  (instantiate cfg p gas).map (setX (instInit cfg p gas))

theorem instantiate_eq_instX (cfg : NearCfg) (p : Prepared) (gas : Gas) :
    instantiate cfg p gas = instX cfg p gas := by
  unfold instX
  rw [instantiate_eq_loops]
  have e := instLoops_X (instInit cfg p gas) p
    (p.m.globals.foldl (fun acc g => acc.push (evalConst acc g.init)) #[])
    (p.m.elems.map (fun e => e.init.map (constRef (p.m.globals.foldl (fun acc g => acc.push (evalConst acc g.init)) #[]))))
    (instInit cfg p gas)
  rw [setX_self] at e
  exact e

/-- The state `runCall` hands to its tail satisfies `LowQ` when the flag is off. -/
theorem lowQ_inst (cfg : NearCfg) (hg : cfg.globalActions = false) (p : Prepared) (gas : Gas) (s : St)
    (ctx : CallCtx) (r : TTN.RealStore) (c : Bool) :
    LowQ ({ setX (instInit cfg p gas) s with ctx := ctx, balance := ctx.accountBalance + ctx.attachedDeposit, storageUsage := ctx.storageUsage, real := some r, curveHosts := c } : St) := by
  have h1 : (instInit cfg p gas).globalActions = cfg.globalActions := rfl
  have h2 : (instInit cfg p gas).actions = #[] := rfl
  refine ⟨h1.trans hg, rfl, ?_⟩
  show ∀ e ∈ (instInit cfg p gas).actions, _
  rw [h2]; intro e he; simp at he

/-! ## The run after instantiation -/

theorem LowQ.entryReset {s : St} (hq : LowQ s) : LowQ (entryReset s) := ⟨hq.ga, hq.real, hq.noraw⟩

theorem runTail_global (cfg : NearCfg) (p : Prepared) (fuel mi : Nat) (s : St) (hq : LowQ s) :
    RunRel XG (setF none (some true)) (runTail cfg p fuel mi s) (runTail cfg p fuel mi (setF none (some true) s)) := by
  have E : ∀ s fi, LowQ s → ER XG (setF none (some true)) (callEntry cfg p fuel s fi)
      (callEntry cfg p fuel (setF none (some true) s) fi) :=
    fun s fi hq => ER_callEntry globalHyp cfg p fuel s fi (LowQ_step_cont cfg p) (LowQ_enter_cont p fi) hq.entryReset
  have second : ∀ s1, LowQ s1 → RunRel XG (setF none (some true))
      (match callEntry cfg p fuel s1 mi with
        | .error why => .line s!"unmodeled {why}"
        | .ok (s, e) => .done s e)
      (match callEntry cfg p fuel (setF none (some true) s1) mi with
        | .error why => .line s!"unmodeled {why}"
        | .ok (s, e) => .done s e) := by
    intro s1 hq1
    rcases E s1 mi hq1 with he | ⟨w, hw, he⟩
    · rw [he]
      cases callEntry cfg p fuel s1 mi with
      | error why => exact Or.inl rfl
      | ok q => exact Or.inl rfl
    · rw [he]; exact Or.inr ⟨w, hw, rfl⟩
  unfold runTail
  cases hst : p.m.start with
  | none => exact second s hq
  | some st =>
    simp only []
    rcases E s st hq with he | ⟨w, hw, he⟩
    · rw [he]
      cases hce : callEntry cfg p fuel s st with
      | error why => exact Or.inl rfl
      | ok q =>
        obtain ⟨s1, e⟩ := q
        cases e with
        | some e => exact Or.inl rfl
        | none => exact second s1 (LowQ_callEntry cfg p fuel s st hq.entryReset s1 none hce)
    · rw [he]; exact Or.inr ⟨w, hw, rfl⟩

theorem runTail_lowQ (cfg : NearCfg) (p : Prepared) (fuel mi : Nat) (s : St) (hq : LowQ s)
    (s' : St) (e : Option String) (h : runTail cfg p fuel mi s = .done s' e) : LowQ s' := by
  have second : ∀ s1, LowQ s1 →
      (match callEntry cfg p fuel s1 mi with
        | .error why => .line s!"unmodeled {why}"
        | .ok (s, e) => .done s e) = Run.done s' e → LowQ s' := by
    intro s1 hq1 h1
    cases hce : callEntry cfg p fuel s1 mi with
    | error why => rw [hce] at h1; cases h1
    | ok q =>
      obtain ⟨s2, e2⟩ := q
      rw [hce] at h1
      simp only [Run.done.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact LowQ_callEntry cfg p fuel s1 mi hq1.entryReset _ _ hce
  unfold runTail at h
  cases hst : p.m.start with
  | none => rw [hst] at h; exact second s hq h
  | some st =>
    rw [hst] at h
    simp only [] at h
    cases hce : callEntry cfg p fuel s st with
    | error why => rw [hce] at h; cases h
    | ok q =>
      obtain ⟨s1, e1⟩ := q
      have hq1 := LowQ_callEntry cfg p fuel s st hq.entryReset s1 e1 hce
      rw [hce] at h
      cases e1 with
      | some x => cases h; exact hq1
      | none => exact second s1 hq1 h

theorem step_ga_cfg (cfg : NearCfg) (b : Bool) (p : Prepared) (s : St) :
    step { cfg with globalActions := b } p s = step cfg p s := rfl

theorem run_ga_cfg (cfg : NearCfg) (b : Bool) (p : Prepared) :
    ∀ n s, run { cfg with globalActions := b } p n s = run cfg p n s
  | 0, _ => rfl
  | n + 1, s => by
    unfold run
    rw [step_ga_cfg]
    cases step cfg p s with
    | cont s' => exact run_ga_cfg cfg b p n s'
    | _ => rfl

theorem callEntry_ga_cfg (cfg : NearCfg) (b : Bool) (p : Prepared) (fuel : Nat) (s : St) (fi : Nat) :
    callEntry { cfg with globalActions := b } p fuel s fi = callEntry cfg p fuel s fi := by
  unfold callEntry; simp only [run_ga_cfg]

theorem prepare_ga_cfg (cfg : NearCfg) (b : Bool) (code : ByteArray) (bl : Bool) :
    prepare { cfg with globalActions := b } code bl = prepare cfg code bl := rfl

theorem runTail_ga_cfg (cfg : NearCfg) (b : Bool) (p : Prepared) (fuel mi : Nat) (s : St) :
    runTail { cfg with globalActions := b } p fuel mi s = runTail cfg p fuel mi s := by
  unfold runTail; simp only [callEntry_ga_cfg]

/-- The two-run relation of a call together with the lower run's invariant on its final state. -/
def RunRelG (r r' : Run) : Prop :=
  RunRel XG (setF none (some true)) r r' ∧ ∀ s e, r = .done s e → LowQ s

theorem RunRelG.line (l : String) : RunRelG (.line l) (.line l) := ⟨Or.inl rfl, fun _ _ h => by cases h⟩

theorem runTail_globalG (cfg : NearCfg) (p : Prepared) (fuel mi : Nat) (s : St) (hq : LowQ s) :
    RunRelG (runTail cfg p fuel mi s) (runTail cfg p fuel mi (setF none (some true) s)) :=
  ⟨runTail_global cfg p fuel mi s hq, fun s' e h => runTail_lowQ cfg p fuel mi s hq s' e h⟩

open Lean Elab Tactic Meta in
/-- Generalize the first closed `instantiate` call of the goal, keeping its equation, and case on it. -/
elab "inst_gen" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some e := tgt.find? (fun e => e.isAppOfArity ``instantiate 3 && !e.hasLooseBVars)
    | throwError "inst_gen: no instantiate call"
  let stx ← Term.exprToSyntax e
  evalTactic (← `(tactic| (generalize hI : $stx = ix; cases ix)))

theorem instantiate_lowQ (cfg : NearCfg) (hg : cfg.globalActions = false) (p : Prepared) (gas : Gas)
    (s : St) (h : instantiate cfg p gas = .ok s) (ctx : CallCtx) (r : TTN.RealStore) (c : Bool) :
    LowQ ({ s with ctx := ctx, balance := ctx.accountBalance + ctx.attachedDeposit, storageUsage := ctx.storageUsage, real := some r, curveHosts := c } : St) := by
  rw [instantiate_eq_instX] at h
  unfold instX at h
  cases hi : instantiate cfg p gas with
  | error e => rw [hi] at h; cases h
  | ok s0 =>
    rw [hi] at h
    simp only [Except.map, Except.ok.injEq] at h
    subst h
    exact lowQ_inst cfg hg p gas s0 ctx r c

/-- **O3, call level.** On a trie-backed call with the flag off, switching it on gives the same call
with the flag set in the final state, or the call with it off stopped at a lifted promise host; the
final state of the call with the flag off satisfies `LowQ`. -/
theorem runCall_globalG (cfg : NearCfg) (hg : cfg.globalActions = false) (code : ByteArray) (method : String)
    (ctx : CallCtx) (fuel : Nat) (bl full : Bool) (r : TTN.RealStore) :
    RunRelG (runCall cfg code method ctx fuel bl full (some r))
      (runCall { cfg with globalActions := true } code method ctx fuel bl full (some r)) := by
  rw [runCall_eq_T, runCall_eq_T]
  unfold runCallT
  simp only [prepare_ga_cfg, runTail_ga_cfg, instantiate_ga, Option.isNone_some, Bool.and_false,
    Bool.false_and, Bool.false_eq_true, ite_false]
  repeat' (first | exact RunRelG.line _ | inst_gen | (simp only [Except.map]) | lk_split)
  all_goals (exact runTail_globalG cfg _ fuel _ _ (instantiate_lowQ cfg hg _ _ _ ‹_› _ _ _))

theorem runCall_global (cfg : NearCfg) (hg : cfg.globalActions = false) (code : ByteArray) (method : String)
    (ctx : CallCtx) (fuel : Nat) (bl full : Bool) (r : TTN.RealStore) :
    RunRel XG (setF none (some true)) (runCall cfg code method ctx fuel bl full (some r))
      (runCall { cfg with globalActions := true } code method ctx fuel bl full (some r)) :=
  (runCall_globalG cfg hg code method ctx fuel bl full r).1

theorem runCallWithLimits_globalG (cfg : NearCfg) (hg : cfg.globalActions = false) (code : ByteArray)
    (method : String) (ctx : CallCtx) (fuel : Nat) (bl full : Bool) (r : TTN.RealStore) :
    RunRelG (runCallWithLimits cfg code method ctx fuel bl full (some r))
      (runCallWithLimits { cfg with globalActions := true } code method ctx fuel bl full (some r)) := by
  unfold runCallWithLimits
  simp only [prepare_ga_cfg]
  have hl : ({ cfg with globalActions := true } : NearCfg).loadingLimits = cfg.loadingLimits := rfl
  rw [hl]
  split
  · exact runCall_globalG cfg hg code method ctx fuel bl full r
  · split
    · split
      · exact runCall_globalG cfg hg code method ctx fuel bl full r
      · exact RunRelG.line _
    · exact runCall_globalG cfg hg code method ctx fuel bl full r

theorem runCallWithLimits_global (cfg : NearCfg) (hg : cfg.globalActions = false) (code : ByteArray)
    (method : String) (ctx : CallCtx) (fuel : Nat) (bl full : Bool) (r : TTN.RealStore) :
    RunRel XG (setF none (some true)) (runCallWithLimits cfg code method ctx fuel bl full (some r))
      (runCallWithLimits { cfg with globalActions := true } code method ctx fuel bl full (some r)) :=
  (runCallWithLimits_globalG cfg hg code method ctx fuel bl full r).1

theorem runCallWithLimits_lowQ (cfg : NearCfg) (hg : cfg.globalActions = false) (code : ByteArray)
    (method : String) (ctx : CallCtx) (fuel : Nat) (bl full : Bool) (r : TTN.RealStore) (s : St)
    (e : Option String) (h : runCallWithLimits cfg code method ctx fuel bl full (some r) = .done s e) :
    LowQ s :=
  (runCallWithLimits_globalG cfg hg code method ctx fuel bl full r).2 s e h

/-! ## The ten parting lines are exclusions of the recorded call -/

set_option maxHeartbeats 16000000 in
theorem lineOutcome_XG (w : String) (hw : XG w) :
    ∃ e, D3.lineOutcome s!"unmodeled {w}" = .error e ∧ isExclusion e = true := by
  obtain ⟨name, hn, rfl⟩ := hw
  apply lineOutcome_of_head
  unfold gaMsg
  have hm := List.contains_iff_mem.mp hn
  simp only [globalPromiseHosts, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> split_eval

#print axioms instantiate_ga
#print axioms runCall_global
#print axioms runCall_globalG
#print axioms runCallWithLimits_global
#print axioms runCallWithLimits_lowQ
#print axioms lineOutcome_XG

end NearSpecV3.Successor.HostComm

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Wasm StorageExecution HostComm

/-! ## The recorded call's `vm` -/

theorem vmF_global (w : NearCfg) (hg : w.globalActions = false) :
    VmF XG (setF none (some true)) (fun code m ctx real => vmCall wasmFuel w code m ctx real)
      (fun code m ctx real => vmCall wasmFuel { w with globalActions := true } code m ctx real) := by
  intro code m ctx real
  simp only []
  unfold vmCall
  have h1 : fuelCertified { w with globalActions := true } code = fuelCertified w code := rfl
  have h2 : wasmFuel { w with globalActions := true } ctx.prepaidGas = wasmFuel w ctx.prepaidGas := rfl
  rw [h1, h2]
  split
  · left; rfl
  · rcases runCallWithLimits_global w hg code m ctx (wasmFuel w ctx.prepaidGas) true false real with h | ⟨x, hx, h⟩
    · left; rw [h]; rfl
    · right; exact ⟨x, hx, by rw [h]⟩

/-- The final state of a recorded call's run with the flag off satisfies `LowQ`. -/
theorem vmCall_lowQ (w : NearCfg) (hg : w.globalActions = false) (code : ByteArray) (m : String)
    (ctx : CallCtx) (real : TTN.RealStore) (s : St) (e : Option String)
    (h : vmCall wasmFuel w code m ctx real = .ok (.done s e)) : LowQ s := by
  unfold vmCall at h
  split at h
  · cases h
  · injection h with h
    exact runCallWithLimits_lowQ w hg code m ctx _ true false real s e h

theorem contractOOD_ga (w : NearCfg) (b : Bool) :
    D3.contractOOD { w with globalActions := b } = D3.contractOOD w := rfl

#print axioms vmF_global
#print axioms vmCall_lowQ

end NearSpecV3.Successor
