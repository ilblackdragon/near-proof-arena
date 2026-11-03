import NearSpecV3.E2E.Refined

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# E2E-M11d, item 3: the honest call tape `K`

`RStep.resume` (`Refined.lean`) completes an engine step with the VM answered only from a recorded
tape `K` (`strictO K`). `estepO_sound` is the soundness side. This file is the **completeness**
side: the honest tape, as a function of the step, reproduces the engine step.

* `TLe x y` (finite use): every successful run of `x` is reproduced by `y K'` for every correct tape
  `K'` (`KOk`) containing some correct tape `K`. Upward closed, so binds compose with `K₁ ++ K₂`.
* `tape_walk` walks the verbatim copies of `CutW.lean` / `Refined.lean` against their tape-indexed
  versions exactly as `mono_walk` does (binds, `tryCatch`, `split` on tape-independent
  discriminants, callee hypothesis). Per layer: `fcW_tle`, `applyActionW_tle`, `actionLoopW_tle`,
  `applyActionReceiptW_tle`, `processReceiptW_tle`, `processWithTotalsW_tle`, `drainW_tle`,
  `processWithInstantW_tle`, `stepMO_tle`; the VM leaf `TLe.vm` uses the tape `[(q, callResult q)]`.
  Composed: `pwO_tle`.
* `strictO_sub`: a correct tape answers below any correct extension.
* **`estepO_complete`**: `estep P c = .ok c' → ∃ K, KOk K ∧ estepO (strictO K) P c = .ok c'`.
* **`honestK P c`** = `(honestQ P c).map fun q => (q, callResult q)` (answers of the spec's VM);
  `honestQ` is a **classical choice** of the queries of a tape given by `estepO_complete` (not a
  constructive recorder of the step's calls). `honestK_ok : KOk (honestK P c)`.
* **`estepO_honest`**: `estepO (strictO (honestK P c)) P c = .ok c' ↔ estep P c = .ok c'`.
* `rsteps_honest_call` / `rsteps_honest`: a successful engine step from a non-final configuration is
  an `RCM` run that enters the first honest call and runs every call of the honest tape
  (`rsteps_calls_aux`), or a base step when the tape is empty.

No checker definition is changed; standard axioms only.
-/

namespace NearSpecV3.E2E
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged NearSpecV3.Wasm
open NearSpecV3.Successor NearSpecV3.Successor.StorageExecution
open NearSpecV3.Successor.StorageExecution.CutW
open NearSpecV3.Wasm.CallCut

abbrev Tape := List (VmQ × Run)

theorem kok_append {K1 K2 : Tape} (h1 : KOk K1) (h2 : KOk K2) : KOk (K1 ++ K2) := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact h1 x hx
  · exact h2 x hx

theorem strictO_of_mem {K : Tape} (hK : KOk K) {q : VmQ} {v : Run} (hm : (q, v) ∈ K) :
    strictO K q = .ok v := by
  unfold strictO
  split
  · rename_i hex
    have h1 := hK _ (Classical.choose_spec hex)
    have h2 := hK _ hm
    simp only at h1 h2
    rw [← h1, h2]
  · rename_i hn
    exact absurd ⟨v, hm⟩ hn

theorem strictO_sub {K K' : Tape} (hK' : KOk K') (hsub : K ⊆ K') : OLe (strictO K) (strictO K') := by
  intro q v h
  unfold strictO at h
  split at h
  · rename_i hex
    cases h
    exact strictO_of_mem hK' (hsub (Classical.choose_spec hex))
  · cases h

/-- `TLe x y`: every successful run of `x` is reproduced by `y K'` for every correct tape `K'`
containing some correct tape `K` (finite use of the VM). -/
def TLe {α : Type} (x : M α) (y : Tape → M α) : Prop :=
  ∀ r e a r', x r e = .ok (a, r') →
    ∃ K, KOk K ∧ ∀ K', KOk K' → K ⊆ K' → y K' r e = .ok (a, r')

theorem TLe.const {α : Type} (x : M α) : TLe x (fun _ => x) :=
  fun _ _ _ _ h => ⟨[], ⟨fun _ hx => (nomatch hx), fun _ _ _ => h⟩⟩

theorem TLe.bind' {α β : Type} {x1 : M α} {y1 : Tape → M α} {f1 : α → M β} {f2 : Tape → α → M β}
    (hf : ∀ a, TLe (f1 a) (fun K => f2 K a)) (hx : TLe x1 y1) :
    TLe (x1 >>= f1) (fun K => y1 K >>= f2 K) := by
  intro r e b r' h
  rw [NearSpecV3.E2E.M.bind_run] at h
  unfold NearSpecV3.E2E.bindRes at h
  rcases h1 : x1 r e with err | ⟨a, r1⟩ <;> rw [h1] at h
  · cases h
  · obtain ⟨K1, hK1, hy1⟩ := hx r e a r1 h1
    obtain ⟨K2, hK2, hy2⟩ := hf a r1 e b r' h
    refine ⟨K1 ++ K2, kok_append hK1 hK2, fun K' hK' hs => ?_⟩
    dsimp only
    rw [NearSpecV3.E2E.M.bind_run]
    unfold NearSpecV3.E2E.bindRes
    rw [hy1 K' hK' (fun x hx => hs (List.mem_append_left _ hx))]
    exact hy2 K' hK' (fun x hx => hs (List.mem_append_right _ hx))

theorem TLe.tryCatch_throw {α : Type} {x1 : M α} {y1 : Tape → M α} (g : String → String)
    (hx : TLe x1 y1) :
    TLe (tryCatch x1 (fun e => throw (g e))) (fun K => tryCatch (y1 K) (fun e => throw (g e))) := by
  intro r e a r' h
  have e1 : ∀ z : M α, (tryCatch z (fun e => throw (g e)) : M α) r e =
      Except.tryCatch (z r e) (fun err => Except.error (g err)) := fun _ => rfl
  rw [e1] at h
  rcases h1 : x1 r e with err | ⟨b, r1⟩ <;> rw [h1] at h
  · cases h
  · cases h
    obtain ⟨K, hK, hy⟩ := hx r e _ _ h1
    refine ⟨K, hK, fun K' hK' hs => ?_⟩
    dsimp only
    rw [e1, hy K' hK' hs]
    rfl

/-- The VM leaf. -/
theorem TLe.vm (q : VmQ) :
    TLe (StorageExecution.liftE (vmStd q)) (fun K => StorageExecution.liftE (strictO K q)) := by
  intro r e a r' h
  refine ⟨[(q, callResult q)], ?_, fun K' hK' hs => ?_⟩
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx; rfl
  · dsimp only
    rw [strictO_of_mem hK' (hs (List.mem_singleton_self _))]
    rw [vmStd_eq] at h
    exact h

/-- Walk a `do` block against its tape-indexed copy. -/
syntax "tape_walk" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| tape_walk) => `(tactic| (
      first
        | (with_reducible exact TLe.const _)
        | (apply hcallee)
        | (apply ih)
        | (with_reducible refine TLe.bind' (fun _ => ?_) ?_) <;> tape_walk
        | (refine TLe.tryCatch_throw _ ?_; tape_walk)
        | (split <;> tape_walk)
        | (cases ‹_ × _›; tape_walk)
        | (dsimp only; tape_walk)))

theorem fcW_tle {vm1 : VmFn} {vm2 : Tape → VmFn}
    (hcallee : ∀ cfg code m ctx real, TLe (StorageExecution.liftE (vm1 cfg code m ctx real))
      (fun K => StorageExecution.liftE (vm2 K cfg code m ctx real))) :
    ∀ fl cfg c st ar b, TLe (fcW vm1 fl cfg c st ar b) (fun K => fcW (vm2 K) fl cfg c st ar b) := by
  intro fl cfg c st ar b
  unfold fcW
  tape_walk

theorem applyActionW_tle {fc1 : FcFn} {fc2 : Tape → FcFn}
    (hcallee : ∀ fl cfg c st ar b, TLe (fc1 fl cfg c st ar b) (fun K => fc2 K fl cfg c st ar b)) :
    ∀ fl cfg c st a, TLe (applyActionW fc1 fl cfg c st a) (fun K => applyActionW (fc2 K) fl cfg c st a) := by
  intro fl cfg c st a
  unfold applyActionW
  tape_walk

theorem actionLoopW_tle {aa1 : AaFn} {aa2 : Tape → AaFn}
    (hcallee : ∀ fl cfg c st a, TLe (aa1 fl cfg c st a) (fun K => aa2 K fl cfg c st a)) :
    ∀ fl hooks env r a inputs deployed attempted i l acc,
      TLe (@actionLoopW aa1 fl hooks env r a inputs deployed attempted i l acc)
        (fun K => @actionLoopW (aa2 K) fl hooks env r a inputs deployed attempted i l acc) := by
  intro fl hooks env r a inputs deployed attempted i l acc
  induction l generalizing i acc with
  | nil => simp only [actionLoopW.eq_1]; exact TLe.const _
  | cons act rest ih =>
    obtain ⟨st, res⟩ := acc
    simp (config := { zeta := false }) only [actionLoopW.eq_2]
    tape_walk

theorem applyActionReceiptW_tle {al1 : AlFn} {al2 : Tape → AlFn}
    (hcallee : ∀ fl hooks env r a inputs deployed attempted i l acc,
      TLe (al1 fl hooks env r a inputs deployed attempted i l acc)
        (fun K => al2 K fl hooks env r a inputs deployed attempted i l acc)) :
    ∀ fl hooks env rs r a, TLe (applyActionReceiptW al1 fl hooks env rs r a)
      (fun K => applyActionReceiptW (al2 K) fl hooks env rs r a) := by
  intro fl hooks env rs r a
  unfold applyActionReceiptW
  tape_walk

theorem processReceiptW_tle {aar1 : AarFn} {aar2 : Tape → AarFn}
    (hcallee : ∀ fl hooks env rs r a, TLe (aar1 fl hooks env rs r a) (fun K => aar2 K fl hooks env rs r a)) :
    ∀ fl hooks env rs r, TLe (processReceiptW aar1 fl hooks env rs r)
      (fun K => processReceiptW (aar2 K) fl hooks env rs r) := by
  intro fl hooks env rs r
  unfold processReceiptW
  tape_walk

theorem processWithTotalsW_tle {pr1 : PrFn} {pr2 : Tape → PrFn}
    (hcallee : ∀ fl hooks env rs r, TLe (pr1 fl hooks env rs r) (fun K => pr2 K fl hooks env rs r)) :
    ∀ fl hooks env rs r, TLe (processWithTotalsW pr1 fl hooks env rs r)
      (fun K => processWithTotalsW (pr2 K) fl hooks env rs r) := by
  intro fl hooks env rs r
  unfold processWithTotalsW
  tape_walk

theorem drainW_tle {pw1 : PwFn} {pw2 : Tape → PwFn}
    (hcallee : ∀ fl hooks env rs r, TLe (pw1 fl hooks env rs r) (fun K => pw2 K fl hooks env rs r)) :
    ∀ fl hooks env n rs, TLe (drainW pw1 fl hooks env n rs) (fun K => drainW (pw2 K) fl hooks env n rs) := by
  intro fl hooks env n rs
  induction n generalizing rs with
  | zero => exact TLe.const _
  | succ n ih =>
    simp (config := { zeta := false }) only [drainW]
    tape_walk

theorem processWithInstantW_tle {pw1 : PwFn} {pw2 : Tape → PwFn}
    (hcallee : ∀ fl hooks env rs r, TLe (pw1 fl hooks env rs r) (fun K => pw2 K fl hooks env rs r)) :
    ∀ fl hooks env rs r, TLe (processWithInstantW pw1 fl hooks env rs r)
      (fun K => processWithInstantW (pw2 K) fl hooks env rs r) := by
  intro fl hooks env rs r
  unfold processWithInstantW
  exact TLe.bind' (fun _ => drainW_tle hcallee _ _ _ _ _) (hcallee _ _ _ _ _)

/-- **Finite use of the VM by the oracle receipt step.** -/
theorem pwO_tle : ∀ fl hooks env rs r,
    TLe (pwO vmStd fl hooks env rs r) (fun K => pwO (strictO K) fl hooks env rs r) :=
  processWithInstantW_tle (processWithTotalsW_tle (processReceiptW_tle
    (applyActionReceiptW_tle (actionLoopW_tle (applyActionW_tle (fcW_tle
      (fun cfg code m ctx real => TLe.vm ⟨cfg, code, m, ctx, real⟩)))))))

theorem stepMO_tle {pw1 : PwFn} {pw2 : Tape → PwFn}
    (hcallee : ∀ fl hooks env rs r, TLe (pw1 fl hooks env rs r) (fun K => pw2 K fl hooks env rs r))
    (P : Prog) (p : EPos) : TLe (stepMO pw1 P p) (fun K => stepMO (pw2 K) P p) := by
  match p with
  | .locals (r :: rest) rs => simp (config := { zeta := false }) only [stepMO, localsBodyO]; tape_walk
  | .delayed (f + 1) rs => simp (config := { zeta := false }) only [stepMO, delayedKO]; tape_walk
  | .incoming (r :: rest) rs => simp (config := { zeta := false }) only [stepMO, incomingBodyO]; tape_walk
  | .start => exact TLe.const _
  | .txs _ _ _ => exact TLe.const _
  | .locals [] rs => exact TLe.const _
  | .delayed 0 rs => exact TLe.const _
  | .incoming [] rs => exact TLe.const _
  | .yields _ _ _ _ _ _ => exact TLe.const _
  | .done _ => exact TLe.const _

/-- **Completeness of the oracle step**: a successful engine step is reproduced by the oracle step
answered from some correct finite tape. -/
theorem estepO_complete {P : Prog} {c c' : EConf} (h : estep P c = .ok c') :
    ∃ K, KOk K ∧ estepO (strictO K) P c = .ok c' := by
  unfold estep at h
  split at h
  · rename_i p r heq
    cases h
    rw [← stepMO_std, ← pwO_std] at heq
    obtain ⟨K, hK, hy⟩ := stepMO_tle pwO_tle P c.pos c.st P.env p r heq
    refine ⟨K, hK, ?_⟩
    unfold estepO
    have h2 := hy K hK (List.Subset.refl _)
    dsimp only at h2
    rw [h2]
  · cases h

/-! ## The honest tape -/

/-- The queries of the honest tape of the step from `c`: the queries of a correct tape that
completes the oracle step to the engine step (`estepO_complete`), chosen by `Classical.choose`;
`[]` when the engine step fails. **Not constructive**: the list is a classical choice among the
correct tapes that work, not a recording of the step's actual calls. -/
noncomputable def honestQ (P : Prog) (c : EConf) : List VmQ :=
  @dite _ (∃ K, KOk K ∧ ∃ c', estep P c = .ok c' ∧ estepO (strictO K) P c = .ok c')
    (Classical.propDecidable _) (fun h => (Classical.choose h).map Prod.fst) (fun _ => [])

/-- **The honest tape**: each query of `honestQ` answered by the spec's VM (`callResult`). -/
noncomputable def honestK (P : Prog) (c : EConf) : Tape :=
  (honestQ P c).map fun q => (q, callResult q)

theorem honestK_ok (P : Prog) (c : EConf) : KOk (honestK P c) := by
  intro x hx
  unfold honestK at hx
  obtain ⟨q, _, rfl⟩ := List.mem_map.1 hx
  rfl

theorem kok_map_eq : ∀ K : Tape, KOk K → (K.map Prod.fst).map (fun q => (q, callResult q)) = K
  | [], _ => rfl
  | x :: K, h => by
    simp only [List.map_cons]
    rw [kok_map_eq K (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    have hx := h x (by simp)
    obtain ⟨q, v⟩ := x
    simp only at hx ⊢
    rw [hx]

/-- **The refined receipt step answered from the honest tape is the engine step.** -/
theorem estepO_honest (P : Prog) (c c' : EConf) :
    estepO (strictO (honestK P c)) P c = .ok c' ↔ estep P c = .ok c' := by
  constructor
  · exact estepO_sound (strictO_le (honestK_ok P c)) P c c'
  · intro h
    have hex : ∃ K, KOk K ∧ ∃ c', estep P c = .ok c' ∧ estepO (strictO K) P c = .ok c' := by
      obtain ⟨K, hK, hO⟩ := estepO_complete h
      exact ⟨K, hK, c', h, hO⟩
    unfold honestK honestQ
    split
    · rename_i h'
      obtain ⟨hK, c'', he, hO⟩ := Classical.choose_spec h'
      rw [kok_map_eq _ hK]
      rw [h] at he
      cases he
      exact hO
    · rename_i hn
      exact absurd hex hn

/-! ## `RCM` runs through the honest tape -/

/-- From the entered first call of the honest tape, `RCM` runs every call of the tape (every Wasm
instruction a step of the call machine) and resumes at the next engine configuration. -/
theorem rsteps_honest_call (I : Intake) (c c' : EConf) (hc : ∀ out, c.pos ≠ .done out)
    (h : estep I.prog c = .ok c') (q : VmQ) (qs : List VmQ) (hq : honestQ I.prog c = q :: qs) :
    RSteps (.call I c [] q .pre) (.base (.eng I c')) := by
  have h2 := (estepO_honest I.prog c c').2 h
  unfold honestK at h2
  rw [hq] at h2
  exact rsteps_calls_aux I c c' hc qs [] q (by rw [List.nil_append]; exact h2)

/-- **The engine step through the honest tape.** If the engine step from a non-final `c` succeeds,
`RCM` reaches `c'`: entering the first honest call and running through all calls of the honest
tape when it is nonempty (`rsteps_honest_call`), by a base step otherwise. -/
theorem rsteps_honest (I : Intake) (c c' : EConf) (hc : ∀ out, c.pos ≠ .done out)
    (h : estep I.prog c = .ok c') : RSteps (.base (.eng I c)) (.base (.eng I c')) := by
  rcases hq : honestQ I.prog c with _ | ⟨q, qs⟩
  · exact .single (.base (cm_step_eng I c c' hc h))
  · exact .step (.enter I c q) (rsteps_honest_call I c c' hc h q qs hq)

#print axioms strictO_sub
#print axioms pwO_tle
#print axioms estepO_complete
#print axioms honestK_ok
#print axioms estepO_honest
#print axioms rsteps_honest_call
#print axioms rsteps_honest

end NearSpecV3.E2E
