import NearSpecV3.E2E.Refined

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# E2E-M11d item 3 / M11e item 3: the honest call tape `K`, recorded

`RStep.resume` (`Refined.lean`) completes an engine step with the VM answered only from a recorded
tape `K` (`strictO K`). `estepO_sound` is the soundness side. This file is the **completeness**
side: the honest tape, as a function of the step, reproduces the engine step.

* `TLe x y` (finite use): every successful run of `x` is reproduced by `y K'` for every correct tape
  `K'` (`KOk`) containing some correct tape `K`. Upward closed, so binds compose with `K₁ ++ K₂`.
* `TRec x y` (the **recorder**): the data version of `TLe` — a function computing, from a successful
  run of `x`, the tape `K` with its correctness and completion facts (a subtype); its second index is
  oracle-indexed (`y : VmO → M α`, read at `strictO K'`). `TLe.of_trec`.
* `trec_walk` walks the verbatim copies of `CutW.lean` / `Refined.lean` against their tape-indexed
  versions exactly as `mono_walk` does (binds, `tryCatch`, `split` on tape-independent
  discriminants, callee hypothesis), building the recorder as a computable `def`. Per layer:
  `fcW_trec`, `applyActionW_trec`, `actionLoopW_trec`, `applyActionReceiptW_trec`,
  `processReceiptW_trec`, `processWithTotalsW_trec`, `drainW_trec` (the two recursive layers by
  structural recursion), `processWithInstantW_trec`, `stepMO_trec`; the VM leaf `TRec.vm` records
  `[(q, callResult q)]`, a bind concatenates. Composed: `pwO_trec`; `pwO_tle` follows.
* `strictO_sub`: a correct tape answers below any correct extension.
* **`recordK P c`**: the recorded tape — run the oracle step at the checker's VM
  (`stepMO (pwO vmStd)`, which is `stepM` by `pwO_std`) and record its calls through
  `stepMO_trec pwO_trec`; `[]` when the step fails. A computable `def`, no classical choice.
  `recordK_spec`: on a successful engine step it is correct and completes the oracle step.
* **`estepO_complete`**: `estep P c = .ok c' → ∃ K, KOk K ∧ estepO (strictO K) P c = .ok c'`
  (witness `recordK P c`).
* **`honestK P c`** = `(honestQ P c).map fun q => (q, callResult q)` (answers of the spec's VM), with
  `honestQ P c = (recordK P c).map Prod.fst` the recorded queries (computable; `honestK_eq`:
  `honestK P c = recordK P c` on a successful step). `honestK_ok : KOk (honestK P c)`.
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

/-- `TRec x y`: the **recorder** — the data version of `TLe`. From every successful run of `x` it
computes a correct tape `K` (`KOk`) such that `y (strictO K')` reproduces the run for every correct
tape `K'` containing `K`. The tape is built by the same structural recursion as the run
(`trec_walk`), so it is the list of the run's VM calls, each answered by `callResult`. The
oracle-indexed side `y : VmO → M α` is a computable function of the oracle (`strictO`, which is
noncomputable, occurs only in the proposition), so the recorders below are compiled `def`s. -/
def TRec {α : Type} (x : M α) (y : VmO → M α) : Type :=
  ∀ r e a r', x r e = .ok (a, r') →
    {K : Tape // KOk K ∧ ∀ K', KOk K' → K ⊆ K' → y (strictO K') r e = .ok (a, r')}

theorem TLe.of_trec {α : Type} {x : M α} {y : VmO → M α} (h : TRec x y) :
    TLe x (fun K => y (strictO K)) :=
  fun r e a r' hx => ⟨(h r e a r' hx).1, (h r e a r' hx).2⟩

/-- No VM call: the empty tape. -/
def TRec.const {α : Type} (x : M α) : TRec x (fun _ => x) :=
  fun _ _ _ _ h => ⟨[], ⟨fun _ hx => (nomatch hx), fun _ _ _ => h⟩⟩

/-- Sequencing: the tape of the first computation, then the tape of the continuation. -/
def TRec.bind' {α β : Type} {x1 : M α} {y1 : VmO → M α} {f1 : α → M β} {f2 : VmO → α → M β}
    (hf : ∀ a, TRec (f1 a) (fun o => f2 o a)) (hx : TRec x1 y1) :
    TRec (x1 >>= f1) (fun o => y1 o >>= f2 o) := fun r e b r' h =>
  match h1 : x1 r e with
  | .error err => absurd h (by rw [M.bind_run, h1]; unfold bindRes; exact nofun)
  | .ok (a, r1) =>
    have h' : f1 a r1 e = .ok (b, r') := by rw [M.bind_run, h1] at h; exact h
    match hx r e a r1 h1, hf a r1 e b r' h' with
    | ⟨K1, hK1, hy1⟩, ⟨K2, hK2, hy2⟩ =>
    ⟨K1 ++ K2, kok_append hK1 hK2, fun K' hK' hs => by
      dsimp only
      rw [M.bind_run]
      unfold bindRes
      rw [hy1 K' hK' (fun x hx => hs (List.mem_append_left _ hx))]
      exact hy2 K' hK' (fun x hx => hs (List.mem_append_right _ hx))⟩

/-- A rethrowing `tryCatch`: the tape of the body. -/
def TRec.tryCatch_throw {α : Type} {x1 : M α} {y1 : VmO → M α} (g : String → String)
    (hx : TRec x1 y1) :
    TRec (tryCatch x1 (fun e => throw (g e))) (fun o => tryCatch (y1 o) (fun e => throw (g e))) :=
  fun r e a r' h =>
  have e1 : ∀ z : M α, (tryCatch z (fun e => throw (g e)) : M α) r e =
      Except.tryCatch (z r e) (fun err => Except.error (g err)) := fun _ => rfl
  have h' : x1 r e = .ok (a, r') := by
    rw [e1] at h
    rcases h1 : x1 r e with err | ⟨b, r1⟩ <;> rw [h1] at h
    · cases h
    · cases h; rfl
  match hx r e a r' h' with
  | ⟨K, hK, hy⟩ =>
    ⟨K, hK, fun K' hK' hs => by
      dsimp only
      rw [e1, hy K' hK' hs]
      rfl⟩

/-- The VM leaf: the query, answered by the spec's VM, is recorded. -/
def TRec.vm (q : VmQ) :
    TRec (StorageExecution.liftE (vmStd q)) (fun o => StorageExecution.liftE (o q)) :=
  fun r e a r' h => ⟨[(q, callResult q)], by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; rfl, fun K' hK' hs => by
    dsimp only
    rw [strictO_of_mem hK' (hs (List.mem_singleton_self _))]
    rw [vmStd_eq] at h
    exact h⟩

theorem TLe.const {α : Type} (x : M α) : TLe x (fun _ => x) := TLe.of_trec (TRec.const x)

theorem TLe.vm (q : VmQ) :
    TLe (StorageExecution.liftE (vmStd q)) (fun K => StorageExecution.liftE (strictO K q)) :=
  TLe.of_trec (TRec.vm q)

/-- Walk a `do` block against its tape-indexed copy, building the recorder. -/
syntax "trec_walk" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| trec_walk) => `(tactic| (
      first
        | (with_reducible exact TRec.const _)
        | (apply hcallee)
        | (apply ih)
        | (with_reducible refine TRec.bind' (fun _ => ?_) ?_) <;> trec_walk
        | (refine TRec.tryCatch_throw _ ?_; trec_walk)
        | (split <;> trec_walk)
        | (cases ‹_ × _›; trec_walk)
        | (dsimp only; trec_walk)))

def fcW_trec {vm1 : VmFn} {vm2 : VmO → VmFn}
    (hcallee : ∀ cfg code m ctx real, TRec (StorageExecution.liftE (vm1 cfg code m ctx real))
      (fun o => StorageExecution.liftE (vm2 o cfg code m ctx real))) :
    ∀ fl cfg c st ar b, TRec (fcW vm1 fl cfg c st ar b) (fun o => fcW (vm2 o) fl cfg c st ar b) := by
  intro fl cfg c st ar b
  unfold fcW
  trec_walk

def applyActionW_trec {fc1 : FcFn} {fc2 : VmO → FcFn}
    (hcallee : ∀ fl cfg c st ar b, TRec (fc1 fl cfg c st ar b) (fun o => fc2 o fl cfg c st ar b)) :
    ∀ fl cfg c st a, TRec (applyActionW fc1 fl cfg c st a) (fun o => applyActionW (fc2 o) fl cfg c st a) := by
  intro fl cfg c st a
  unfold applyActionW
  trec_walk

def actionLoopW_trec {aa1 : AaFn} {aa2 : VmO → AaFn}
    (hcallee : ∀ fl cfg c st a, TRec (aa1 fl cfg c st a) (fun o => aa2 o fl cfg c st a))
    (fl : Flags) (hooks : NearCfg) (env : Env) (r : Rcpt) (a : ActionR)
    (inputs : List (Option Bytes)) (deployed attempted : List Bytes) :
    ∀ i l acc,
      TRec (@actionLoopW aa1 fl hooks env r a inputs deployed attempted i l acc)
        (fun o => @actionLoopW (aa2 o) fl hooks env r a inputs deployed attempted i l acc)
  | i, [], acc => by simp only [actionLoopW.eq_1]; exact TRec.const _
  | i, act :: rest, (st, res) => by
    have ih := fun i acc =>
      actionLoopW_trec hcallee fl hooks env r a inputs deployed attempted i rest acc
    simp (config := { zeta := false }) only [actionLoopW.eq_2]
    trec_walk

def applyActionReceiptW_trec {al1 : AlFn} {al2 : VmO → AlFn}
    (hcallee : ∀ fl hooks env r a inputs deployed attempted i l acc,
      TRec (al1 fl hooks env r a inputs deployed attempted i l acc)
        (fun o => al2 o fl hooks env r a inputs deployed attempted i l acc)) :
    ∀ fl hooks env rs r a, TRec (applyActionReceiptW al1 fl hooks env rs r a)
      (fun o => applyActionReceiptW (al2 o) fl hooks env rs r a) := by
  intro fl hooks env rs r a
  unfold applyActionReceiptW
  trec_walk

def processReceiptW_trec {aar1 : AarFn} {aar2 : VmO → AarFn}
    (hcallee : ∀ fl hooks env rs r a, TRec (aar1 fl hooks env rs r a) (fun o => aar2 o fl hooks env rs r a)) :
    ∀ fl hooks env rs r, TRec (processReceiptW aar1 fl hooks env rs r)
      (fun o => processReceiptW (aar2 o) fl hooks env rs r) := by
  intro fl hooks env rs r
  unfold processReceiptW
  trec_walk

def processWithTotalsW_trec {pr1 : PrFn} {pr2 : VmO → PrFn}
    (hcallee : ∀ fl hooks env rs r, TRec (pr1 fl hooks env rs r) (fun o => pr2 o fl hooks env rs r)) :
    ∀ fl hooks env rs r, TRec (processWithTotalsW pr1 fl hooks env rs r)
      (fun o => processWithTotalsW (pr2 o) fl hooks env rs r) := by
  intro fl hooks env rs r
  unfold processWithTotalsW
  trec_walk

def drainW_trec {pw1 : PwFn} {pw2 : VmO → PwFn}
    (hcallee : ∀ fl hooks env rs r, TRec (pw1 fl hooks env rs r) (fun o => pw2 o fl hooks env rs r))
    (fl : Flags) (hooks : NearCfg) (env : Env) :
    ∀ n rs, TRec (drainW pw1 fl hooks env n rs) (fun o => drainW (pw2 o) fl hooks env n rs)
  | 0, rs => TRec.const _
  | n + 1, rs => by
    have ih := fun rs => drainW_trec hcallee fl hooks env n rs
    simp (config := { zeta := false }) only [drainW]
    trec_walk

def processWithInstantW_trec {pw1 : PwFn} {pw2 : VmO → PwFn}
    (hcallee : ∀ fl hooks env rs r, TRec (pw1 fl hooks env rs r) (fun o => pw2 o fl hooks env rs r)) :
    ∀ fl hooks env rs r, TRec (processWithInstantW pw1 fl hooks env rs r)
      (fun o => processWithInstantW (pw2 o) fl hooks env rs r) := by
  intro fl hooks env rs r
  unfold processWithInstantW
  exact TRec.bind' (fun _ => drainW_trec hcallee _ _ _ _ _) (hcallee _ _ _ _ _)

/-- **The recorder of the oracle receipt step** (through every `CutW` layer). -/
def pwO_trec : ∀ fl hooks env rs r,
    TRec (pwO vmStd fl hooks env rs r) (fun o => pwO o fl hooks env rs r) :=
  processWithInstantW_trec (processWithTotalsW_trec (processReceiptW_trec
    (applyActionReceiptW_trec (actionLoopW_trec (applyActionW_trec (fcW_trec
      (fun cfg code m ctx real => TRec.vm ⟨cfg, code, m, ctx, real⟩)))))))

def stepMO_trec {pw1 : PwFn} {pw2 : VmO → PwFn}
    (hcallee : ∀ fl hooks env rs r, TRec (pw1 fl hooks env rs r) (fun o => pw2 o fl hooks env rs r))
    (P : Prog) (p : EPos) : TRec (stepMO pw1 P p) (fun o => stepMO (pw2 o) P p) := by
  match p with
  | .locals (r :: rest) rs => simp (config := { zeta := false }) only [stepMO, localsBodyO]; trec_walk
  | .delayed (f + 1) rs => simp (config := { zeta := false }) only [stepMO, delayedKO]; trec_walk
  | .incoming (r :: rest) rs => simp (config := { zeta := false }) only [stepMO, incomingBodyO]; trec_walk
  | .start => exact TRec.const _
  | .txs _ _ _ => exact TRec.const _
  | .locals [] rs => exact TRec.const _
  | .delayed 0 rs => exact TRec.const _
  | .incoming [] rs => exact TRec.const _
  | .yields _ _ _ _ _ _ => exact TRec.const _
  | .done _ => exact TRec.const _

/-- **Finite use of the VM by the oracle receipt step.** -/
theorem pwO_tle : ∀ fl hooks env rs r,
    TLe (pwO vmStd fl hooks env rs r) (fun K => pwO (strictO K) fl hooks env rs r) :=
  fun fl hooks env rs r => TLe.of_trec (pwO_trec fl hooks env rs r)

theorem stepMO_pwO_std (P : Prog) (c : EConf) :
    stepMO (pwO vmStd) P c.pos c.st P.env = stepM P c.pos c.st P.env := by
  rw [pwO_std, stepMO_std]

/-! ## The honest tape -/

/-- **The recorder**: the tape of the VM calls of the engine step from `c`, each answered by the
spec's VM (`callResult`), computed by running the oracle step at the checker's VM (`pwO vmStd`,
which is the engine's receipt step, `pwO_std`) through the recorder `stepMO_trec pwO_trec`; `[]` when
the step fails. Computable: no classical choice. -/
def recordK (P : Prog) (c : EConf) : Tape :=
  match h : stepMO (pwO vmStd) P c.pos c.st P.env with
  | .ok (p, r) => (stepMO_trec pwO_trec P c.pos c.st P.env p r h).1
  | .error _ => []

/-- The queries of the honest tape of the step from `c`: the VM calls the step makes, recorded
(`recordK`). -/
def honestQ (P : Prog) (c : EConf) : List VmQ := (recordK P c).map Prod.fst

/-- **The honest tape**: each query of `honestQ` answered by the spec's VM (`callResult`). -/
def honestK (P : Prog) (c : EConf) : Tape :=
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

/-- The recorded tape is correct and completes the oracle step to the engine step. -/
theorem recordK_spec {P : Prog} {c c' : EConf} (h : estep P c = .ok c') :
    KOk (recordK P c) ∧ estepO (strictO (recordK P c)) P c = .ok c' := by
  unfold estep at h
  rw [← stepMO_pwO_std] at h
  unfold recordK
  split
  · rename_i p r heq
    rw [heq] at h
    cases h
    obtain ⟨hK, hy⟩ := (stepMO_trec pwO_trec P c.pos c.st P.env p r heq).2
    refine ⟨hK, ?_⟩
    unfold estepO
    have h2 := hy _ hK (List.Subset.refl _)
    dsimp only at h2
    rw [h2]
  · rename_i e heq
    rw [heq] at h
    cases h

theorem honestK_eq {P : Prog} {c c' : EConf} (h : estep P c = .ok c') :
    honestK P c = recordK P c := by
  unfold honestK honestQ
  exact kok_map_eq _ (recordK_spec h).1

/-- **Completeness of the oracle step**: a successful engine step is reproduced by the oracle step
answered from some correct finite tape (the recorded one). -/
theorem estepO_complete {P : Prog} {c c' : EConf} (h : estep P c = .ok c') :
    ∃ K, KOk K ∧ estepO (strictO K) P c = .ok c' :=
  ⟨recordK P c, recordK_spec h⟩

/-- **The refined receipt step answered from the honest tape is the engine step.** -/
theorem estepO_honest (P : Prog) (c c' : EConf) :
    estepO (strictO (honestK P c)) P c = .ok c' ↔ estep P c = .ok c' := by
  constructor
  · exact estepO_sound (strictO_le (honestK_ok P c)) P c c'
  · intro h
    rw [honestK_eq h]
    exact (recordK_spec h).2

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
#print axioms recordK
#print axioms honestQ
#print axioms recordK_spec
#print axioms honestK_ok
#print axioms estepO_honest
#print axioms rsteps_honest_call
#print axioms rsteps_honest

end NearSpecV3.E2E
