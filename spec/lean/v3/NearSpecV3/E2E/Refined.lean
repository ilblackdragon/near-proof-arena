import NearSpecV3.E2E.CutW

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# E2E-M11b, part 3: the refined chunk machine `RCM` with mid-call (`inCall`) boundaries

`CM` (`Machine.lean`) takes one whole receipt per engine step, including every Wasm call the
receipt makes. `RCM` refines it so that a segment boundary may fall **inside a Wasm call**
(plan §3.2, `inCall`):

* `RConf.base c` — a `CM` configuration;
* `RConf.call I c K q cc` — engine configuration `c` is executing a receipt step; the VM queries it
  has already had answered are `K` (query, result); the current query `q` is in the call machine
  (`CallMachine.lean`) at `cc`. When `cc = .ent p k (.cont s) n`, `s` is the whole Wasm state
  `St`, the plan's `inCall` boundary.

Steps (`RStep`):
* `base`: a `CM` step;
* `enter`: start a VM call `q` from an engine configuration;
* `wasm`: one call-machine step (one Wasm instruction inside an entry);
* `next`: a finished call's result is appended to `K`; the next call starts;
* `resume`: the receipt step is completed with the VM answered **only** from `K`
  (`strictO K`: an unanswered query fails), giving the next engine configuration.

So the `STATE` template of the plan never runs Wasm: its receipt step reads the VM results from
the `WASM` segments through `K` (the host/VM answers carried in the boundary).

Results (standard axioms only):
* `rsteps_sound` / `rsteps_of_steps`: `RSteps (base a) (base b) ↔ Steps a b`; hence
  **`rcm_iff : Tier.rel .allFeatures cb wb ↔ RCMAccepts cb wb`**.
* `estepO_sound`: a receipt step run with any oracle below the checker's VM (`OLe`) that succeeds
  is the real engine step. It rests on the verbatim copies of `CutW.lean` (`pwO_std`) and their
  monotonicity (`pwO_mono`).
* `rsteps_seg`, `rsteps_foldSegments`: a Wasm segment (`seg`/`foldSegments`, i.e.
  `Wasm.run_foldSegments`) is an `RCM` run between two `inCall` boundaries.
* `rsteps_through_calls`: non-vacuity of the cut. If a receipt step is completed by the answers of
  calls `q₁ … q_m`, `RCM` reaches the next engine configuration through every Wasm instruction of
  every call.
* `e2e_sound_r`: `e2e_sound` with segment soundness against `RSteps` (segments may begin and end
  mid-call); the wrap obligations are unchanged.
-/

namespace NearSpecV3.E2E
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged NearSpecV3.Wasm
open NearSpecV3.Successor NearSpecV3.Successor.StorageExecution
open NearSpecV3.Successor.StorageExecution.CutW
open NearSpecV3.Wasm.CallCut

/-! ## The engine step with the receipt body as a parameter (verbatim) -/

def localsBodyO (pw : PwFn) (fl : Flags) (hooks : NearCfg) (env : Env)
    (decode : Bytes → Except String Rcpt) (rs : RS) (r : Rcpt) : M RS := do
    if rs.compute ≥ env.ctx.gasLimit || (← softExceeded) then logged (delayPushL rs r)
    else
      modifyPipe (Pipeline.stepList decode rs.o)
      pw fl hooks env rs r

def incomingBodyO (pw : PwFn) (fl : Flags) (hooks : NearCfg) (env : Env)
    (decode : Bytes → Except String Rcpt) (rs : RS) (r : Rcpt) : M RS := do
    if !validReceipt false r then throw (panicked "ReceiptValidationError on an incoming receipt")
    if rs.compute ≥ env.ctx.gasLimit || (← softExceeded) then logged (delayPushL rs r)
    else
      modifyPipe (Pipeline.stepList decode rs.o)
      pw fl hooks env rs r

def delayedKO {β : Type} (pw : PwFn) (fl : Flags) (hooks : NearCfg) (env : Env) (stop cont : RS → M β)
    (rs : RS) : M β := do
    if rs.compute ≥ env.ctx.gasLimit || (← softExceeded) then return ← stop rs
    let (rs, r) ← delayPopR fl.globalActions env (rs.dq.next - rs.dq.first + 1) rs
    match r with
    | none => stop rs
    | some r =>
      match (← get).pipe.next with
      | some n =>
        if n - 1 == 0 then scheduleDelayed fl.globalActions env rs
        else modifyPipe fun p => { p with next := some (n - 1) }
      | none => pure ()
      if !validReceipt false r then throw (inconsistent "Delayed receipt in the state is invalid")
      let rs ← pw fl hooks env rs r
      cont rs

/-- `stepM` with the receipt body `processWithInstant` as a parameter. -/
def stepMO (pw : PwFn) (P : Prog) : EPos → M EPos
  | .locals (r :: rest) rs =>
    localsBodyO pw P.fl P.hooks P.env (decodeOf P.fl.globalActions) rs r >>= fun rs => pure (.locals rest rs)
  | .delayed (f + 1) rs =>
    delayedKO pw P.fl P.hooks P.env (fun rs => pure (.delayed 0 rs)) (fun rs => pure (.delayed f rs)) rs
  | .incoming (r :: rest) rs =>
    incomingBodyO pw P.fl P.hooks P.env (decodeOf P.fl.globalActions) rs r >>= fun rs =>
      pure (.incoming rest rs)
  | p => stepM P p

theorem stepMO_std (P : Prog) (p : EPos) : stepMO processWithInstant P p = stepM P p := by
  match p with
  | .locals (r :: rest) rs => rfl
  | .delayed (f + 1) rs => rfl
  | .incoming (r :: rest) rs => rfl
  | .start => rfl
  | .txs _ _ _ => rfl
  | .locals [] rs => rfl
  | .delayed 0 rs => rfl
  | .incoming [] rs => rfl
  | .yields _ _ _ _ _ _ => rfl
  | .done _ => rfl

theorem stepMO_mono {pw1 pw2 : PwFn}
    (hcallee : ∀ fl hooks env rs r, MLe (pw1 fl hooks env rs r) (pw2 fl hooks env rs r))
    (P : Prog) (p : EPos) : MLe (stepMO pw1 P p) (stepMO pw2 P p) := by
  match p with
  | .locals (r :: rest) rs => simp only [stepMO, localsBodyO]; mono_walk
  | .delayed (f + 1) rs => simp only [stepMO, delayedKO]; mono_walk
  | .incoming (r :: rest) rs => simp only [stepMO, incomingBodyO]; mono_walk
  | .start => exact MLe.refl _
  | .txs _ _ _ => exact MLe.refl _
  | .locals [] rs => exact MLe.refl _
  | .delayed 0 rs => exact MLe.refl _
  | .incoming [] rs => exact MLe.refl _
  | .yields _ _ _ _ _ _ => exact MLe.refl _
  | .done _ => exact MLe.refl _

/-- One engine step with the VM answered by the oracle `o`. -/
def estepO (o : VmO) (P : Prog) (c : EConf) : Except String EConf :=
  match stepMO (pwO o) P c.pos c.st P.env with
  | .ok (p, r) => .ok ⟨p, r⟩
  | .error e => .error e

/-- **A successful oracle step with an oracle below the checker's VM is the engine step.** -/
theorem estepO_sound {o : VmO} (ho : OLe o vmStd) (P : Prog) (c c' : EConf)
    (h : estepO o P c = .ok c') : estep P c = .ok c' := by
  unfold estepO at h
  split at h
  · rename_i p r heq
    cases h
    have h2 := stepMO_mono (pwO_mono ho) P c.pos c.st P.env p r heq
    rw [pwO_std, stepMO_std] at h2
    unfold estep
    rw [h2]
  · cases h

/-! ## Strict oracles from answered queries -/

/-- The answers `K` are the checker's: every recorded result is the call's result. -/
def KOk (K : List (VmQ × Run)) : Prop := ∀ x ∈ K, callResult x.1 = x.2

/-- Answer only from `K`; an unanswered query fails. -/
noncomputable def strictO (K : List (VmQ × Run)) : VmO := fun q =>
  @dite _ (∃ r, (q, r) ∈ K) (Classical.propDecidable _) (fun h => .ok (Classical.choose h))
    (fun _ => .error "E2E: VM query not answered")

theorem strictO_le {K : List (VmQ × Run)} (hK : KOk K) : OLe (strictO K) vmStd := by
  intro q v h
  unfold strictO at h
  split at h
  · rename_i hex
    cases h
    rw [vmStd_eq, hK _ (Classical.choose_spec hex)]
  · cases h

/-! ## The refined machine -/

/-- A configuration of `RCM`. -/
inductive RConf where
  | base (c : Conf)
  | call (I : Intake) (c : EConf) (K : List (VmQ × Run)) (q : VmQ) (cc : CallConf)

/-- The steps of `RCM`. -/
inductive RStep : RConf → RConf → Prop
  | base {a b : Conf} : CM.step a = .ok b → RStep (.base a) (.base b)
  | enter (I : Intake) (c : EConf) (q : VmQ) : RStep (.base (.eng I c)) (.call I c [] q .pre)
  | wasm {I : Intake} {c : EConf} {K : List (VmQ × Run)} {q : VmQ} {cc : CallConf} :
      (∀ r, cc ≠ .fin r) → RStep (.call I c K q cc) (.call I c K q (cstep q cc))
  | next {I : Intake} {c : EConf} {K : List (VmQ × Run)} {q : VmQ} {r : Run} (q' : VmQ) :
      RStep (.call I c K q (.fin r)) (.call I c (K ++ [(q, r)]) q' .pre)
  | resume {I : Intake} {c c' : EConf} {K : List (VmQ × Run)} {q : VmQ} {r : Run} :
      (∀ out, c.pos ≠ .done out) → estepO (strictO (K ++ [(q, r)])) I.prog c = .ok c' →
      RStep (.call I c K q (.fin r)) (.base (.eng I c'))

/-- Runs of `RCM`. -/
inductive RSteps : RConf → RConf → Prop
  | refl (x : RConf) : RSteps x x
  | step {x y z : RConf} : RStep x y → RSteps y z → RSteps x z

theorem RSteps.trans {x y z : RConf} (h1 : RSteps x y) (h2 : RSteps y z) : RSteps x z := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact .step h (ih h2)

theorem RSteps.single {x y : RConf} (h : RStep x y) : RSteps x y := .step h (.refl _)

/-- An engine configuration that is not finished takes an engine step in `CM`. -/
theorem cm_step_eng (I : Intake) (c c' : EConf) (hc : ∀ out, c.pos ≠ .done out)
    (h : estep I.prog c = .ok c') : CM.step (.eng I c) = .ok (.eng I c') := by
  obtain ⟨pos, st⟩ := c
  cases pos with
  | done out => exact absurd rfl (hc out)
  | _ => simp only [CM.step, h]; rfl

/-- The invariant of an `RCM` run started at `a`. -/
def RInv (a : Conf) : RConf → Prop
  | .base b => Steps a b
  | .call I c K q cc => Steps a (.eng I c) ∧ KOk K ∧ CSteps q .pre cc

theorem rinv_step {a : Conf} {x y : RConf} (h : RStep x y) (hx : RInv a x) : RInv a y := by
  cases h with
  | base hs => simp only [RInv] at hx ⊢; exact hx.trans (.step hs (.refl _))
  | enter I c q => simp only [RInv] at hx ⊢; exact ⟨hx, ⟨(by intro y hy; cases hy), CSteps.refl _⟩⟩
  | wasm hnf => simp only [RInv] at hx ⊢; exact ⟨hx.1, hx.2.1, hx.2.2.trans (.step (.refl _))⟩
  | @next I c K q r q' =>
    simp only [RInv] at hx ⊢
    refine ⟨hx.1, ⟨?_, .refl _⟩⟩
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hx.2.1 y hy
    · simp only [List.mem_singleton] at hy
      subst hy
      exact (csteps_fin_iff q r).1 hx.2.2
  | @resume I c c' K q r hc he =>
    simp only [RInv] at hx ⊢
    have hK : KOk (K ++ [(q, r)]) := by
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact hx.2.1 y hy
      · simp only [List.mem_singleton] at hy
        subst hy
        exact (csteps_fin_iff q r).1 hx.2.2
    have hs := estepO_sound (strictO_le hK) I.prog c c' he
    exact hx.1.trans (.step (cm_step_eng I c c' hc hs) (.refl _))

theorem rinv_steps {a : Conf} {x y : RConf} (h : RSteps x y) (hx : RInv a x) : RInv a y := by
  induction h with
  | refl => exact hx
  | step h _ ih => exact ih (rinv_step h hx)

/-- **Soundness of the refinement.** -/
theorem rsteps_sound {a b : Conf} (h : RSteps (.base a) (.base b)) : Steps a b :=
  rinv_steps h (Steps.refl a)

/-- **Completeness of the refinement.** -/
theorem rsteps_of_steps {a b : Conf} (h : Steps a b) : RSteps (.base a) (.base b) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.base hs) ih

/-- `RCM` accepts `(claim, witness)`. -/
def RCMAccepts (cb wb : Bytes) : Prop :=
  ∃ cf, RSteps (.base (.init cb wb)) (.base cf) ∧ cf.accepting = true

/-- **`rcm_iff`: the refined machine with mid-call boundaries decides the `allFeatures` relation.** -/
theorem rcm_iff (cb wb : Bytes) : Tier.rel .allFeatures cb wb ↔ RCMAccepts cb wb := by
  rw [cm_iff]
  constructor
  · rintro ⟨cf, hs, ha⟩; exact ⟨cf, rsteps_of_steps hs, ha⟩
  · rintro ⟨cf, hs, ha⟩; exact ⟨cf, rsteps_sound hs, ha⟩

/-! ## Wasm segments are `RCM` runs between `inCall` boundaries -/

theorem rsteps_of_csteps {I : Intake} {c : EConf} {K : List (VmQ × Run)} {q : VmQ}
    {cc cc' : CallConf} (h : CSteps q cc cc') : RSteps (.call I c K q cc) (.call I c K q cc') := by
  induction h with
  | refl => exact .refl _
  | @step a d _ ih =>
    by_cases ha : ∃ r, a = .fin r
    · obtain ⟨r, rfl⟩ := ha
      exact ih
    · exact .step (.wasm fun r h => ha ⟨r, h⟩) ih

/-- **A Wasm segment is an `RCM` run** from one `inCall` boundary to the next. -/
theorem rsteps_seg (I : Intake) (c : EConf) (K : List (VmQ × Run)) (q : VmQ) (p : Prepared)
    (k : EntK) (a : Nat) (s s' : St) (n : Nat) (h : seg q.cfg p a s = .cont s') (hn : a ≤ n) :
    RSteps (.call I c K q (.ent p k (.cont s) n)) (.call I c K q (.ent p k (.cont s') (n - a))) :=
  rsteps_of_csteps (csteps_seg q p k a s s' n h hn)

/-- **A list of Wasm segments** (`Wasm.foldSegments`) is an `RCM` run. -/
theorem rsteps_foldSegments (I : Intake) (c : EConf) (K : List (VmQ × Run)) (q : VmQ) (p : Prepared)
    (k : EntK) (ks : List Nat) (s s' : St) (n : Nat) (h : foldSegments q.cfg p ks s = .cont s')
    (hn : ks.sum ≤ n) :
    RSteps (.call I c K q (.ent p k (.cont s) n)) (.call I c K q (.ent p k (.cont s') (n - ks.sum))) :=
  rsteps_of_csteps (csteps_foldSegments q p k ks s s' n h hn)

/-! ## Non-vacuity of the cut -/

theorem rsteps_calls_aux (I : Intake) (c c' : EConf) (hc : ∀ out, c.pos ≠ .done out)
    (rest : List VmQ) : ∀ (K0 : List (VmQ × Run)) (q : VmQ),
      estepO (strictO (K0 ++ (q, callResult q) :: rest.map fun x => (x, callResult x))) I.prog c = .ok c' →
      RSteps (.call I c K0 q .pre) (.base (.eng I c')) := by
  induction rest with
  | nil =>
    intro K0 q h
    have hq : CSteps q .pre (.fin (callResult q)) := (csteps_fin_iff q (callResult q)).2 (Eq.refl _)
    exact (rsteps_of_csteps hq).trans (.single (.resume hc h))
  | cons q2 rest ih =>
    intro K0 q h
    have hq : CSteps q .pre (.fin (callResult q)) := (csteps_fin_iff q (callResult q)).2 (Eq.refl _)
    refine (rsteps_of_csteps hq).trans (.step (.next q2) (ih (K0 ++ [(q, callResult q)]) q2 ?_))
    rw [List.append_assoc]
    exact h

/-- **The cut is not vacuous.** If a receipt step from `c` is completed by the answers of the calls
`q :: qs` (each answered with its own result), `RCM` reaches the next engine configuration through
every configuration of every call's machine — every Wasm instruction is its own step. -/
theorem rsteps_through_calls (I : Intake) (c c' : EConf) (hc : ∀ out, c.pos ≠ .done out)
    (q : VmQ) (qs : List VmQ)
    (h : estepO (strictO ((q :: qs).map fun x => (x, callResult x))) I.prog c = .ok c') :
    RSteps (.base (.eng I c)) (.base (.eng I c')) :=
  .step (.enter I c q) (rsteps_calls_aux I c c' hc qs [] q (by rw [List.nil_append]; exact h))

/-! ## `e2e_sound` with mid-call segment boundaries -/

/-- A segment system whose boundaries abstract to `RCM` configurations (mid-call included). -/
structure RSegSystem where
  Template : Type
  Bnd : Type
  Trace : Type
  abs : Bnd → Option RConf
  Holds : Template → Bnd → Bnd → Trace → Prop

/-- The `CM`-level view (only `base` boundaries abstract), for the unchanged wrap obligations. -/
def RSegSystem.toSeg (R : RSegSystem) : SegSystem where
  Template := R.Template
  Bnd := R.Bnd
  Trace := R.Trace
  abs := fun b => match R.abs b with
    | some (.base c) => some c
    | _ => none
  Holds := R.Holds

/-- **Obligation 2 with mid-call boundaries.** -/
def SegSoundR (R : RSegSystem) (Bad : Prop) : Prop :=
  ∀ k b b' tr, R.Holds k b b' tr →
    Bad ∨ ∃ x x', R.abs b = some x ∧ R.abs b' = some x' ∧ RSteps x x'

theorem toSeg_abs {R : RSegSystem} {b : R.Bnd} {c : Conf} (h : R.toSeg.abs b = some c) :
    R.abs b = some (.base c) := by
  simp only [RSegSystem.toSeg] at h
  split at h
  · rename_i c' hb; cases h; exact hb
  · cases h

theorem rsteps_of_bndChain (R : RSegSystem) :
    ∀ (segs : List (R.Template × R.Bnd × R.Bnd × R.Trace)) (b0 bN : R.Bnd) (x0 xN : RConf),
      (∀ x ∈ segs, ∃ c c', R.abs x.2.1 = some c ∧ R.abs x.2.2.1 = some c' ∧ RSteps c c') →
      BndChained b0 (segs.map fun x => (x.2.1, x.2.2.1)) bN →
      R.abs b0 = some x0 → R.abs bN = some xN → RSteps x0 xN
  | [], b0, bN, c0, cN, _, h, h0, hN => by
    cases h; rw [h0] at hN; cases hN; exact .refl _
  | x :: rest, b0, bN, c0, cN, hs, ⟨h1, h2⟩, h0, hN => by
    obtain ⟨c, c', hc, hc', hst⟩ := hs x (by simp)
    subst h1
    rw [h0] at hc; cases hc
    exact hst.trans (rsteps_of_bndChain R rest x.2.2.1 bN c' cN
      (fun y hy => hs y (by simp [hy])) h2 hc' hN)

/-- **`e2e_sound` with segments that may start and end inside a Wasm call.** Obligations 1 and 4
as before (on the `CM`-level view), obligation 2 against `RSteps`. -/
theorem e2e_sound_r (R : RSegSystem) (W : WrapCheck R.toSeg) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (Bad : Prop)
    (ob1 : NvFaithfulE2E R.toSeg W FinalVerify Bad) (ob1b : WrapFinalFaithful R.toSeg W)
    (ob2 : SegSoundR R Bad) (ob4 : WitnessExtraction R.toSeg W Bad)
    (s : PublicStmt) (π : Proof) (hv : FinalVerify s π = true) :
    E2EStmt s ∨ Bad := by
  classical
  rcases ob1 s π hv with hb | ⟨ch, ⟨hholds, hchain⟩, hinit, hfin⟩
  · exact .inr hb
  rcases ob4 s ch.b0 hinit with hb | ⟨secB, w, h0⟩
  · exact .inr hb
  by_cases hbad : Bad
  · exact .inr hbad
  have hsegs : ∀ x ∈ ch.segs, ∃ c c', R.abs x.2.1 = some c ∧ R.abs x.2.2.1 = some c' ∧ RSteps c c' :=
    fun x hx => (ob2 _ _ _ _ (hholds x hx)).resolve_left hbad
  obtain ⟨cf, hN, hacc⟩ := ob1b s ch.bN hfin
  have hrun := rsteps_of_bndChain R ch.segs ch.b0 ch.bN _ _ hsegs hchain (toSeg_abs h0) (toSeg_abs hN)
  exact .inl ((e2e_stmt_iff_cm s).2 ⟨secB, w, cf, rsteps_sound hrun, hacc⟩)

#print axioms estepO_sound
#print axioms rcm_iff
#print axioms rsteps_foldSegments
#print axioms rsteps_through_calls
#print axioms e2e_sound_r

end NearSpecV3.E2E
