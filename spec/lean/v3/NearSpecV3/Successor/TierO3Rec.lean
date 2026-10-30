import NearSpecV3.Successor.TierO3Inv

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O3 step 5e — the recorded call and the action dispatch, `globalActions` off against on

* More rules of `MRX` (`forIn_array`, `liftE_ref`, `modify_off`, `throw_bind_same`, `get_bind'`), and the
  walk tactic `mrx` (closers extend `mrx_close`; `lower_head`/`lower_bind_has` guard the rules so the
  unifier never compares the two runs' differing programs by unfolding them).
* `XU`: the lower errors the recorded call may stop with (exclusions or `unmodeled`), and
  `MRX.tryCatch_unmodeled`: `applyAction`'s handler turns them into exclusions.
* **`functionCallRecorded_global`**: the recorded call at `globalActions` false (configuration `w`)
  against true (`{ w with globalActions := true }`), up to `XU`, with no distribution receipt among
  the new receipts. The steps that differ: the pipeline's `timely` (`liftE_timely`: the lower pipe is
  the upper one or uncertain, `PipeRel.det`; untimely code is the race exclusion), the VM
  (`vm_step` from `vmF_global` and `vmCall_lowQ`), the action log (`managerGlobal_eq_manager` on the
  lower run's raw-free log), `finishActs` against `finishActsGlobal` (`liftE_finishActs`: equal, or the
  lower fails with a `w.shape`/`e.wasm-α` exclusion or `unmodeled: action re-encoding`).
* **`applyAction_global`**: the dispatch (call through the `try … catch`, the global actions are the
  lower run's `w.shape` exclusion, the others `ordinaryAction_rr`), `MRQ` with `ND` of the new receipts.
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged NearSpecV3.Wasm StorageExecution HostComm

/-! ## More rules of the two-run relation -/

namespace MRX
variable {X : String → Prop} {E : Env → Prop}

theorem forIn_list {α σ : Type} (l : List α) (init : σ)
    {f g : α → σ → M (ForInStep σ)} (h : ∀ a s, MRX X E (fun _ => True) (f a s) (g a s)) :
    MRX X E (fun _ => True) (forIn l init f) (forIn l init g) := by
  induction l generalizing init with
  | nil => exact MRX.pure _ trivial
  | cons a t ih =>
    simp only [List.forIn_cons]
    refine MRX.bind (h a init) fun r _ => ?_
    cases r with
    | done s => exact MRX.pure _ trivial
    | yield s => exact ih s

theorem forIn_array {α σ : Type} (l : Array α) (init : σ)
    {f g : α → σ → M (ForInStep σ)} (h : ∀ a s, MRX X E (fun _ => True) (f a s) (g a s)) :
    MRX X E (fun _ => True) (forIn l init f) (forIn l init g) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact forIn_list _ _ h

/-- `liftE` of two `Except` values: where the lower succeeds the upper succeeds with the same
value, and a lower error is in `X` or is the upper's. -/
theorem liftE_ref {α : Type} {Q : α → Prop} {x y : Except String α}
    (hok : ∀ a, x = .ok a → y = .ok a ∧ Q a) (herr : ∀ e, x = .error e → X e ∨ y = .error e) :
    MRX X E Q (StorageExecution.liftE x) (StorageExecution.liftE y) := by
  intro rL rU env hr _
  cases hx : x with
  | ok a =>
    obtain ⟨hy, hq⟩ := hok a hx
    exact Or.inr (Or.inr ⟨a, rL, rU, by simp [StorageExecution.liftE, Except.map],
      by simp [StorageExecution.liftE, hy, Except.map], hr, hq⟩)
  | error e =>
    rcases herr e hx with h | h
    · exact Or.inl ⟨e, by simp [StorageExecution.liftE, Except.map], h⟩
    · exact Or.inr (Or.inl ⟨e, by simp [StorageExecution.liftE, Except.map],
        by simp [StorageExecution.liftE, h, Except.map]⟩)

theorem liftE_same {α : Type} (x : Except String α) :
    MRX X E (fun _ => True) (StorageExecution.liftE x) (StorageExecution.liftE x) :=
  liftE_ref (fun _ h => ⟨h, trivial⟩) (fun _ h => Or.inr h)

/-- A record update off the pipe. -/
theorem modify_off (f : Recording → Recording) (hf : ∀ r q, f { r with pipe := q } = { f r with pipe := q })
    (hp : ∀ r, (f r).pipe = r.pipe) : MRX X E (fun _ => True) (_root_.modify f : M Unit) (_root_.modify f) :=
  MRX.modify (rr_update hf hp)

theorem throwThe_same {α : Type} {Q : α → Prop} (e : String) :
    MRX X E Q (throwThe String e : M α) (throwThe String e) := MRX.throw_same e

theorem throw_bind_same {α β : Type} {Q : β → Prop} (e : String) (f g : α → M β) :
    MRX X E Q (throw e >>= f) (throw e >>= g) := fun _ _ _ _ _ => Or.inr (Or.inl ⟨e, rfl, rfl⟩)

theorem mono {Y : String → Prop} (hXY : ∀ e, X e → Y e) {α : Type} {Q : α → Prop} {x y : M α}
    (h : MRX X E Q x y) : MRX Y E Q x y := by
  intro rL rU env hr he
  rcases h rL rU env hr he with ⟨e, h1, h2⟩ | h1 | h1
  · exact Or.inl ⟨e, h1, hXY e h2⟩
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

end MRX

/-- The lower errors of the recorded call: exclusions, or `unmodeled` errors (which `applyAction`'s
handler turns into exclusions). -/
def XU (e : String) : Prop := isExclusion e = true ∨ e.startsWith "unmodeled" = true

theorem XU.of_exc {e : String} (h : isExclusion e = true) : XU e := Or.inl h
theorem XU.hX : ∀ e, isExclusion e = true → XU e := fun _ h => Or.inl h
theorem Exc.hX : ∀ e, isExclusion e = true → Exc e := fun _ h => h

/-- `applyAction`'s `try … catch`: lower `unmodeled` errors become exclusions. -/
theorem MRX.tryCatch_unmodeled {E : Env → Prop} {α : Type} {Q : α → Prop} {x y : M α}
    (h : MRX XU E Q x y) :
    MRQ E Q (tryCatch x fun e => throw (if e.startsWith "unmodeled" then D3.oodE e else e))
      (tryCatch y fun e => throw (if e.startsWith "unmodeled" then D3.oodE e else e)) := by
  intro rL rU env hr he
  have hl : (tryCatch x fun e => throw (if e.startsWith "unmodeled" then D3.oodE e else e) : M α) rL env =
      Except.tryCatch (x rL env) (fun e => .error (if e.startsWith "unmodeled" then D3.oodE e else e)) := rfl
  have hu : (tryCatch y fun e => throw (if e.startsWith "unmodeled" then D3.oodE e else e) : M α) rU env =
      Except.tryCatch (y rU env) (fun e => .error (if e.startsWith "unmodeled" then D3.oodE e else e)) := rfl
  rw [hl, hu]
  rcases h rL rU env hr he with ⟨e, h1, h2⟩ | ⟨e, h1, h2⟩ | ⟨a, sL, sU, h1, h2, h3, h4⟩
  · rw [h1]
    left
    refine ⟨_, rfl, ?_⟩
    show isExclusion (if e.startsWith "unmodeled" then D3.oodE e else e) = true
    split
    · exact oodE_isExclusion e
    · rcases h2 with h2 | h2
      · exact h2
      · contradiction
  · rw [h1, h2]; exact Or.inr (Or.inl ⟨_, rfl, rfl⟩)
  · rw [h1, h2]; exact Or.inr (Or.inr ⟨a, sL, sU, rfl, rfl, h3, h4⟩)

theorem MRX.get_bind' {X : String → Prop} {E : Env → Prop} {α : Type} {Q : α → Prop} {f g : Recording → M α}
    (h : ∀ r q, PipeRel q r.pipe → MRX X E Q (f { r with pipe := q }) (g r)) :
    MRX X E Q (get >>= f) (get >>= g) := by
  refine MRX.get_bind fun rL rU ⟨h1, h2⟩ => ?_
  have := h rU rL.pipe h2
  rw [← h1] at this
  exact this

/-- The VM step of the recorded call: the two runs' `vm` results are related by `vmF_global`. -/
theorem vm_step {E : Env → Prop} {β : Type} {Q : β → Prop} (w : NearCfg) (hg : w.globalActions = false)
    (code : ByteArray) (m : String) (ctx : CallCtx) (real : TTN.RealStore) (k k' : Run → M β)
    (hl : ∀ l, MRX XU E Q (k (.line l)) (k' (.line l)))
    (hk1 : ∀ l, ∃ K1, k (.line l) = StorageExecution.liftE (D3.lineOutcome l) >>= K1)
    (hd : ∀ s e, LowQ s → MRX XU E Q (k (.done s e)) (k' (.done (setF none (some true) s) e))) :
    MRX XU E Q (StorageExecution.liftE (vmCall wasmFuel w code m ctx real) >>= k)
      (StorageExecution.liftE (vmCall wasmFuel { w with globalActions := true } code m ctx real) >>= k') := by
  intro rL rU env hr he
  rw [MRef.bind_run, MRef.bind_run]
  rcases vmF_global w hg code m ctx real with h | ⟨x, hx, h⟩
  · simp only [] at h
    rw [h]
    cases hv : vmCall wasmFuel w code m ctx real with
    | error e => exact Or.inr (Or.inl ⟨e, rfl, rfl⟩)
    | ok v =>
      cases v with
      | line l => exact hl l rL rU env hr he
      | done s e => exact hd s e (vmCall_lowQ w hg code m ctx real s e hv) rL rU env hr he
  · simp only [] at h
    rw [h]
    obtain ⟨e, he1, hex⟩ := lineOutcome_XG x hx
    obtain ⟨K1, hK⟩ := hk1 s!"unmodeled {x}"
    left
    refine ⟨e, ?_, Or.inl hex⟩
    show k (.line s!"unmodeled {x}") rL env = .error e
    rw [hK, MRef.bind_run]
    simp only [StorageExecution.liftE, he1, Except.map]
    rfl

theorem ND.map {α : Type} {f : α → Rcpt} (h : ∀ a, rcptIsDistribution (f a) = false) (l : List α) :
    ND (l.map f) := by
  intro r hr
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hr
  exact h a

/-- Leaf facts of the walk. -/
macro "ndc" : tactic => `(tactic| first
  | exact True.intro
  | exact nd_action _ _ _ _ _
  | exact nd_data _ _ _ _ _ _
  | (repeat' (first | assumption | exact ND.nil | exact ND.single rfl | exact ND.map (fun _ => rfl) _ | refine ND.append ?_ ?_); done)
  | nd_close)

/-! ## The walk tactic -/

syntax "mrx_close" : tactic

macro "mrx_hX" : tactic => `(tactic| first | assumption | exact Exc.hX | exact XU.hX)

open Lean Elab Tactic Meta in
/-- Succeed when the lower program of an `MRX`/`MRQ` goal is an application of `n`. -/
elab "lower_head " n:ident : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let args := t.getAppArgs
  if args.size < 2 then throwError "lower_head: not a relation goal"
  let x := args[args.size - 2]!
  let c ← realizeGlobalConstNoOverloadWithInfo n
  unless x.getAppFn.isConstOf c do throwError "lower_head: other head"

open Lean Elab Tactic Meta in
/-- Rewrite the goal with the last hypothesis (the equation `split` adds). -/
elab "simp_last_eq" : tactic => withMainContext do
  let some d := (← getLCtx).lastDecl | throwError "simp_last_eq: empty context"
  let stx ← Term.exprToSyntax (mkFVar d.fvarId)
  evalTactic (← `(tactic| simp only [$stx:term]))

open Lean Elab Tactic Meta in
/-- Succeed when the lower program mentions `n`. -/
elab "lower_has " n:ident : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let args := t.getAppArgs
  if args.size < 2 then throwError "lower_has: not a relation goal"
  let x := args[args.size - 2]!
  let c ← realizeGlobalConstNoOverloadWithInfo n
  unless (x.find? (·.isConstOf c)).isSome do throwError "lower_has: absent"

open Lean Elab Tactic Meta in
/-- Succeed when the lower program is a bind whose first action mentions `n`. -/
elab "lower_bind_has " n:ident : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let args := t.getAppArgs
  if args.size < 2 then throwError "lower_bind_has: not a relation goal"
  let x := args[args.size - 2]!
  unless x.isAppOfArity ``Bind.bind 6 do throwError "lower_bind_has: not a bind"
  let a := x.getAppArgs[4]!
  let c ← realizeGlobalConstNoOverloadWithInfo n
  unless (a.find? (·.isConstOf c)).isSome do throwError "lower_bind_has: absent"

macro "mrx" : tactic => `(tactic|
  repeat' (first
    | (lower_head Pure.pure; refine MRX.pure _ ?_; focus ((try dsimp only); ndc; done))
    | (lower_head MonadExcept.throw; exact MRX.throw_same _)
    | (lower_head throwThe; exact MRX.throwThe_same _)
    | mrx_close
    | (lower_head Bind.bind; first
        | (exact MRX.throw_bind_same _ _ _)
        | (rw [managerGlobal_eq_manager _ _ _ (LowQ.noraw ‹_›)])
        | ((refine MRX.bind (MRX.mapM (Q := fun r => rcptIsDistribution r = false) _ fun _ => ?_) fun _ _ => ?_);
            try dsimp only)
        | ((refine MRX.bind (MRX.forIn_array _ _ fun _ _ => ?_) fun _ _ => ?_); try dsimp only)
        | (simp only [pure_bind])
        | (lower_bind_has vmCall; refine vm_step _ ‹_› _ _ _ _ _ _ (fun l => ?_) (fun l => by exact ⟨_, rfl⟩) (fun s e hq => ?_))
        | ((refine MRX.bind (by mrx_close) fun _ _ => ?_); try dsimp only)
        | ((refine MRX.get_bind' fun _ _ _ => ?_); try dsimp only))
    | (lower_head ite; refine MRX.ite _ (fun _ => ?_) (fun _ => ?_))
    | (dsimp only)
    | (simp only [setF, Option.getD, Bool.false_eq_true, ↓reduceIte])
    | (split <;> ((try simp_last_eq); (try dsimp only)))))

macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact MRX.liftE_same _)
macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact MRX.logged (by mrx_hX) (LR.refl _))
macro_rules | `(tactic| mrx_close) => `(tactic| (first | lower_head modify | lower_head setVmErr | lower_head startReceipt | lower_head accountRemovals); exact MRX.modify_off _ (fun _ _ => rfl) (fun _ => rfl))
macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact MRX.throw_same _)

/-! ## The recorded call -/

theorem resolveCode_rr {X : String → Prop} (hX : ∀ e, isExclusion e = true → X e) {E : Env → Prop}
    (c : ActCtx) (st : ActSt) (acct : D2.Acct) :
    MRX X E (fun _ => True) (resolveCode c st acct) (resolveCode c st acct) := by
  unfold resolveCode
  mrx

macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact resolveCode_rr (by mrx_hX) _ _ _)

/-- The code resolution at `timely` false: as at `timely` true, or the race exclusion. -/
theorem resolveCodeBytes_untimely (pol : CodeWitnessPolicy) (s : CodeSources) (pre : PrestateCode) (h : Bytes) :
    resolveCodeBytes pol s pre h false = resolveCodeBytes pol s pre h true ∨
      resolveCodeBytes pol s pre h false = .error raceExclusion := by
  cases pol <;> simp only [resolveCodeBytes, resolveColdCode, resolveCompleteCode] <;>
    repeat' split
  all_goals first | (left; rfl) | (right; rfl) | simp_all

theorem liftE_timely {E : Env → Prop} (pol : CodeWitnessPolicy) (s : CodeSources) (pre : PrestateCode)
    (h : Bytes) (tL tU : Bool) (ht : tL = true → tU = true) :
    MRX XU E (fun _ => True) (StorageExecution.liftE (resolveCodeBytes pol s pre h tL))
      (StorageExecution.liftE (resolveCodeBytes pol s pre h tU)) := by
  cases tL
  · cases tU
    · exact MRX.liftE_same _
    · rcases resolveCodeBytes_untimely pol s pre h with he | he
      · rw [he]; exact MRX.liftE_same _
      · rw [he]
        exact MRX.liftE_ref (fun _ h => by cases h) fun e h => by
          cases h; exact Or.inl (XU.of_exc raceExclusion_isExclusion)
  · rw [ht rfl]; exact MRX.liftE_same _

theorem mapM_err {α β : Type} {f : α → Except String β} {P : String → Prop}
    (h : ∀ a e, f a = .error e → P e) : ∀ (l : List α) e, l.mapM f = .error e → P e
  | [], e, hl => by cases hl
  | a :: l, e, hl => by
    simp only [List.mapM_cons, bind, Except.bind] at hl
    cases hf : f a with
    | error e' => rw [hf] at hl; cases hl; exact h a _ hf
    | ok x =>
      rw [hf] at hl; simp only at hl
      cases hm : l.mapM f with
      | error e' => rw [hm] at hl; cases hl; exact mapM_err h l _ hm
      | ok r => rw [hm] at hl; cases hl

theorem unmodeled_reenc : "unmodeled: action re-encoding".startsWith "unmodeled" = true := by decide +kernel

/-- The lower action-log errors are exclusions or `unmodeled`. -/
theorem finishActs_err (m : D3.MR) (e : String) (h : D3.finishActs m = .error e) : XU e := by
  unfold D3.finishActs at h
  refine mapM_err (fun a e h => ?_) _ e h
  obtain ⟨raw, fc⟩ := a
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h; exact Or.inr unmodeled_reenc
  · split at h
    · cases h; exact Or.inl (Codec.shape_excl _ ‹_›)
    · cases h; exact Or.inl (oodE_isExclusion _)

theorem liftE_finishActs {E : Env → Prop} (m : D3.MR) :
    MRX XU E (fun _ => True) (StorageExecution.liftE (D3.finishActs m))
      (StorageExecution.liftE (finishActsGlobal m)) :=
  MRX.liftE_ref (fun a h => ⟨finishActsGlobal_of_finishActs m a h, trivial⟩)
    fun e h => Or.inl (finishActs_err m e h)

macro_rules | `(tactic| mrx_close) => `(tactic| lower_has resOf; exact liftE_timely _ _ _ _ _ _ (PipeRel.det ‹_› _ _ _))
macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact liftE_finishActs _)

theorem resOf_ga (p : CodeWitnessPolicy) (c : ActCtx) : resOf ⟨true, p⟩ c = resOf ⟨false, p⟩ c := rfl

set_option maxHeartbeats 16000000 in
/-- **O3, recorded call.** -/
theorem functionCallRecorded_global (w : NearCfg) (hg : w.globalActions = false) (p : CodeWitnessPolicy)
    {E : Env → Prop} (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) (har : ND ar.newReceipts) :
    MRX XU E (fun x : ActSt × AR => ND x.2.newReceipts)
      (functionCallRecorded ⟨false, p⟩ w c st ar b)
      (functionCallRecorded ⟨true, p⟩ { w with globalActions := true } c st ar b) := by
  rw [functionCallRecorded_eq_with, functionCallRecorded_eq_with, contractOOD_ga w true, resOf_ga]
  unfold functionCallRecordedWith
  mrx
  all_goals (refine MRX.pure _ ?_)
  all_goals (dsimp only; exact ND.append har (ND.append ‹_› (ND.map (fun _ => rfl) _)))

macro_rules | `(tactic| mrx_close) => `(tactic|
  with_reducible exact MRX.tryCatch_unmodeled (functionCallRecorded_global _ ‹_› _ _ _ _ _ ND.nil))

/-- The lower run's global actions stop with `w.shape`. -/
theorem applyGlobal_false {E : Env → Prop} {Q : ActSt × AR → Prop} (c : ActCtx) (st : ActSt) (a : Act) (b : Base)
    (y : M (ActSt × AR)) : MRQ E Q (applyGlobal false c st a b) y :=
  fun _ _ _ _ _ => Or.inl ⟨_, rfl, by show isExclusion _ = true; decide +kernel⟩

/-- `ordinaryAction` creates no distribution receipt. -/
theorem ordinaryAction_rr {E : Env → Prop} (c : ActCtx) (st : ActSt) (a : Act) :
    MRQ E (fun x : ActSt × AR => ND x.2.newReceipts) (ordinaryAction c st a) (ordinaryAction c st a) := by
  unfold ordinaryAction accountRemovals
  refine MRX.bind (MRX.loggedQ Exc.hX (LRQ.refl_of (applyActionL_nd c st a))) fun out hout => ?_
  refine MRX.bind (MRX.modify_off _ (fun _ _ => rfl) (fun _ => rfl)) fun _ _ => ?_
  exact MRX.pure _ hout

macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact ordinaryAction_rr _ _ _)
macro_rules | `(tactic| mrx_close) => `(tactic| lower_head applyGlobal; exact applyGlobal_false _ _ _ _ _)

set_option maxHeartbeats 16000000 in
/-- **O3, action dispatch.** The recorded call entered through `applyAction`'s `try … catch`, the
global actions (lower: `w.shape`), and the ordinary actions; no distribution receipt is created. -/
theorem applyAction_global (w : NearCfg) (hg : w.globalActions = false) (p : CodeWitnessPolicy)
    {E : Env → Prop} (c : ActCtx) (st : ActSt) (a : Act) :
    MRQ E (fun x : ActSt × AR => ND x.2.newReceipts)
      (StorageExecution.applyAction ⟨false, p⟩ w c st a) (StorageExecution.applyAction ⟨true, p⟩ { w with globalActions := true } c st a) := by
  unfold StorageExecution.applyAction
  mrx

#print axioms functionCallRecorded_global
#print axioms applyAction_global

end NearSpecV3.Successor
