import NearSpecV3.Successor.StorageExecutionOrig

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 — the flag refactor of the recorder engine changes nothing (`run_eq_orig`)

`StorageExecution` takes `globalActions` and `codePolicy` as a parameter (`Flags`) instead of
reading them from its `Recording` state. `StorageExecutionOrig` is the pre-refactor engine.
`Sim fl xO xN`: from the pre-refactor state `s.withF fl` (the new state plus the two flags) the old
computation returns what the new one returns from `s`, with the flags added back to the final state.
The flags are never written, so the walk below closes every function, and `run_eq_orig` is the
checker-level statement: the recorder engine is the same function as before.
-/

namespace NearSpecV3.Successor.StorageExecution
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged NearSpecV3.Wasm

/-! ### The two engines' `match` auxiliaries

Each `match` of the frozen engine elaborates to its own auxiliary constant. `orig_matchers`
replaces every frozen-engine auxiliary in the goal by an auxiliary of the same type that the goal's
refactored side uses, after checking that the two constants are definitionally equal, so `split`
cases both sides together. The replacement is a definitional change of the goal, rechecked by the
kernel. -/

open Lean Meta Elab Tactic in
elab "orig_matchers" : tactic => do
  liftMetaTactic1 fun g => do
    let env ← getEnv
    let pre := `NearSpecV3.Successor.StorageExecution.Orig
    let t ← instantiateMVars (← g.getType)
    let cs := t.foldConsts (#[] : Array Name) fun c acc =>
      if isMatcherCore env c && !acc.contains c then acc.push c else acc
    let news := cs.filter (fun c => !pre.isPrefixOf c)
    let mut m : Std.HashMap Name Name := {}
    for c in cs do
      if pre.isPrefixOf c then
        let some ci := env.find? c | continue
        let us := ci.levelParams.map Level.param
        for d in news do
          if !m.contains c then
            if let some di := env.find? d then
              if di.type == ci.type && di.levelParams.length == ci.levelParams.length then
                if ← withTransparency .all (isDefEq (.const c us) (.const d us)) then
                  m := m.insert c d
    let t' := t.replace fun e => match e with
      | .const n us => (m.get? n).map (fun b => Expr.const b us)
      | _ => none
    g.replaceTargetDefEq t'

/-- The pre-refactor state for a new state and a flag setting. -/
def Recording.withF (s : Recording) (fl : Flags) : Orig.RecordingO :=
  { toRecording := s, globalActions := fl.globalActions, codePolicy := fl.codePolicy }

/-- The old computation from `s.withF fl` is the new one from `s`, the flags added back. -/
def Sim {α : Type} (fl : Flags) (xO : Orig.M α) (xN : M α) : Prop :=
  ∀ s env, xO (s.withF fl) env = (xN s env).map (fun p => (p.1, p.2.withF fl))

namespace Sim
variable {fl : Flags}

theorem bind_run {σ α β : Type} (x : StateT σ (ReaderT Env (Except String)) α)
    (f : α → StateT σ (ReaderT Env (Except String)) β) (r : σ) (env : Env) :
    (x >>= f) r env = (x r env) >>= (fun p => f p.1 p.2 env) := by
  show (StateT.bind x f) r env = _
  simp only [StateT.bind, bind, ReaderT.bind, Except.bind]

theorem bind {α β : Type} {xO : Orig.M α} {xN : M α} {fO : α → Orig.M β} {fN : α → M β}
    (hx : Sim fl xO xN) (hf : ∀ a, Sim fl (fO a) (fN a)) : Sim fl (xO >>= fO) (xN >>= fN) := by
  intro s env
  rw [bind_run, bind_run, hx s env]
  cases xN s env with
  | error e => rfl
  | ok p => exact hf p.1 p.2 env

/-- Closing a leaf up to definitional equality of the new side (the two engines' `match`
auxiliaries are different constants with the same body). -/
theorem of_eq_right {α : Type} {xO : Orig.M α} {xN xN' : M α} (h : Sim fl xO xN) (e : xN = xN') :
    Sim fl xO xN' := e ▸ h

theorem pure {α : Type} (a : α) : Sim fl (Pure.pure a : Orig.M α) (Pure.pure a : M α) :=
  fun _ _ => rfl

theorem throw {α : Type} (e : String) : Sim fl (MonadExcept.throw e : Orig.M α) (MonadExcept.throw e : M α) :=
  fun _ _ => rfl

theorem throw_bind {α β : Type} (e : String) (fO : α → Orig.M β) (fN : α → M β) :
    Sim fl (MonadExcept.throw e >>= fO) (MonadExcept.throw e >>= fN) :=
  fun _ _ => rfl

theorem get_bind {β : Type} {kO : Orig.RecordingO → Orig.M β} {kN : Recording → M β}
    (h : ∀ s : Recording, Sim fl (kO (s.withF fl)) (kN s)) : Sim fl (MonadState.get >>= kO) (MonadState.get >>= kN) :=
  fun s env => h s s env

theorem get_left {β : Type} {kO : Orig.RecordingO → Orig.M β} {xN : M β}
    (h : ∀ s : Recording, Sim fl (kO (s.withF fl)) xN) : Sim fl (MonadState.get >>= kO) xN :=
  fun s env => h s s env

theorem read_bind {β : Type} {kO : Env → Orig.M β} {kN : Env → M β}
    (h : ∀ e, Sim fl (kO e) (kN e)) : Sim fl (MonadReader.read >>= kO) (MonadReader.read >>= kN) :=
  fun s env => h env s env

theorem modify {fO : Orig.RecordingO → Orig.RecordingO} {fN : Recording → Recording}
    (h : ∀ s, fO (s.withF fl) = (fN s).withF fl) :
    Sim fl (modify fO : Orig.M PUnit) (modify fN : M PUnit) := by
  intro s env
  show Except.ok (PUnit.unit, fO (s.withF fl)) = Except.ok (PUnit.unit, (fN s).withF fl)
  rw [h]

theorem set {sO : Orig.RecordingO} {sN : Recording} (h : sO = sN.withF fl) :
    Sim fl (MonadStateOf.set sO : Orig.M PUnit) (MonadStateOf.set sN : M PUnit) := by
  subst h; intro s env; rfl

theorem ite_congr {β : Type} (c : Prop) [Decidable c] {t e : Orig.M β} {t' e' : M β}
    (ht : c → Sim fl t t') (he : ¬c → Sim fl e e') :
    Sim fl (if c then t else e) (if c then t' else e') := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact ht hc
  · simp only [hc, ite_false]; exact he hc

theorem foldlM {α β : Type} (l : List β) (init : α)
    {f : α → β → Orig.M α} {g : α → β → M α} (h : ∀ a b, Sim fl (f a b) (g a b)) :
    Sim fl (l.foldlM f init) (l.foldlM g init) := by
  induction l generalizing init with
  | nil => exact pure _
  | cons x t ih =>
    simp only [List.foldlM_cons]
    exact bind (h init x) fun a => ih a

theorem forIn_list {α σ : Type} (l : List α) (init : σ)
    {f : α → σ → Orig.M (ForInStep σ)} {g : α → σ → M (ForInStep σ)} (h : ∀ a s, Sim fl (f a s) (g a s)) :
    Sim fl (forIn l init f) (forIn l init g) := by
  induction l generalizing init with
  | nil => exact pure _
  | cons a t ih =>
    simp only [List.forIn_cons]
    refine bind (h a init) fun r => ?_
    cases r with
    | done s => exact pure _
    | yield s => exact ih s

theorem forIn_array {α σ : Type} (l : Array α) (init : σ)
    {f : α → σ → Orig.M (ForInStep σ)} {g : α → σ → M (ForInStep σ)} (h : ∀ a s, Sim fl (f a s) (g a s)) :
    Sim fl (forIn l init f) (forIn l init g) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact forIn_list _ _ h

theorem mapM {α β : Type} (l : List α) {f : α → Orig.M β} {g : α → M β} (h : ∀ a, Sim fl (f a) (g a)) :
    Sim fl (l.mapM f) (l.mapM g) := by
  induction l with
  | nil => exact pure _
  | cons a t ih =>
    simp only [List.mapM_cons]
    exact bind (h a) fun b => bind ih fun _ => pure _

theorem tryCatch {α : Type} {x : Orig.M α} {y : M α} (HO : String → Orig.M α) (HN : String → M α)
    (hx : Sim fl x y) (hH : ∀ e, Sim fl (HO e) (HN e)) :
    Sim fl (MonadExcept.tryCatch x HO) (MonadExcept.tryCatch y HN) := by
  intro s env
  have hl : (MonadExcept.tryCatch x HO : Orig.M α) (s.withF fl) env =
      Except.tryCatch (x (s.withF fl) env) (fun e => HO e (s.withF fl) env) := rfl
  have hr : (MonadExcept.tryCatch y HN : M α) s env =
      Except.tryCatch (y s env) (fun e => HN e s env) := rfl
  rw [hl, hr, hx s env]
  cases y s env with
  | ok p => rfl
  | error e => exact hH e s env

/-! ### Leaves -/

theorem liftE {α : Type} (x : Except String α) : Sim fl (Orig.liftE x) (StorageExecution.liftE x) := by
  intro s env
  cases x <;> rfl

theorem liftE' {α : Type} {x y : Except String α} (h : x = y) :
    Sim fl (Orig.liftE x) (StorageExecution.liftE y) := h ▸ liftE x

theorem okR {α : Type} (x : Option α) (e : String) : Sim fl (Orig.okR x e) (StorageExecution.okR x e) :=
  liftE _

theorem logged {α : Type} (x : LM α) : Sim fl (Orig.logged x) (StorageExecution.logged x) := by
  unfold Orig.logged StorageExecution.logged
  orig_matchers
  refine read_bind fun env => ?_
  dsimp only
  refine get_bind fun s => ?_
  refine bind (set rfl) fun _ => liftE _

end Sim

/-! ### The walk -/

syntax "sim_close" : tactic
-- fallbacks (tried last): equal up to the two engines' distinct `match` auxiliaries
macro_rules | `(tactic| sim_close) => `(tactic| ((with_reducible refine Sim.of_eq_right (Sim.pure _) ?_); rfl))
macro_rules | `(tactic| sim_close) => `(tactic| ((with_reducible refine Sim.of_eq_right (Sim.logged _) ?_); rfl))
macro_rules | `(tactic| sim_close) => `(tactic| ((with_reducible refine Sim.liftE' ?_); rfl))
macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.liftE _)
macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.okR _ _)
macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.logged _)
macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.pure _)
macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.throw _)
macro_rules | `(tactic| sim_close) => `(tactic| ((with_reducible refine Sim.modify ?_); intro _; rfl))

macro "sim_lockstep" : tactic => `(tactic|
  repeat (first
    | sim_close
    | (with_reducible exact Sim.throw_bind _ _ _)
    | ((with_reducible refine Sim.read_bind fun _ => ?_); try dsimp only)
    | ((with_reducible refine Sim.get_bind fun _ => ?_); try dsimp only [Recording.withF])
    | ((with_reducible refine Sim.get_left fun _ => ?_); try dsimp only [Recording.withF])
    | ((with_reducible refine Sim.set ?_); rfl)
    | (with_reducible refine Sim.tryCatch _ _ (by sim_close) fun _ => ?_)
    | ((with_reducible refine Sim.bind (Sim.foldlM _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((with_reducible refine Sim.foldlM _ _ fun _ _ => ?_); try dsimp only)
    | ((with_reducible refine Sim.bind (Sim.forIn_array _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((with_reducible refine Sim.bind (Sim.forIn_list _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((with_reducible refine Sim.bind (Sim.mapM _ fun _ => ?_) fun _ => ?_); try dsimp only)
    | ((with_reducible refine Sim.bind (by sim_close) fun (_, _) => ?_); try dsimp only)
    | ((with_reducible refine Sim.bind (by sim_close) fun _ => ?_); try dsimp only)
    | ((with_reducible refine Sim.bind ?_ fun (_, _) => ?_); try dsimp only)
    | ((with_reducible refine Sim.bind ?_ fun _ => ?_); try dsimp only)
    | (with_reducible refine Sim.ite_congr _ (fun _ => ?_) (fun _ => ?_))
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only)))))

/-! ### Join points

`do` blocks with mutable variables elaborate to join points `have __do_jp := fun … => k; …` used in
several branches. Zeta-reducing them duplicates the continuation in every branch (exponential in the
nesting depth). `sim_let` instead proves the two join points related once (`∀ xs, Sim fl (jO xs)
(jN xs)`) and walks the body with the join points abstract; `sim_hyp` closes a call of the abstract
join points from that hypothesis. A `have` whose value is not a join point is zeta-reduced alone. -/

open Lean Meta Elab Tactic in
elab "sim_let" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t := (← instantiateMVars (← g.getType)).consumeMData
    let_expr Sim α fl lhs rhs := t | throwError "sim_let: not a Sim goal"
    let .letE n ty v b _ := lhs.consumeMData | throwError "sim_let: no let on the left"
    let .letE _ ty' v' b' _ := rhs.consumeMData | throwError "sim_let: no let on the right"
    -- the join point's result type `Orig.M γ` (possibly unfolded to its `StateT` form)
    let resTy? : Expr → MetaM (Option Expr) := fun r => withNewMCtxDepth do
      let γ ← mkFreshTypeMVar
      if ← withReducible (isDefEq r (mkApp (mkConst ``Orig.M) γ)) then
        return some (← instantiateMVars γ)
      return none
    let isJp ← forallTelescope ty fun _ r => do pure (← resTy? r).isSome
    if isJp then
      -- G_A : ∀ xs, Sim fl (v xs) (v' xs)
      let gaTy ← forallTelescope ty fun xs r => do
        let some γ ← resTy? r | throwError "sim_let: join point type"
        mkForallFVars xs (mkAppN (mkConst ``Sim) #[γ, fl, mkAppN v xs, mkAppN v' xs])
      let gA ← mkFreshExprSyntheticOpaqueMVar gaTy (tag := n)
      -- G_B : ∀ jO jN, (∀ xs, Sim fl (jO xs) (jN xs)) → Sim fl (b jO) (b' jN)
      let gbTy ← withLocalDeclD `jO ty fun jO => withLocalDeclD `jN ty' fun jN => do
        let hTy ← forallTelescope ty fun xs r => do
          let some γ ← resTy? r | throwError "sim_let: join point type"
          mkForallFVars xs (mkAppN (mkConst ``Sim) #[γ, fl, mkAppN jO xs, mkAppN jN xs])
        withLocalDeclD `hj hTy fun hj => do
          mkForallFVars #[jO, jN, hj] (mkAppN (mkConst ``Sim) #[α, fl, b.instantiate1 jO, b'.instantiate1 jN])
      let gB ← mkFreshExprSyntheticOpaqueMVar gbTy (tag := n)
      g.assign (mkAppN gB #[v, v', gA])
      replaceMainGoal [gA.mvarId!, gB.mvarId!]
    else
      let g' ← mkFreshExprSyntheticOpaqueMVar
        (mkAppN (mkConst ``Sim) #[α, fl, b.instantiate1 v, b'.instantiate1 v']) (tag := n)
      g.assign g'
      replaceMainGoal [g'.mvarId!]

open Lean Meta Elab Tactic in
elab "sim_hyp" : tactic => do
  let g ← getMainGoal
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let ok ← withReducible <| observing? do
      let gs ← g.apply (mkFVar d.fvarId)
      unless gs.isEmpty do throwError "sim_hyp: subgoals"
    if ok.isSome then return
  throwError "sim_hyp: no hypothesis applies"

open Lean Meta Elab Tactic in
/-- `intro` only on a syntactic `∀` (never unfolds `Sim`). -/
elab "sim_intro" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.consumeMData.isForall do throwError "sim_intro: not a ∀"
  let (_, g') ← g.intro1
  replaceMainGoal [g']

/-- The walk for bodies with join points: `have` is not zeta-reduced (`sim_let`). -/
macro "sim_lockstep_jp" : tactic => `(tactic|
  repeat (first
    | sim_intro
    | sim_close
    | sim_hyp
    | sim_let
    | (with_reducible exact Sim.throw_bind _ _ _)
    | ((with_reducible refine Sim.read_bind fun _ => ?_); try dsimp (config := {zeta := false}) only)
    | ((with_reducible refine Sim.get_bind fun _ => ?_); try dsimp (config := {zeta := false}) only [Recording.withF])
    | ((with_reducible refine Sim.get_left fun _ => ?_); try dsimp (config := {zeta := false}) only [Recording.withF])
    | ((with_reducible refine Sim.set ?_); rfl)
    | (with_reducible refine Sim.tryCatch _ _ (by sim_close) fun _ => ?_)
    | ((with_reducible refine Sim.bind (Sim.foldlM _ _ fun _ _ => ?_) fun _ => ?_); try dsimp (config := {zeta := false}) only)
    | ((with_reducible refine Sim.foldlM _ _ fun _ _ => ?_); try dsimp (config := {zeta := false}) only)
    | ((with_reducible refine Sim.bind (Sim.forIn_array _ _ fun _ _ => ?_) fun _ => ?_); try dsimp (config := {zeta := false}) only)
    | ((with_reducible refine Sim.bind (Sim.forIn_list _ _ fun _ _ => ?_) fun _ => ?_); try dsimp (config := {zeta := false}) only)
    | ((with_reducible refine Sim.bind (Sim.mapM _ fun _ => ?_) fun _ => ?_); try dsimp (config := {zeta := false}) only)
    | ((with_reducible refine Sim.bind (by sim_close) fun _ => ?_); try dsimp (config := {zeta := false}) only)
    | ((with_reducible refine Sim.bind ?_ fun _ => ?_); try dsimp (config := {zeta := false}) only)
    | (with_reducible refine Sim.ite_congr _ (fun _ => ?_) (fun _ => ?_))
    | (split <;> (rename_i hsplit; (try simp (config := {zeta := false}) only [hsplit]); (try dsimp (config := {zeta := false}) only)))))

macro "sim_step_jp" : tactic => `(tactic|
  (first
    | sim_intro
    | sim_close
    | sim_hyp
    | sim_let
    | (with_reducible exact Sim.throw_bind _ _ _)
    | ((with_reducible refine Sim.read_bind fun _ => ?_); try dsimp (config := {zeta := false}) only)
    | ((with_reducible refine Sim.get_bind fun _ => ?_); try dsimp (config := {zeta := false}) only [Recording.withF])
    | ((with_reducible refine Sim.get_left fun _ => ?_); try dsimp (config := {zeta := false}) only [Recording.withF])
    | ((with_reducible refine Sim.set ?_); rfl)
    | (with_reducible refine Sim.tryCatch _ _ (by sim_close) fun _ => ?_)
    | ((with_reducible refine Sim.bind (Sim.foldlM _ _ fun _ _ => ?_) fun _ => ?_); try dsimp (config := {zeta := false}) only)
    | ((with_reducible refine Sim.foldlM _ _ fun _ _ => ?_); try dsimp (config := {zeta := false}) only)
    | ((with_reducible refine Sim.bind (Sim.forIn_array _ _ fun _ _ => ?_) fun _ => ?_); try dsimp (config := {zeta := false}) only)
    | ((with_reducible refine Sim.bind (Sim.forIn_list _ _ fun _ _ => ?_) fun _ => ?_); try dsimp (config := {zeta := false}) only)
    | ((with_reducible refine Sim.bind (Sim.mapM _ fun _ => ?_) fun _ => ?_); try dsimp (config := {zeta := false}) only)
    | ((with_reducible refine Sim.bind (by sim_close) fun _ => ?_); try dsimp (config := {zeta := false}) only)
    | ((with_reducible refine Sim.bind ?_ fun _ => ?_); try dsimp (config := {zeta := false}) only)
    | (with_reducible refine Sim.ite_congr _ (fun _ => ?_) (fun _ => ?_))
    | (split <;> (rename_i hsplit; (try simp (config := {zeta := false}) only [hsplit]); (try dsimp (config := {zeta := false}) only)))))

macro "sim_walk_jp" : tactic => `(tactic| (sim_lockstep_jp; iterate 5 all_goals sim_lockstep_jp))

/-- Lean's `repeat` stops silently at its recursion depth on long bodies; further passes resume. -/
macro "sim_walk" : tactic => `(tactic| (sim_lockstep; iterate 5 all_goals sim_lockstep))

section
variable {fl : Flags}

theorem Sim.startReceipt  :
    Sim fl (Orig.startReceipt) (StorageExecution.startReceipt) := by
  unfold Orig.startReceipt StorageExecution.startReceipt
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.startReceipt )

theorem Sim.modifyPipe (f : Pipeline.Pipe → Pipeline.Pipe) :
    Sim fl (Orig.modifyPipe f) (StorageExecution.modifyPipe f) := by
  unfold Orig.modifyPipe StorageExecution.modifyPipe
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.modifyPipe _)

theorem Sim.setVmErr (e : String) :
    Sim fl (Orig.setVmErr e) (StorageExecution.setVmErr e) := by
  unfold Orig.setVmErr StorageExecution.setVmErr
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.setVmErr _)

theorem Sim.modifyDetail (f : ObsDetail → ObsDetail) :
    Sim fl (Orig.modifyDetail f) (StorageExecution.modifyDetail f) := by
  unfold Orig.modifyDetail StorageExecution.modifyDetail
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.modifyDetail _)

theorem Sim.pushAttrib (ids : List Bytes) (d : List (Bytes × Option Bytes) × List (Bytes × Option Bytes)) :
    Sim fl (Orig.pushAttrib ids d) (StorageExecution.pushAttrib ids d) := by
  unfold Orig.pushAttrib StorageExecution.pushAttrib
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.pushAttrib _ _)

theorem Sim.softExceeded  :
    Sim fl (Orig.softExceeded) (StorageExecution.softExceeded) := by
  unfold Orig.softExceeded StorageExecution.softExceeded
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.softExceeded )

theorem Sim.accountRemovals (b a : Ovl) :
    Sim fl (Orig.accountRemovals b a) (StorageExecution.accountRemovals b a) := by
  unfold Orig.accountRemovals StorageExecution.accountRemovals
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.accountRemovals _ _)

theorem Sim.ordinaryAction (c : ActCtx) (st : ActSt) (a : Act) :
    Sim fl (Orig.ordinaryAction c st a) (StorageExecution.ordinaryAction c st a) := by
  unfold Orig.ordinaryAction StorageExecution.ordinaryAction
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.ordinaryAction _ _ _)

theorem Sim.resolveCode (c : ActCtx) (st : ActSt) (acct : D2.Acct) :
    Sim fl (Orig.resolveCode c st acct) (StorageExecution.resolveCode c st acct) := by
  unfold Orig.resolveCode StorageExecution.resolveCode
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.resolveCode _ _ _)

theorem Sim.getR (o : Ovl) (k : Bytes) (w : String) :
    Sim fl (Orig.getR o k w) (StorageExecution.getR o k w) := by
  unfold Orig.getR StorageExecution.getR
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.getR _ _ _)

theorem Sim.getAcctR (o : Ovl) (k : Bytes) :
    Sim fl (Orig.getAcctR o k) (StorageExecution.getAcctR o k) := by
  unfold Orig.getAcctR StorageExecution.getAcctR
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.getAcctR _ _)

theorem Sim.getIndicesR (o : Ovl) (k : Bytes) (w : String) :
    Sim fl (Orig.getIndicesR o k w) (StorageExecution.getIndicesR o k w) := by
  unfold Orig.getIndicesR StorageExecution.getIndicesR
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.getIndicesR _ _ _)

theorem Sim.containsR (o : Ovl) (k : Bytes) (w : String) :
    Sim fl (Orig.containsR o k w) (StorageExecution.containsR o k w) := by
  unfold Orig.containsR StorageExecution.containsR
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.containsR _ _ _)

theorem Sim.finalizeR (o : Ovl) :
    Sim fl (Orig.finalizeR o) (StorageExecution.finalizeR o) := by
  unfold Orig.finalizeR StorageExecution.finalizeR
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.finalizeR _)

theorem Sim.trieFindR (k : Bytes) :
    Sim fl (Orig.trieFindR k) (StorageExecution.trieFindR k) := by
  unfold Orig.trieFindR StorageExecution.trieFindR
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.trieFindR _)

theorem Sim.validatorUpdateR (l : Layout) (own : Nat) (o : Ovl) (f : ValidatorUpdateFacts) (ps : List (Bytes × Nat)) :
    Sim fl (Orig.validatorUpdateR l own o f ps) (StorageExecution.validatorUpdateR l own o f ps) := by
  unfold Orig.validatorUpdateR StorageExecution.validatorUpdateR
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.validatorUpdateR _ _ _ _ _)

theorem Sim.schedOvlR (prims : Prims) (ctx : ApplyCtx) (o : Ovl) :
    Sim fl (Orig.schedOvlR prims ctx o) (StorageExecution.schedOvlR prims ctx o) := by
  unfold Orig.schedOvlR StorageExecution.schedOvlR
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.schedOvlR _ _ _)

theorem Sim.bandwidthRequestsR (env : Env) (rs : RS) :
    Sim fl (Orig.bandwidthRequestsR env rs) (StorageExecution.bandwidthRequestsR env rs) := by
  unfold Orig.bandwidthRequestsR StorageExecution.bandwidthRequestsR
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.bandwidthRequestsR _ _)

theorem Sim.processTxR (env : Env) (rs : RS × List Bytes) (tf : TxD2 × Bool) :
    Sim fl (Orig.processTxR env rs tf) (StorageExecution.processTxR env rs tf) := by
  unfold Orig.processTxR StorageExecution.processTxR
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.processTxR _ _ _)

theorem Sim.forwardOrBufferR (env : Env) (rs : RS) (r : Rcpt) :
    Sim fl (Orig.forwardOrBufferR env rs r) (StorageExecution.forwardOrBufferR fl.globalActions env rs r) := by
  unfold Orig.forwardOrBufferR StorageExecution.forwardOrBufferR
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.forwardOrBufferR _ _ _)

theorem Sim.delayPopR (env : Env) (fuel : Nat) (rs : RS) :
    Sim fl (Orig.delayPopR env fuel rs) (StorageExecution.delayPopR fl.globalActions env fuel rs) := by
  unfold Orig.delayPopR StorageExecution.delayPopR
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.delayPopR _ _ _)

theorem Sim.forwardFromBufferR (env : Env) (rs : RS) :
    Sim fl (Orig.forwardFromBufferR env rs) (StorageExecution.forwardFromBufferR fl.globalActions env rs) := by
  unfold Orig.forwardFromBufferR StorageExecution.forwardFromBufferR
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.forwardFromBufferR _ _)

theorem Sim.decodeStoredRcptR (b : Bytes) (w : String) :
    Sim fl (Orig.decodeStoredRcptR b w) (StorageExecution.decodeStoredRcptR fl.globalActions b w) := by
  unfold Orig.decodeStoredRcptR StorageExecution.decodeStoredRcptR
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.decodeStoredRcptR _ _)

theorem Sim.pipeDecode  :
    Sim fl (Orig.pipeDecode) (StorageExecution.pipeDecode fl.globalActions) := by
  unfold Orig.pipeDecode StorageExecution.pipeDecode
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.pipeDecode )

theorem Sim.scheduleDelayed (env : Env) (rs : RS) :
    Sim fl (Orig.scheduleDelayed env rs) (StorageExecution.scheduleDelayed fl.globalActions env rs) := by
  unfold Orig.scheduleDelayed StorageExecution.scheduleDelayed
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.scheduleDelayed _ _)

theorem Sim.applyGlobal (c : ActCtx) (st : ActSt) (a : Act) (b : Base) :
    Sim fl (Orig.applyGlobal c st a b) (StorageExecution.applyGlobal fl.globalActions c st a b) := by
  unfold Orig.applyGlobal StorageExecution.applyGlobal
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.applyGlobal _ _ _ _)

theorem Sim.functionCallRecordedF (F : NearCfg → Nat → Nat) (cfg : NearCfg) (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) :
    Sim fl (Orig.functionCallRecordedF F cfg c st ar b) (StorageExecution.functionCallRecordedF fl F cfg c st ar b) := by
  unfold Orig.functionCallRecordedF StorageExecution.functionCallRecordedF
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.functionCallRecordedF _ _ _ _ _ _)

theorem Sim.functionCallRecorded (cfg : NearCfg) (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) :
    Sim fl (Orig.functionCallRecorded cfg c st ar b) (StorageExecution.functionCallRecorded fl cfg c st ar b) := by
  unfold Orig.functionCallRecorded StorageExecution.functionCallRecorded
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.functionCallRecorded _ _ _ _ _)

theorem Sim.applyAction (cfg : NearCfg) (c : ActCtx) (st : ActSt) (a : Act) :
    Sim fl (Orig.applyAction cfg c st a) (StorageExecution.applyAction fl cfg c st a) := by
  unfold Orig.applyAction StorageExecution.applyAction
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.applyAction _ _ _ _)

theorem Sim.actionLoop (hooks : NearCfg) (env : Env) (r : Rcpt) (a : ActionR)
    (inputs : List (Option Bytes)) (deployed attempted : List Bytes) (i : Nat) (acts : List Act)
    (acc : ActSt × AR) :
    Sim fl (Orig.actionLoop hooks env r a inputs deployed attempted i acts acc)
      (StorageExecution.actionLoop fl hooks env r a inputs deployed attempted i acts acc) := by
  induction acts generalizing i acc with
  | nil => exact Sim.pure _
  | cons act rest ih =>
    obtain ⟨st, res⟩ := acc
    unfold Orig.actionLoop StorageExecution.actionLoop
    orig_matchers
    sim_walk
    all_goals first | exact ih _ _

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.actionLoop _ _ _ _ _ _ _ _ _ _)

theorem Sim.emitReceipts (env : Env) (parent : Bytes) (rs : RS) (k : Nat) (l : List Rcpt) :
    Sim fl (Orig.emitReceipts env parent rs k l)
      (StorageExecution.emitReceipts fl.globalActions env parent rs k l) := by
  induction l generalizing rs k with
  | nil => exact Sim.pure _
  | cons nr rest ih =>
    unfold Orig.emitReceipts StorageExecution.emitReceipts
    orig_matchers
    sim_walk
    all_goals first | exact ih _ _

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.emitReceipts _ _ _ _ _)

set_option maxHeartbeats 0 in
theorem Sim.applyActionReceipt (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt) (a : ActionR) :
    Sim fl (Orig.applyActionReceipt hooks env rs r a)
      (StorageExecution.applyActionReceipt fl hooks env rs r a) := by
  unfold Orig.applyActionReceipt StorageExecution.applyActionReceipt
  orig_matchers
  sim_walk_jp

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.applyActionReceipt _ _ _ _ _)

theorem Sim.processReceipt (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt) :
    Sim fl (Orig.processReceipt hooks env rs r) (StorageExecution.processReceipt fl hooks env rs r) := by
  unfold Orig.processReceipt StorageExecution.processReceipt
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.processReceipt _ _ _ _)

theorem Sim.processWithTotals (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt) :
    Sim fl (Orig.processWithTotals hooks env rs r)
      (StorageExecution.processWithTotals fl hooks env rs r) := by
  unfold Orig.processWithTotals StorageExecution.processWithTotals
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.processWithTotals _ _ _ _)

theorem Sim.drain (hooks : NearCfg) (env : Env) (fuel : Nat) (rs : RS) :
    Sim fl (Orig.processWithInstant.drain hooks env fuel rs)
      (StorageExecution.processWithInstant.drain fl hooks env fuel rs) := by
  induction fuel generalizing rs with
  | zero => exact Sim.throw _
  | succ n ih =>
    unfold Orig.processWithInstant.drain StorageExecution.processWithInstant.drain
    orig_matchers
    sim_walk
    all_goals first | exact ih _

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.drain _ _ _ _)

theorem Sim.processWithInstant (hooks : NearCfg) (env : Env) (rs : RS) (r : Rcpt) :
    Sim fl (Orig.processWithInstant hooks env rs r)
      (StorageExecution.processWithInstant fl hooks env rs r) := by
  unfold Orig.processWithInstant StorageExecution.processWithInstant
  orig_matchers
  sim_walk

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.processWithInstant _ _ _ _)

theorem Sim.processLocals (hooks : NearCfg) (env : Env) (rs : RS) (l : List Rcpt) :
    Sim fl (Orig.processLocals hooks env rs l) (StorageExecution.processLocals fl hooks env rs l) := by
  unfold Orig.processLocals StorageExecution.processLocals
  orig_matchers
  sim_walk

theorem Sim.processDelayedLoop (hooks : NearCfg) (env : Env) (fuel : Nat) (rs : RS) :
    Sim fl (Orig.processDelayedLoop hooks env fuel rs)
      (StorageExecution.processDelayedLoop fl hooks env fuel rs) := by
  induction fuel generalizing rs with
  | zero => exact Sim.pure _
  | succ n ih =>
    unfold Orig.processDelayedLoop StorageExecution.processDelayedLoop
    orig_matchers
    sim_walk
    all_goals first | exact ih _

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.processDelayedLoop _ _ _ _)

theorem Sim.processDelayed (hooks : NearCfg) (env : Env) (fuel : Nat) (rs : RS) :
    Sim fl (Orig.processDelayed hooks env fuel rs)
      (StorageExecution.processDelayed fl hooks env fuel rs) := by
  unfold Orig.processDelayed StorageExecution.processDelayed
  orig_matchers
  sim_walk

theorem Sim.processIncoming (hooks : NearCfg) (env : Env) (rs : RS) (l : List Rcpt) :
    Sim fl (Orig.processIncoming hooks env rs l) (StorageExecution.processIncoming fl hooks env rs l) := by
  unfold Orig.processIncoming StorageExecution.processIncoming
  orig_matchers
  sim_walk

theorem Sim.yieldLoop (env : Env) (next fuel : Nat) (x : RS × Nat × Nat) :
    Sim fl (Orig.yieldLoop env next fuel x) (StorageExecution.yieldLoop fl.globalActions env next fuel x) := by
  induction fuel generalizing x with
  | zero => obtain ⟨rs, i, k⟩ := x; exact Sim.pure _
  | succ n ih =>
    obtain ⟨rs, i, k⟩ := x
    unfold Orig.yieldLoop StorageExecution.yieldLoop
    orig_matchers
    sim_walk
    all_goals first | exact ih _

macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.processLocals _ _ _ _)
macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.processDelayed _ _ _ _)
macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.processIncoming _ _ _ _)
macro_rules | `(tactic| sim_close) => `(tactic| with_reducible exact Sim.yieldLoop _ _ _ _)

theorem Sim.applyNewChunkD2 (hooks : NearCfg) (prims : Prims) (env : Env) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (lastProps : List (Bytes × Nat)) (incoming : List Rcpt)
    (txs : List (TxD2 × Bool)) (ownCong : Congestion) :
    Sim fl (Orig.applyNewChunkD2 hooks prims env t vu lastProps incoming txs ownCong)
      (StorageExecution.applyNewChunkD2 fl hooks prims env t vu lastProps incoming txs ownCong) := by
  unfold Orig.applyNewChunkD2 StorageExecution.applyNewChunkD2
  orig_matchers
  sim_walk

end

/-- **The flag refactor is behaviour-preserving.** The recorder engine with the flags as parameters
is the pre-refactor engine (flags in the `Recording` state), on every input. -/
theorem run_eq_orig (cfg : NearCfg) (prims : Prims) (env : Env) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (props : List (Bytes × Nat)) (incoming : List Rcpt)
    (txs : List (TxD2 × Bool)) (congestion : Congestion) (globalActions : Bool)
    (codePolicy : CodeWitnessPolicy) :
    run cfg prims env t vu props incoming txs congestion globalActions codePolicy =
      Orig.run cfg prims env t vu props incoming txs congestion globalActions codePolicy := by
  unfold run Orig.run
  have h := Sim.applyNewChunkD2 (fl := { globalActions, codePolicy }) cfg prims env t vu props incoming
    txs congestion { observe := cfg.observeDetail } env
  simp only [StateT.run]
  rw [show ({ globalActions, codePolicy, observe := cfg.observeDetail } : Orig.RecordingO) =
    Recording.withF { observe := cfg.observeDetail } { globalActions, codePolicy } from rfl, h]
  cases applyNewChunkD2 { globalActions, codePolicy } cfg prims env t vu props incoming txs congestion
    { observe := cfg.observeDetail } env <;> rfl

#print axioms run_eq_orig

end NearSpecV3.Successor.StorageExecution
