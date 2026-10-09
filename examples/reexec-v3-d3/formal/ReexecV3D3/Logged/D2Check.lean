import ReexecV3D3.Logged.Runtime.D2Check
import ReexecV3D3.Logged.D2Runtime
import NearSpecV3.ChunkValidationD2

/-!
# The D2 checker with every recorded-storage read logged

`checkD2CoreL` is `checkD2Core` with the main transition run lazily over the merged recorded
storage (store tag `0`) and implicit transition `k` over its own `base_state` (tag `k + 1`); the
full reveal and its root check (`tMain.hashOf == prev_state_root`, always true: `hashOf_revealAll`)
are gone. `storesOf witnessBytes` is the tagged store.
-/

namespace ReexecV3D3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2

/-- `RK g n o`: the tagged-store program `n` computes `o` on the store `g`. -/
@[irreducible] def RK {K α : Type} (g : K → Option Bytes) (n : SM K α) (o : Except String α) : Prop :=
  o = SM.run g n

section
variable {K : Type} {g : K → Option Bytes}

theorem RK_bind {α β : Type} {x : Except String α} {x' : SM K α} {f : α → Except String β}
    {f' : α → SM K β} (h1 : RK g x' x) (h2 : ∀ a, RK g (f' a) (f a)) : RK g (x' >>= f') (x >>= f) := by
  unfold RK at h1 h2 ⊢
  rw [h1, SM.run_bind']
  cases SM.run g x' with
  | error e => rfl
  | ok a => exact h2 a

theorem RK_pure {α : Type} (a : α) : RK g (pure a) (pure a) := by unfold RK; rfl
theorem RK_ok {α : Type} (a : α) : RK g (pure a) (.ok a) := by unfold RK; rfl
theorem RK_throw {α : Type} (e : String) : RK g (throw e : SM K α) (throw e) := by unfold RK; rfl
theorem RK_error {α : Type} (e : String) : RK g (throw e : SM K α) (.error e) := by unfold RK; rfl
theorem RK_liftEK {α : Type} (x : Except String α) : RK g (liftEK x) x := by unfold RK; cases x <;> rfl
theorem RK_checkK (b : Bool) (m : String) : RK g (checkK b m) (check b m) := by
  unfold RK; cases b <;> rfl
theorem RK_checkK_true {b : Bool} (m : String) (h : b = true) : RK g (checkK true m) (check b m) := by
  subst h; exact RK_checkK _ _
theorem RK_ite {α : Type} (c c' : Prop) [Decidable c] [Decidable c'] (hc : c = c')
    {x y : Except String α} {x' y' : SM K α} (h1 : RK g x' x) (h2 : RK g y' y) :
    RK g (if c' then x' else y') (if c then x else y) := by
  subst hc; by_cases h : c <;> simp only [h, ite_true, ite_false] <;> assumption

theorem RK_bind_liftEK {α β : Type} {x : Except String α} {f : α → Except String β}
    {f' : α → SM K β} (h2 : ∀ a, x = .ok a → RK g (f' a) (f a)) : RK g (liftEK x >>= f') (x >>= f) := by
  unfold RK at h2 ⊢
  cases x with
  | error e => rfl
  | ok a => exact h2 a rfl

theorem RK_forIn_zipIdx {α β : Type} (l : List α) (b : β) (k0 : Nat) {f : α → β → Except String (ForInStep β)}
    {f' : α × Nat → β → SM K (ForInStep β)}
    (h : ∀ x k b, (x, k) ∈ l.zipIdx k0 → RK g (f' (x, k) b) (f x b)) :
    RK g (forIn (l.zipIdx k0) b f') (forIn l b f) := by
  induction l generalizing b k0 with
  | nil => exact RK_pure b
  | cons x xs ih =>
    simp only [List.zipIdx_cons, List.forIn_cons]
    apply RK_bind (h x k0 b (List.mem_cons_self ..))
    intro r; cases r with
    | done b' => exact RK_pure b'
    | yield b' => exact ih b' (k0 + 1) (fun y k b hm => h y k b (List.mem_cons_of_mem _ hm))

theorem RK_forIn {α β : Type} (l : List α) (b : β) {f : α → β → Except String (ForInStep β)}
    {f' : α → β → SM K (ForInStep β)} (h : ∀ x b, RK g (f' x b) (f x b)) :
    RK g (forIn l b f') (forIn l b f) := by
  induction l generalizing b with
  | nil => exact RK_pure b
  | cons x xs ih =>
    simp only [List.forIn_cons]
    apply RK_bind (h x b)
    intro r; cases r with
    | done b' => exact RK_pure b'
    | yield b' => exact ih b'

theorem RK_mapM {α γ : Type} (l : List γ) {f : γ → Except String α} {f' : γ → SM K α}
    (h : ∀ x, RK g (f' x) (f x)) : RK g (l.mapM f') (l.mapM f) := by
  induction l with
  | nil => exact RK_pure _
  | cons x xs ih =>
    simp only [List.mapM_cons]
    exact RK_bind (h x) (fun a => RK_bind ih (fun b => RK_pure _))

end


theorem RK_keyed {α : Type} {g : Nat × Bytes → Option Bytes} {k : Nat} {s : HStore} {root : Bytes}
    {x : LM α} {o : Except String α} (hg : ∀ h, g (k, h) = hGet s h) (hR : R s root x o id) :
    RK g (SM.mapKey (fun h => (k, h)) (x root)) o := by
  unfold RK; unfold R at hR
  rw [SM.run_mapKey, hR]
  have : (g ∘ fun h => (k, h)) = hGet s := funext hg
  rw [this]; unfold LM.ev; cases SM.run (hGet s) (x root) <;> rfl

theorem implicit_mem {A B : Type} {l1 : List A} {l2 : List B} {x : A × B} {k : Nat}
    (h : (x, k) ∈ (l1.zip l2).zipIdx) : l2[k]? = some x.2 := by
  rw [List.mk_mem_zipIdx_iff_getElem?] at h
  rw [List.getElem?_zip_eq_some] at h
  exact h.2

open Lean Elab Tactic Meta in
/-- Join points for `RK` (identity relation on the join-point arguments). -/
elab "lkk_jp" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← whnfR (← instantiateMVars (← g.getType))
    unless tgt.isAppOfArity ``RK 5 do throwError "lkk_jp: not RK"
    let args := tgt.getAppArgs
    let gs := args[2]!; let n := args[3]!; let o := args[4]!
    let .letE nN tyN vN bN _ := n | throwError "lkk_jp: mirror not a let"
    let .letE nO tyO vO bO _ := o | throwError "lkk_jp: original not a let"
    unless tyN.isForall && tyO.isForall do throwError "lkk_jp: not a join point"
    let mkHJ (jN jO : Expr) : MetaM Expr :=
      forallTelescope tyN fun xs _ => do
        let body ← mkAppM ``RK #[gs, mkAppN jN xs, mkAppN jO xs]
        mkForallFVars xs body
    let hjv ← mkHJ vN vO
    let mH1 ← mkFreshExprSyntheticOpaqueMVar hjv
    let bodyTy ← withLocalDeclD nN tyN fun jN => withLocalDeclD nO tyO fun jO => do
      let hj ← mkHJ jN jO
      withLocalDeclD `hj hj fun h => do
        let r ← mkAppM ``RK #[gs, bN.instantiate1 jN, bO.instantiate1 jO]
        mkForallFVars #[jN, jO, h] r
    let mBody ← mkFreshExprSyntheticOpaqueMVar bodyTy
    g.assign (mkApp3 mBody vN vO mH1)
    let (_, gB) ← mBody.mvarId!.introN 3 [nN, nO, `hj]
    replaceMainGoal [mH1.mvarId!, gB]

open Lean Elab Tactic Meta in
elab "lkk_zeta" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← whnfR (← instantiateMVars (← g.getType))
    unless tgt.isAppOfArity ``RK 5 do throwError "lkk_zeta: not RK"
    let args := tgt.getAppArgs
    let red (e : Expr) : Bool × Expr :=
      match e with
      | .letE _ ty v b _ => if ty.isForall then (false, e) else (true, b.instantiate1 v)
      | _ => (false, e)
    let (c1, n) := red args[3]!
    let (c2, o) := red args[4]!
    unless c1 || c2 do throwError "lkk_zeta: nothing"
    replaceMainGoal [← g.replaceTargetDefEq (mkAppN tgt.getAppFn (args.set! 3 n |>.set! 4 o))]

open Lean Elab Tactic Meta in
elab "lkk_hyp" : tactic => do
  let g ← getMainGoal
  g.withContext do
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ok ← forallTelescopeReducing d.type fun _ b => pure (b.isAppOfArity ``RK 5)
      if !ok then continue
      let s ← saveState
      try
        let gs ← g.apply (mkFVar d.fvarId)
        replaceMainGoal gs
        return
      catch _ => restoreState s
    throwError "lkk_hyp: no hypothesis applies"

syntax "lkk_call" : tactic
macro_rules | `(tactic| lkk_call) => `(tactic| first
  | apply RK_liftEK | apply RK_checkK | apply RK_throw | apply RK_error)

syntax "lkk_step" : tactic
macro_rules | `(tactic| lkk_step) => `(tactic| first
  | (apply RK_ite _ _ rfl)
  | (exact RK_pure _)
  | (exact RK_ok _)
  | (exact RK_throw _)
  | (exact RK_error _)
  | lkk_call
  | (apply RK_bind; apply RK_checkK_true; simp only [hashOf_revealAll (HInv_mkHStore _), beq_self_eq_true])
  | (apply RK_bind_liftEK; intro _ _)
  | lkk_hyp
  | lkk_jp
  | lkk_zeta
  | (apply RK_bind; lkk_call)
  | (apply RK_bind; lkk_hyp)
  | (apply RK_bind; exact RK_pure _)
  | (apply RK_forIn)
  | (apply RK_bind; apply RK_forIn)
  | (apply RK_bind; apply RK_mapM)
  | (dsimp (config := { zeta := false }) only [id])
  | lk_split
  | lk_intro)

macro "lkk" : tactic => `(tactic| repeat (any_goals lkk_step))

theorem checkD2Core_logged (H : ActionHooks) (HL : ActionHooksL)
    (hH : ∀ (s : HStore) (root : Bytes), HInv s → HooksR s root s H HL)
    (allowCodes : Bool) (cb wb : Bytes) (gasCap : Option Nat) :
    RK (storesOf wb) (checkD2CoreL HL allowCodes cb wb gasCap) (checkD2Core H allowCodes cb wb gasCap) := by
  unfold checkD2Core checkD2CoreL
  lkk
  all_goals
    apply RK_bind
    · refine RK_keyed ?_ (R_applyNewChunkD2 H HL _ (hH _ _ (HInv_mkHStore _)) (HInv_mkHStore _) _ _ _ _ _ _ _)
      intro h; simp [storesOf, storesData, storeFn, storesOfW, *]
  all_goals lkk
  all_goals
    apply RK_bind
    · apply RK_forIn_zipIdx
      intro x k b hmem
      have hk := implicit_mem hmem
      lkk
      all_goals
        apply RK_bind
        · refine RK_keyed ?_ (R_applyMissingChunkD2 (HInv_mkHStore _) _ _ _ _)
          intro h; simp [storesOf, storesData, storeFn, storesOfW, *]
      all_goals lkk
  all_goals lkk

/-- **The logged D2 checker computes `checkD2`.** -/
theorem checkD2L_eq (cb wb : Bytes) : SM.run (storesOf wb) (checkD2L cb wb) = checkD2 cb wb := by
  have h := checkD2Core_logged d2Hooks d2HooksL (fun _ _ _ => HooksR_d2 _) false cb wb none
  unfold RK at h; exact h.symm

end ReexecV3D3.Logged
