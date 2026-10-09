import Lean
import NearSpecV3.Logged.D2Queues
import NearSpecV3.D2.Actions

/-!
# Lockstep tactic for `R` (mirror vs original)

`lk` walks a mirror and its original together: `if`s with the same condition (`R_ite`), binds
whose heads are related by a known `R`-lemma (`lk_call`, extended with `macro_rules` as mirrors are
proved), `pure`/`throw` leaves, and `match`es (split once on the mirror side; the original's match
on the same discriminant is reduced with the case equation).
-/

namespace NearSpecV3.D2

open NearSpec NearSpecV3

@[reducible] def ActSt.wt (st : ActSt) (t : PTrie) : ActSt := { st with o := st.o.wt t }
@[reducible] def ActCtx.ws (c : ActCtx) (es : HStore) : ActCtx := { c with env := c.env.ws es }

end NearSpecV3.D2

namespace NearSpecV3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2

/-- Put the revealed trie back into the states inside a value (identity on non-states). -/
class WT (α : Type) where
  wt : α → PTrie → α

instance (priority := low) instWTDefault {α : Type} : WT α := ⟨fun a _ => a⟩
@[reducible] instance instWTOvl : WT Ovl := ⟨Ovl.wt⟩
@[reducible] instance instWTRS : WT RS := ⟨RS.wt⟩
@[reducible] instance instWTActSt : WT ActSt := ⟨ActSt.wt⟩
@[reducible] instance instWTProd {α β : Type} [WT α] [WT β] : WT (α × β) :=
  ⟨fun p t => (WT.wt p.1 t, WT.wt p.2 t)⟩

section
variable {s : HStore} {root : Bytes}

theorem R_liftE {α : Type} (x : Except String α) : R s root (liftE x) x id := by unfold R; cases x <;> rfl

theorem R_foldlM' {α β γ : Type} (φ : β → α) (f : α → γ → Except String α) (f' : β → γ → LM β)
    (h : ∀ b x, R s root (f' b x) (f (φ b) x) φ) :
    ∀ (l : List γ) (b : β), R s root (l.foldlM f' b) (l.foldlM f (φ b)) φ
  | [], b => R_pure rfl
  | x :: xs, b => by
    simp only [List.foldlM_cons]
    exact R_bind (h b x) (fun b' => R_foldlM' φ f f' h xs b')

theorem R_foldlM {α β γ : Type} {φ : β → α} {f : α → γ → Except String α} {f' : β → γ → LM β}
    {l : List γ} {b : β} {ob : α} (h : ∀ b x, R s root (f' b x) (f (φ b) x) φ) (hb : ob = φ b) :
    R s root (l.foldlM f' b) (l.foldlM f ob) φ := hb ▸ R_foldlM' φ f f' h l b

theorem R_mapM {α γ : Type} (f : γ → Except String α) (f' : γ → LM α)
    (h : ∀ x, R s root (f' x) (f x) id) : ∀ (l : List γ), R s root (l.mapM f') (l.mapM f) id := by
  intro l
  unfold R at h ⊢
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, LM.ev_bind]
    rw [h x]
    cases LM.ev s root (f' x) with
    | error e => rfl
    | ok a =>
      simp only [Except.map, ex_ok_bind, bind, Except.bind] at ih ⊢
      rw [ih]
      cases LM.ev s root (List.mapM f' xs) <;> rfl

theorem R_foldlM_wt {α γ : Type} [WT α] {f : α → γ → Except String α} {f' : α → γ → LM α}
    {l : List γ} {b : α} {ob : α}
    (h : ∀ b x, R s root (f' b x) (f (WT.wt b (preT s root)) x) (fun x => WT.wt x (preT s root)))
    (hb : ob = WT.wt b (preT s root)) :
    R s root (l.foldlM f' b) (l.foldlM f ob) (fun x => WT.wt x (preT s root)) := R_foldlM h hb

/-- A mirror bind whose head is a pure read of the original. -/
theorem R_bind_ok {α β β' : Type} {x' : LM α} {a : α} {f' : α → LM β'} {o : Except String β} {ψ : β' → β}
    (h1 : LM.ev s root x' = .ok a) (h2 : R s root (f' a) o ψ) : R s root (x' >>= f') o ψ := by
  unfold R at h2 ⊢; rw [h2, LM.ev_bind, h1]; rfl

theorem foldl_ovl_wt {β : Type} (t : PTrie) (g : Ovl → β → Ovl) (l : List β) (o : Ovl)
    (hg : ∀ o b, g (o.wt t) b = (g o b).wt t) : l.foldl g (o.wt t) = (l.foldl g o).wt t :=
  List.foldl_hom (fun (x : Ovl) => x.wt t) hg

theorem foldl_rs_wt {β : Type} (t : PTrie) (g : RS → β → RS) (l : List β) (rs : RS)
    (hg : ∀ r b, g (r.wt t) b = (g r b).wt t) : l.foldl g (rs.wt t) = (l.foldl g rs).wt t :=
  List.foldl_hom (fun (x : RS) => x.wt t) hg

theorem foldl_hom_wt {β : Type} {t : PTrie} {g : Ovl → β → Ovl} {l : List β} {init oinit : Ovl}
    (h1 : oinit = init.wt t) (hg : ∀ o b, g (o.wt t) b = (g o b).wt t) : l.foldl g oinit = (l.foldl g init).wt t := by
  subst h1; exact List.foldl_hom (fun (x : Ovl) => x.wt t) hg

theorem foldl_hom_rs {β : Type} {t : PTrie} {g : RS → β → RS} {l : List β} {init oinit : RS}
    (h1 : oinit = init.wt t) (hg : ∀ r b, g (r.wt t) b = (g r b).wt t) : l.foldl g oinit = (l.foldl g init).wt t := by
  subst h1; exact List.foldl_hom (fun (x : RS) => x.wt t) hg

theorem ovl_remove_congr {t : PTrie} {a b : Ovl} (k : Bytes) (h : a = b.wt t) :
    a.remove k = (b.remove k).wt t := by subst h; rfl
theorem ovl_set_congr {t : PTrie} {a b : Ovl} (k v : Bytes) (h : a = b.wt t) :
    a.set k v = (b.set k v).wt t := by subst h; rfl
theorem ovl_setAK_congr {t : PTrie} {a b : Ovl} (x : Bytes) (pk : PublicKey) (k : AK) (h : a = b.wt t) :
    a.setAK x pk k = (b.setAK x pk k).wt t := by subst h; rfl
theorem ovl_setAcct_congr {t : PTrie} {a b : Ovl} (x : Bytes) (ac : Acct) (h : a = b.wt t) :
    a.setAcct x ac = (b.setAcct x ac).wt t := by subst h; rfl
theorem ovl_commit_congr {t : PTrie} {a b : Ovl} (h : a = b.wt t) : a.commit = b.commit.wt t := by subst h; rfl

end

/-- Close an equation between an original value and a mirror value carrying the revealed trie
back: `rfl`, or folds of trie-preserving updates (`foldl_hom_*`), under constructor congruence. -/
syntax "lk_eq" : tactic
macro_rules | `(tactic| lk_eq) => `(tactic| first
  | rfl
  | (apply foldl_hom_wt <;> first | (intros; rfl) | lk_eq)
  | (apply foldl_hom_rs <;> first | (intros; rfl) | lk_eq)
  | (apply ovl_remove_congr; lk_eq)
  | (apply ovl_set_congr; lk_eq)
  | (apply ovl_setAK_congr; lk_eq)
  | (apply ovl_setAcct_congr; lk_eq)
  | (apply ovl_commit_congr; lk_eq)
  | (dsimp only; congr 1 <;> first
      | rfl
      | lk_eq
      | (congr 1 <;> first | rfl | lk_eq)))

open Lean Elab Tactic Meta in
/-- Generalize the (non-variable) discriminants of the first `match` of the goal over the whole goal,
so that splitting it splits the other side's `match` on the same discriminant too. -/
def lkGeneralizeFirstMatch (g : MVarId) : MetaM (MVarId × Array FVarId × Option Expr) := do
  let tgt ← instantiateMVars (← g.getType)
  let env ← getEnv
  let some e := tgt.find? (fun e => isMatcherAppCore env e) | return (g, #[], none)
  let some m ← matchMatcherApp? e | return (g, #[], none)
  let fvs := m.discrs.filterMap (fun d => if d.isFVar then some d.fvarId! else none)
  let ds := m.discrs.filter (fun d => !d.isFVar && !d.hasLooseBVars)
  if ds.isEmpty then return (g, fvs, some e)
  let args := ds.map fun d => ({ expr := d, xName? := some `d, hName? := none } : GeneralizeArg)
  try
    let (xs, g') ← g.generalize args
    -- the match, after generalization
    let tgt' ← instantiateMVars (← g'.getType)
    let e' := tgt'.find? (fun e => isMatcherAppCore env e)
    return (g', fvs ++ xs, e')
  catch _ => return (g, fvs, some e)

open Lean Elab Tactic Meta in
/-- Does the target still `match` on the free variable `x`? -/
def lkMatchesOn (g : MVarId) (x : FVarId) : MetaM Bool := do
  let tgt ← instantiateMVars (← g.getType)
  let env ← getEnv
  let ms := (tgt.foldlM (init := #[]) (fun acc e =>
    if isMatcherAppCore env e then some (acc.push e) else some acc)).getD #[]
  for e in ms do
    if let some m ← matchMatcherApp? e then
      if m.discrs.any (fun d => d.isFVar && d.fvarId! == x) then return true
  return false

open Lean Elab Tactic Meta in
/-- Close `g` if a hypothesis `∀ xs, a = b → False` applies (its equation closed by `rfl`). -/
def lkCloseByNegHyps (g : MVarId) : MetaM Bool := g.withContext do
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let ok ← forallTelescopeReducing t fun _ body => pure (body.isConstOf ``False)
    if !ok then continue
    let s ← saveState
    try
      let g' ← g.exfalso
      let gs ← g'.apply (mkFVar d.fvarId)
      for sg in gs do
        if !(← sg.isAssigned) then
          let ty ← instantiateMVars (← sg.getType)
          if ty.isEq then
            try sg.refl catch _ => sg.assumption
      let rest ← gs.filterM fun sg => do return !(← sg.isAssigned)
      if rest.isEmpty then return true
      restoreState s
    catch _ => restoreState s
  return false

open Lean Elab Tactic Meta in
/-- `split` the first `match`/`if` of the goal (its discriminants generalized first), then rewrite the
goal of every case with the case hypotheses the split introduced. -/
elab "lk_split" : tactic => do
  let g ← getMainGoal
  let (g, gfv, me) ← lkGeneralizeFirstMatch g
  replaceMainGoal [g]
  let before := (← g.getDecl).lctx
  try
    match me with
    | some e =>
      let gs ← g.withContext (Split.splitMatch g e)
      replaceMainGoal gs
    | none => evalTactic (← `(tactic| split))
  catch _ => throwError "lk_split: nothing to split"
  let gs ← getGoals
  let mut out : List MVarId := []
  for g0 in gs do
    let gs1 ← g0.withContext do
      let mut g := g0
      let lctx := (← g.getDecl).lctx
      for d in lctx do
        if d.isImplementationDetail || before.contains d.fvarId then continue
        let t ← instantiateMVars d.type
        let pf? : Option Expr ← do
          if t.isEq then pure (some (mkFVar d.fvarId))
          else if (← isProp t) then
            if t.isAppOfArity ``Not 1 then
              pure (some (← mkAppM ``eq_false #[mkFVar d.fvarId]))
            else pure (some (← mkAppM ``eq_true #[mkFVar d.fvarId]))
          else pure none
        if let some pf := pf? then
          try
            let r ← g.rewrite (← g.getType) pf
            g ← g.replaceTargetEq r.eNew r.eqProof
          catch _ => pure ()
      pure [g]
    -- a `match` on a generalized discriminant left (the other side took a catch-all
    -- alternative): split it too; the inconsistent combinations close by the case hypotheses
    let mut gs' : List MVarId := []
    for h in gs1 do
      let env ← getEnv
      let tgt ← instantiateMVars (← h.getType)
      let m? := tgt.find? (fun e => isMatcherAppCore env e &&
        (e.getAppArgs.any fun a => a.isFVar && gfv.contains a.fvarId!))
      match m? with
      | none => gs' := gs' ++ [h]
      | some e =>
        try
          let hs ← h.withContext (Split.splitMatch h e)
          gs' := gs' ++ hs
        catch _ => gs' := gs' ++ [h]
    for h in gs' do
      if (← h.isAssigned) then continue
      let closed ← try (h.withContext do
          if (← h.contradictionCore {}) then pure true else lkCloseByNegHyps h)
        catch _ => pure false
      if !closed then out := out ++ [h]
  setGoals out

open Lean Elab Tactic Meta in
/-- Join points: on `R (let j := vN; bN) (let j' := vO; bO) χ` with function-valued `j`, `j'` (the
`__do_jp` of `do`-notation), relate the two join points once — `∀ xs, R (j xs) (j' (WT.wt xs T)) χ` —
and continue on the bodies with that hypothesis, instead of inlining them into every branch. -/
elab "lk_jp" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← whnfR (← instantiateMVars (← g.getType))
    unless tgt.isAppOfArity ``R 7 do throwError "lk_jp: not R"
    let args := tgt.getAppArgs
    let s := args[2]!; let root := args[3]!; let n := args[4]!; let o := args[5]!; let χ := args[6]!
    let .letE nN tyN vN bN _ := n | throwError "lk_jp: mirror not a let"
    let .letE nO tyO vO bO _ := o | throwError "lk_jp: original not a let"
    unless tyN.isForall && tyO.isForall do throwError "lk_jp: not a join point"
    let T ← mkAppM ``preT #[s, root]
    -- HJ jN jO := ∀ xs, R s root (jN xs) (jO (WT.wt xs T)) χ
    let mkHJ (jN jO : Expr) : MetaM Expr :=
      forallTelescope tyN fun xs _ => do
        let xsO ← xs.mapM fun x => mkAppM ``WT.wt #[x, T]
        let body ← mkAppM ``R #[s, root, mkAppN jN xs, mkAppN jO xsO, χ]
        mkForallFVars xs body
    let hjv ← mkHJ vN vO
    let mH1 ← mkFreshExprSyntheticOpaqueMVar hjv
    let bodyTy ← withLocalDeclD nN tyN fun jN => withLocalDeclD nO tyO fun jO => do
      let hj ← mkHJ jN jO
      withLocalDeclD `hj hj fun h => do
        let r ← mkAppM ``R #[s, root, bN.instantiate1 jN, bO.instantiate1 jO, χ]
        mkForallFVars #[jN, jO, h] r
    let mBody ← mkFreshExprSyntheticOpaqueMVar bodyTy
    g.assign (mkApp3 mBody vN vO mH1)
    -- body: intro the join points and the hypothesis
    let (_, gB) ← mBody.mvarId!.introN 3 [nN, nO, `hj]
    replaceMainGoal [mH1.mvarId!, gB]

open Lean Elab Tactic Meta in
/-- Zeta-reduce top-level non-function `let`s of either side of an `R` goal. -/
elab "lk_zeta" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← whnfR (← instantiateMVars (← g.getType))
    unless tgt.isAppOfArity ``R 7 do throwError "lk_zeta: not R"
    let args := tgt.getAppArgs
    let red (e : Expr) : Bool × Expr :=
      match e with
      | .letE _ ty v b _ => if ty.isForall then (false, e) else (true, b.instantiate1 v)
      | _ => (false, e)
    let (c1, n) := red args[4]!
    let (c2, o) := red args[5]!
    unless c1 || c2 do throwError "lk_zeta: nothing"
    let tgt' := mkAppN tgt.getAppFn (args.set! 4 n |>.set! 5 o)
    replaceMainGoal [← g.replaceTargetDefEq tgt']

open Lean Elab Tactic Meta in
/-- Apply a local hypothesis concluding in `R` (join-point relations, induction hypotheses). -/
elab "lk_hyp" : tactic => do
  let g ← getMainGoal
  g.withContext do
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ok ← forallTelescopeReducing d.type fun _ b => pure (b.isAppOfArity ``R 7)
      if !ok then continue
      let s ← saveState
      try
        let gs ← g.apply (mkFVar d.fvarId)
        replaceMainGoal gs
        return
      catch _ => restoreState s
    throwError "lk_hyp: no hypothesis applies"

open Lean Elab Tactic Meta in
/-- `intro`, only on propositions (never on a pending data metavariable such as a bind's `φ`). -/
elab "lk_intro" : tactic => do
  let g ← getMainGoal
  let ty ← g.getType
  unless (← isProp ty) do throwError "lk_intro: not a proposition"
  evalTactic (← `(tactic| intro))

syntax "lk_call" : tactic
syntax "lk_ih" : tactic
set_option hygiene false in
macro_rules | `(tactic| lk_ih) => `(tactic| first | apply ih | apply hH)
macro_rules | `(tactic| lk_call) => `(tactic| first
  | apply R_get' | apply R_okL | apply R_throw | apply R_liftE | apply R_getAcct' | apply R_getAK'
  | apply R_getAKRaw' | apply R_getU64' | apply R_getIndices' | apply R_contains' | apply R_refLen'
  | apply R_iterKeys')

syntax "lk_step" : tactic
macro_rules | `(tactic| lk_step) => `(tactic| first
  | (apply R_ite _ _ rfl)
  | (apply R_pure; lk_eq)
  | (apply R_ok; lk_eq)
  | (apply R_throw)
  | (apply R_error)
  | (with_reducible lk_call)
  | lk_ih
  | lk_hyp
  | lk_jp
  | lk_zeta
  | (apply R_bind; with_reducible lk_call)
  | (apply R_bind; lk_ih)
  | (apply R_bind; lk_hyp)
  | (simp only [pure_bind])
  | (apply R_bind; apply R_pure rfl)
  | lk_eq
  | (dsimp (config := { zeta := false }) only [id, WT.wt, instWTProd, instWTOvl, instWTRS, instWTActSt, instWTDefault])
  | lk_split
  | (apply R_foldlM)
  | (apply R_mapM)
  | (apply R_bind; apply R_mapM)
  | (apply R_bind; apply R_foldlM_wt)
  | lk_intro)

macro "lk" : tactic => `(tactic| repeat (any_goals lk_step))

end NearSpecV3.Logged
