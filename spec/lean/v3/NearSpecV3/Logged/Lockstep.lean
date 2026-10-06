import Lean
import NearSpecV3.Logged.D2Queues

/-!
# Lockstep tactic for `R` (mirror vs original)

`lk` walks a mirror and its original together: `if`s with the same condition (`R_ite`), binds
whose heads are related by a known `R`-lemma (`lk_call`, extended with `macro_rules` as mirrors are
proved), `pure`/`throw` leaves, and `match`es (split once on the mirror side; the original's match
on the same discriminant is reduced with the case equation).
-/

namespace NearSpecV3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2

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
def lkGeneralizeFirstMatch (g : MVarId) : MetaM (MVarId × Array FVarId) := do
  let tgt ← instantiateMVars (← g.getType)
  let env ← getEnv
  let some e := tgt.find? (fun e => isMatcherAppCore env e) | return (g, #[])
  let some m ← matchMatcherApp? e | return (g, #[])
  let fvs := m.discrs.filterMap (fun d => if d.isFVar then some d.fvarId! else none)
  let ds := m.discrs.filter (fun d => !d.isFVar && !d.hasLooseBVars)
  if ds.isEmpty then return (g, fvs)
  let args := ds.map fun d => ({ expr := d, xName? := some `d, hName? := none } : GeneralizeArg)
  try
    let (xs, g') ← g.generalize args
    return (g', fvs ++ xs)
  catch _ => return (g, fvs)

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
  let (g, gfv) ← lkGeneralizeFirstMatch g
  replaceMainGoal [g]
  let before := (← g.getDecl).lctx
  try
    evalTactic (← `(tactic| split))
  catch _ =>
    -- fallback: case on the first closed `if` condition, reduce every `if` on it
    let tgt ← instantiateMVars (← g.getType)
    let some e := tgt.find? (fun e => e.isAppOfArity ``ite 5 && !(e.getArg! 1).hasLooseBVars)
      | throwError "lk_split: nothing to split"
    let c ← Term.exprToSyntax (e.getArg! 1)
    evalTactic (← `(tactic| by_cases hc : $c <;> simp only [hc, ite_true, ite_false, if_pos, if_neg,
      not_false_eq_true, true_and, and_true]))
    return
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
    -- a `match` on a generalized discriminant left (catch-all alternative): case on it
    let mut gs' : List MVarId := gs1
    for x in gfv do
      let mut next : List MVarId := []
      for h in gs' do
        if (← h.isAssigned) then continue
        let still ← try h.withContext (lkMatchesOn h x) catch _ => pure false
        if still then
          try
            let cs ← h.withContext (h.cases x)
            for c in cs do
              let c' ← try (c.mvarId.withContext do
                  let r ← c.mvarId.contradictionCore {}
                  if r then pure none
                  else if (← lkCloseByNegHyps c.mvarId) then pure none
                  else pure (some c.mvarId))
                catch _ => pure (some c.mvarId)
              if let some c' := c' then next := next ++ [c']
          catch _ => next := next ++ [h]
        else next := next ++ [h]
      gs' := next
    for h in gs' do
      if (← h.isAssigned) then continue
      let closed ← try (h.withContext do
          if (← h.contradictionCore {}) then pure true else lkCloseByNegHyps h)
        catch _ => pure false
      if !closed then out := out ++ [h]
  setGoals out

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
  | (apply R_bind; with_reducible lk_call)
  | (apply R_bind; lk_ih)
  | (apply R_bind; apply R_pure rfl)
  | lk_eq
  | (dsimp only [id])
  | lk_split
  | (apply R_foldlM)
  | (apply R_mapM)
  | (apply R_bind; apply R_mapM)
  | (apply R_bind; apply R_foldlM)
  | (intro))

macro "lk" : tactic => `(tactic| repeat' lk_step)

end NearSpecV3.Logged
