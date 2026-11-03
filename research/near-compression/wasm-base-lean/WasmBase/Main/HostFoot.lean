import Lean
import WasmBase.Main.StepRegs
import WasmBase.Main.RegMemLink
import WasmBase.Event

/-!
# WasmBase.Main.HostFoot — host-function footprint (E2E M6.1, first part)

A host function (`NearSpecV3/Wasm/Host.lean`, `hostCall name : Option (HM Unit)`,
`HM = EStateM String St`) is a monadic program over the whole `St`.  M6 splits `St` into the
**Wasm-visible part** (operand stack, frames, pages, globals, registers) and the **host-side part**
`σ` (every other field: `gas`, `ctx`, `ret`, `balance`, `storageUsage`, `regUsage`, `logs`, …).

## Invariants of a host program: `Inv I V m`

`Inv I V m`: from any state satisfying `I`, the program ends (normally or by an error) in a state
satisfying `I`, and a normal result satisfies `V`.  It composes over `bind` (`inv_bind`: the
continuation may assume `V` of the value), `get` yields a state satisfying `I` (`inv_get`), so a
later `set { s with … }` of a captured state is handled; `if`/`match` by `split`; `for` loops over
ranges/lists by `inv_forIn_list`/`inv_forIn_range`.  Relational facts ("field `f` is unchanged")
are invariants with a fixed reference `W0` (`I s := s.f = W0.f`).

## The primitives act on the two parts separately

The split: `vis s` (Wasm-visible part) and `hostSide s` (`σ`: the rest), lossless
(`st_eq_of_parts`).  The primitive effects:
* gas ops (`withGas`, hence `payBaseH`, `payPerH`, `payActionH`, `burnH`): only `gas` (`withGas_st`);
  `sync`: only `gas` (`sync_st`, `Main/HostArms.lean`);
* `readMemH`, `regGetH`, `memOrRegH`: only `gas` (they read pages / registers);
* `writeMemH`: `gas` and `pages`, the latter by `writeBytes`, which changes only `pages`
  (`writeBytes_split`: `wbPages`, a function of the pages alone; page count and sizes kept);
* `regSetH`: `gas`, `regUsage` and `registers := regSetRegs registers id d` (`regSetH_regs_eq`),
  which **keeps ids distinct** (`regSetRegs_nodup`);
* `popArgs`, `pushRet`: only `stack` (`StepRegs.popN_snd`, `pushRet_st`).
These are exactly the clauses of `Stab I` (a stable invariant survives any `σ`-only change, a pop,
an integer push, `writeBytes`, `regSetRegs`), and `inv_*` proves each primitive keeps every stable
invariant.

## The host invariant `HInv W0`

frames, globals, table, tableMax, elems, datas, stackRem equal `W0`'s; the page count is `W0`'s and pages stay well-sized;
register ids distinct; every operand-stack value an `i32`/`i64`.  `HInv` is preserved by every
primitive (`hinv_stab`), hence (tactic `inv_auto`) by whole arms of `hostCall`: see `HostArms.lean`.
-/

namespace WasmBase
namespace HostFoot
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-- The final state of a host-program result (normal or error). -/
def rst {α : Type} : EStateM.Result String St α → St
  | .ok _ s => s
  | .error _ s => s

/-- **`I` is invariant under `m`** (normal and error ends), and a normal result satisfies `V`. -/
def Inv (I : St → Prop) {α : Type} (V : α → Prop) (m : HM α) : Prop :=
  ∀ s, I s → match m s with
    | .ok a s' => V a ∧ I s'
    | .error _ s' => I s'

section
variable {I : St → Prop}

theorem inv_pure {α : Type} {V : α → Prop} {a : α} (h : V a) : Inv I V (pure a : HM α) :=
  fun _ hs => ⟨h, hs⟩

theorem inv_bind {α β : Type} {V : α → Prop} {W : β → Prop} {m : HM α} {k : α → HM β}
    (hm : Inv I V m) (hk : ∀ a, V a → Inv I W (k a)) : Inv I W (m >>= k) := by
  intro s hs
  have h := hm s hs
  simp only [bind, EStateM.bind]
  revert h
  cases m s with
  | ok a s1 => intro h; exact hk a h.1 s1 h.2
  | error e s1 => intro h; exact h

theorem inv_get : Inv I I (get : HM St) := fun _ hs => ⟨hs, hs⟩

theorem inv_map {α β : Type} {V : α → Prop} {f : α → β} {m : HM α} (h : Inv I V m) :
    Inv I (fun _ => True) (f <$> m) := by
  intro s hs
  have := h s hs
  simp only [Functor.map, EStateM.map]
  revert this
  cases m s with
  | ok a s1 => exact fun h => ⟨trivial, h.2⟩
  | error e s1 => exact id

theorem inv_set {s' : St} (h : I s') : Inv I (fun _ => True) (set s' : HM PUnit) := fun _ _ => ⟨trivial, h⟩

theorem inv_modify {f : St → St} (h : ∀ s, I s → I (f s)) : Inv I (fun _ => True) (modify f : HM PUnit) :=
  fun s hs => ⟨trivial, h s hs⟩

theorem inv_throw {α : Type} {V : α → Prop} {e : String} : Inv I V (throw e : HM α) := fun _ hs => hs

theorem inv_hErr {α : Type} {V : α → Prop} {e : String} : Inv I V (hErr e : HM α) := fun _ hs => hs

theorem inv_mono {α : Type} {V W : α → Prop} {m : HM α} (h : Inv I V m) (hw : ∀ a, V a → W a) :
    Inv I W m := by
  intro s hs
  have := h s hs
  revert this
  cases m s with
  | ok a s1 => exact fun h => ⟨hw a h.1, h.2⟩
  | error e s1 => exact id

theorem inv_true {α : Type} {V : α → Prop} {m : HM α} (h : Inv I V m) : Inv I (fun _ => True) m :=
  inv_mono h fun _ _ => trivial

theorem inv_ite {α : Type} {V : α → Prop} {c : Prop} [Decidable c] {a b : HM α}
    (ha : c → Inv I V a) (hb : ¬ c → Inv I V b) : Inv I V (if c then a else b) := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

theorem inv_dite {α : Type} {V : α → Prop} {c : Prop} [Decidable c] {a : c → HM α} {b : ¬ c → HM α}
    (ha : ∀ h, Inv I V (a h)) (hb : ∀ h, Inv I V (b h)) : Inv I V (if h : c then a h else b h) := by
  split
  · exact ha _
  · exact hb _

theorem inv_forIn_list {α β : Type} {V : β → Prop} (l : List α) (b : β) (f : α → β → HM (ForInStep β))
    (hb : V b) (hf : ∀ x c, V c → Inv I (fun r => V r.value) (f x c)) : Inv I V (forIn l b f) := by
  induction l generalizing b with
  | nil => exact inv_pure hb
  | cons x l ih =>
    rw [List.forIn_cons]
    refine inv_bind (hf x b hb) fun r hr => ?_
    cases r with
    | done c => exact inv_pure hr
    | yield c => exact ih c hr

theorem inv_forIn_range {β : Type} {V : β → Prop} (r : Std.Legacy.Range) (b : β) (f : Nat → β → HM (ForInStep β))
    (hb : V b) (hf : ∀ x c, V c → Inv I (fun r => V r.value) (f x c)) : Inv I V (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact inv_forIn_list _ b f hb hf

end


/-! ## The primitives' state effects -/

theorem rst_ok {α : Type} (a : α) (s : St) : rst (.ok a s : EStateM.Result String St α) = s := rfl
theorem rst_err {α : Type} (e : String) (s : St) : rst (.error e s : EStateM.Result String St α) = s := rfl

/-- `pushRet`: only the operand stack changes (an `i64`/`i32` push). -/
theorem pushRet_st (v : Nat) (is64 : Bool) (s : St) :
    rst (pushRet v is64 s) = if is64 then pushI64 s v else pushI32 s v := rfl

/-- Gas ops: only `gas` changes (to the op's new counter, on success and on failure). -/
theorem withGas_st (f : Gas → Gas × Option String) (s : St) :
    rst (withGas f s) = { s with gas := (f s.gas).1 } := by
  unfold withGas
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet]
  cases (f s.gas).2 <;> rfl


/-! ## The two parts of a state -/

/-- **The Wasm-visible part** of a state: operand stack, frames, pages, globals, registers, and the
static Wasm fields (table, its bound, element/data segments, the stack budget). -/
structure Vis where
  stack : Array Val
  frames : List Frame
  pages : Array ByteArray
  globals : Array Val
  registers : Array (Nat × ByteArray)
  table : Array (Option Nat)
  tableMax : Nat
  elems : Array (Array (Option Nat))
  datas : Array ByteArray
  stackRem : Nat

def vis (s : St) : Vis :=
  ⟨s.stack, s.frames, s.pages, s.globals, s.registers, s.table, s.tableMax, s.elems, s.datas, s.stackRem⟩

/-- **The host-side part `σ`**: the state with the Wasm-visible fields blanked. -/
def hostSide (s : St) : St :=
  { s with stack := #[], frames := [], pages := #[], globals := #[], registers := #[], table := #[],
           tableMax := 0, elems := #[], datas := #[], stackRem := 0 }

/-- The split is lossless: a state is determined by its two parts. -/
theorem st_eq_of_parts {s t : St} (hv : vis s = vis t) (hh : hostSide s = hostSide t) : s = t := by
  cases s; cases t
  simp only [vis, Vis.mk.injEq] at hv
  simp only [hostSide, St.mk.injEq] at hh
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hv
  obtain ⟨-, -, -, -, -, -, -, -, -, h11, h12, h13, h14, h15, -, h16, h17, h18, h19, h20, h21, h22, h23,
    h24, h25, h26⟩ := hh
  subst_vars; rfl

/-- The register file after `regSetH id d` (`Registers::set_impl`): replace the entry of `id`, or
push a new one. -/
def regSetRegs (regs : Array (Nat × ByteArray)) (id : Nat) (d : ByteArray) : Array (Nat × ByteArray) :=
  match regs.findIdx? (·.1 = id) with
  | some i => regs.set! i (id, d)
  | none => regs.push (id, d)

/-! ## Stable invariants

`Stab I`: `I` survives every primitive state change a host function makes: any change of the
host-side part alone (`side`), a pop (`popN`), an integer push, `writeBytes`, and a register write
(`regSetRegs`, with any new `regUsage`). -/
structure Stab (I : St → Prop) : Prop where
  side : ∀ {s s' : St}, I s → vis s' = vis s → I s'
  pop : ∀ {s : St}, I s → I (popN s).2
  push64 : ∀ {s : St} (v : Nat), I s → I (pushI64 s v)
  push32 : ∀ {s : St} (v : Nat), I s → I (pushI32 s v)
  wb : ∀ {s : St} (a : Nat) (d : ByteArray), I s → I (writeBytes s a d)
  regset : ∀ {s : St} (id : Nat) (d : ByteArray) (u : Nat), I s →
    I { s with registers := regSetRegs s.registers id d, regUsage := u }

/-- Close a goal `I s'` from some hypothesis `I s` of the context by one of `Stab`'s clauses. -/
syntax "close_stab " term : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| close_stab $hS) => withMainContext do
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      unless ← isProp d.type do continue
      let stx ← Term.exprToSyntax d.toExpr
      for t in [← `(tactic| exact $stx), ← `(tactic| exact ($hS).side $stx rfl), ← `(tactic| exact ($hS).pop $stx),
                ← `(tactic| exact ($hS).push64 _ $stx), ← `(tactic| exact ($hS).push32 _ $stx),
                ← `(tactic| exact ($hS).wb _ _ $stx), ← `(tactic| exact ($hS).regset _ _ _ $stx)] do
        let saved ← saveState
        try
          Term.withoutErrToSorry (evalTactic t)
          return
        catch _ => saved.restore
    throwError "close_stab: no hypothesis closes the goal"

/-- Known host-program lemmas (extended by `macro_rules` as helpers are proved). -/
syntax "inv_prim " term : tactic
macro_rules | `(tactic| inv_prim $_hS) => `(tactic| with_reducible exact inv_get)
macro_rules | `(tactic| inv_prim $_hS) => `(tactic| with_reducible exact inv_hErr)
macro_rules | `(tactic| inv_prim $_hS) => `(tactic| with_reducible exact inv_throw)

/-- **The host-program invariant tactic**: decompose `Inv I V prog` over `bind`, `if`, `match`,
`for`, and close the leaves by `inv_prim` lemmas, `pure`, and `close_stab` for `set`/`modify`.  The
program's head symbol selects the rule, and the decomposition lemma is applied by building its term
directly (no unification against the program, which could unfold the gas constants). -/
syntax "inv_auto " term : tactic

open Lean Meta Elab Tactic in
/-- One `inv_auto` step on goal `g`. -/
partial def invAutoGo (hS : Term) (g : MVarId) : TacticM Unit := g.withContext do
  let t := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let t := (← whnfR t).cleanupAnnotations
  let rec norm : Nat → Lean.Expr → Lean.Expr
    | 0, e => e
    | n + 1, e => match e.headBeta with
      | .letE _ _ v b _ => norm n (b.instantiate1 v)
      | .mdata _ e => norm n e
      | e => e
  let args := t.getAppArgs
  unless t.isAppOfArity ``Inv 4 do throwError "inv_auto: not an `Inv` goal{indentExpr t}"
  let I := args[0]!
  let W := args[2]!
  let m := norm 1000 args[3]!
  let g ← g.replaceTargetDefEq (mkAppN t.getAppFn #[I, args[1]!, W, m])
  let nm := m.getAppFn.constName?.getD .anonymous
  let isGet (e : Lean.Expr) : Bool :=
    let n := e.getAppFn.constName?.getD .anonymous
    n == ``MonadState.get || n == ``MonadStateOf.get || n == ``get || n == ``getThe
  let run (tac : TSyntax `tactic) : TacticM Unit := do
    setGoals [g]
    Term.withoutErrToSorry (evalTactic tac)
    unless (← getGoals).isEmpty do throwError "inv_auto: leaf not closed"
  if nm == ``Bind.bind && m.getAppNumArgs == 6 then
    let α := m.getArg! 2
    let β := m.getArg! 3
    let x := m.getArg! 4
    let f := m.getArg! 5
    let V ← if isGet x then pure I else
      withLocalDeclD `a α fun a => mkLambdaFVars #[a] (mkConst ``True)
    let hmT := mkAppN (mkConst ``Inv) #[I, α, V, x]
    let hm ← mkFreshExprSyntheticOpaqueMVar hmT
    let hkT ← withLocalDeclD `a α fun a => do
      let va := (mkApp V a).headBeta
      withLocalDeclD `ha va fun ha => do
        mkForallFVars #[a, ha] (mkAppN (mkConst ``Inv) #[I, β, W, (mkApp f a).headBeta])
    let hk ← mkFreshExprSyntheticOpaqueMVar hkT
    g.assign (mkAppN (mkConst ``inv_bind) #[I, α, β, V, W, x, f, hm, hk])
    invAutoGo hS hm.mvarId!
    let (_, hk') ← hk.mvarId!.introN 2
    invAutoGo hS hk'
  else if nm == ``ite && m.getAppNumArgs == 5 then
    let α := args[1]!
    let c := m.getArg! 1
    let inst := m.getArg! 2
    let a := m.getArg! 3
    let b := m.getArg! 4
    let haT ← withLocalDeclD `h c fun h => mkForallFVars #[h] (mkAppN (mkConst ``Inv) #[I, α, W, a])
    let hbT ← withLocalDeclD `h (mkNot c) fun h => mkForallFVars #[h] (mkAppN (mkConst ``Inv) #[I, α, W, b])
    let ha ← mkFreshExprSyntheticOpaqueMVar haT
    let hb ← mkFreshExprSyntheticOpaqueMVar hbT
    g.assign (mkAppN (mkConst ``inv_ite) #[I, α, W, c, inst, a, b, ha, hb])
    let (_, ga) ← ha.mvarId!.intro1
    invAutoGo hS ga
    let (_, gb) ← hb.mvarId!.intro1
    invAutoGo hS gb
  else if nm == ``dite && m.getAppNumArgs == 5 then
    let α := args[1]!
    let c := m.getArg! 1
    let inst := m.getArg! 2
    let a := m.getArg! 3
    let b := m.getArg! 4
    let haT ← withLocalDeclD `h c fun h => mkForallFVars #[h] (mkAppN (mkConst ``Inv) #[I, α, W, (mkApp a h).headBeta])
    let hbT ← withLocalDeclD `h (mkNot c) fun h => mkForallFVars #[h] (mkAppN (mkConst ``Inv) #[I, α, W, (mkApp b h).headBeta])
    let ha ← mkFreshExprSyntheticOpaqueMVar haT
    let hb ← mkFreshExprSyntheticOpaqueMVar hbT
    g.assign (mkAppN (mkConst ``inv_dite) #[I, α, W, c, inst, a, b, ha, hb])
    let (_, ga) ← ha.mvarId!.intro1
    invAutoGo hS ga
    let (_, gb) ← hb.mvarId!.intro1
    invAutoGo hS gb
  else if nm == ``Pure.pure && m.getAppNumArgs == 4 then
    let wa ← whnfR (mkApp W (m.getArg! 3)).headBeta
    if wa.isConstOf ``True then
      g.assign (mkAppN (mkConst ``inv_pure) #[I, args[1]!, W, m.getArg! 3, mkConst ``True.intro])
    else
      run (← `(tactic| first | exact inv_pure trivial | exact inv_pure (by assumption)))
  else if nm == ``MonadStateOf.set || nm == ``MonadState.set || nm == ``set then
    run (← `(tactic| (refine inv_set ?_; close_stab $hS)))
  else if nm == ``modify || nm == ``MonadState.modifyGet || nm == ``modifyGet then
    run (← `(tactic| (refine inv_modify fun _ _ => ?_; first | close_stab $hS | (split <;> close_stab $hS))))
  else if nm == ``ForIn.forIn && m.getAppNumArgs ≥ 3 then
    let n := m.getAppNumArgs
    let x := m.getArg! (n - 3)
    let b := m.getArg! (n - 2)
    let f := m.getArg! (n - 1)
    let ρ ← whnfR (← inferType x)
    let β ← inferType b
    let V ← withLocalDeclD `a β fun a => mkLambdaFVars #[a] (mkConst ``True)
    let isRange := ρ.isConstOf ``Std.Legacy.Range
    let α := (← whnfR (← inferType f)).bindingDomain!
    let stepT := mkApp (mkConst ``ForInStep [0]) β
    let hfT ← withLocalDeclD `x α fun xv => withLocalDeclD `c β fun cv =>
      withLocalDeclD `hc (mkConst ``True) fun hc => do
        let Vr ← withLocalDeclD `r stepT fun r => mkLambdaFVars #[r] (mkConst ``True)
        mkForallFVars #[xv, cv, hc] (mkAppN (mkConst ``Inv) #[I, stepT, Vr, mkAppN f #[xv, cv]])
    let hf ← mkFreshExprSyntheticOpaqueMVar hfT
    let pf := if isRange then
        mkAppN (mkConst ``inv_forIn_range) #[I, β, V, x, b, f, mkConst ``True.intro, hf]
      else
        mkAppN (mkConst ``inv_forIn_list) #[I, α, β, V, x, b, f, mkConst ``True.intro, hf]
    g.assign pf
    let (_, g') ← hf.mvarId!.introN 3
    invAutoGo hS g'
  else if nm == ``Functor.map then
    run (← `(tactic| (refine inv_map ?_; inv_auto $hS)))
  else if (← isMatcher nm) then
    setGoals [g]
    evalTactic (← `(tactic| split))
    for g' in ← getGoals do
      invAutoGo hS g'
  else
    let saved ← saveState
    try
      run (← `(tactic| inv_prim $hS))
    catch ex =>
      saved.restore
      -- an unknown helper: unfold its definition and continue
      match ← unfoldDefinition? m with
      | some m' =>
        let g' ← g.replaceTargetDefEq (mkAppN t.getAppFn #[I, args[1]!, W, m'])
        invAutoGo hS g'
      | none => throw ex

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| inv_auto $hS) => do
    let g ← getMainGoal
    invAutoGo hS g
    setGoals []


section
variable {I : St → Prop} (hS : Stab I)
include hS

theorem inv_withGas (f : Gas → Gas × Option String) : Inv I (fun _ => True) (withGas f) := by
  unfold withGas; inv_auto hS

end

macro_rules | `(tactic| inv_prim $hS) => `(tactic| with_reducible exact inv_withGas $hS _)

section
variable {I : St → Prop} (hS : Stab I)
include hS

theorem inv_payBaseH (c : Cost) : Inv I (fun _ => True) (payBaseH c) := inv_withGas hS _
theorem inv_payPerH (c : Cost) (n : Nat) : Inv I (fun _ => True) (payPerH c n) := inv_withGas hS _
theorem inv_payActionH (b bc u : Nat) : Inv I (fun _ => True) (payActionH b bc u) := inv_withGas hS _
theorem inv_burnH (x : Nat) : Inv I (fun _ => True) (burnH x) := inv_withGas hS _

end

macro_rules | `(tactic| inv_prim $hS) => `(tactic| with_reducible exact inv_payBaseH $hS _)
macro_rules | `(tactic| inv_prim $hS) => `(tactic| with_reducible exact inv_payPerH $hS _ _)
macro_rules | `(tactic| inv_prim $hS) => `(tactic| with_reducible exact inv_payActionH $hS _ _ _)
macro_rules | `(tactic| inv_prim $hS) => `(tactic| with_reducible exact inv_burnH $hS _)

section
variable {I : St → Prop} (hS : Stab I)
include hS

theorem inv_readMemH (ptr len : Nat) : Inv I (fun _ => True) (readMemH ptr len) := by
  unfold readMemH; inv_auto hS

theorem inv_writeMemH (ptr : Nat) (d : ByteArray) : Inv I (fun _ => True) (writeMemH ptr d) := by
  unfold writeMemH; inv_auto hS

theorem inv_regGetH (id : Nat) : Inv I (fun _ => True) (regGetH id) := by
  unfold regGetH; inv_auto hS

theorem inv_pushRet (v : Nat) (is64 : Bool) : Inv I (fun _ => True) (pushRet v is64) := by
  unfold pushRet; inv_auto hS

theorem inv_regSetH (id : Nat) (d : ByteArray) (cb : Bool) : Inv I (fun _ => True) (regSetH id d cb) := by
  unfold regSetH; inv_auto hS

theorem inv_memOrRegH (ptr len : Nat) : Inv I (fun _ => True) (memOrRegH ptr len) := by
  unfold memOrRegH; inv_auto hS

theorem inv_popArgs (n : Nat) : Inv I (fun _ => True) (popArgs n) := by
  unfold popArgs
  refine inv_bind (V := fun _ => True) ?_ (fun _ _ => ?_)
  · refine inv_forIn_range (V := fun _ => True) _ _ _ trivial (fun _ _ _ => ?_)
    refine inv_bind inv_get (fun x hx => ?_)
    have hp := hS.pop hx
    revert hp
    cases popN x
    intro hp
    dsimp only
    refine inv_bind (V := fun _ => True) (inv_set ?_) (fun _ _ => ?_)
    · exact hp
    · inv_auto hS
  · inv_auto hS

end

macro_rules | `(tactic| inv_prim $hS) => `(tactic| with_reducible exact inv_readMemH $hS _ _)
macro_rules | `(tactic| inv_prim $hS) => `(tactic| with_reducible exact inv_writeMemH $hS _ _)
macro_rules | `(tactic| inv_prim $hS) => `(tactic| with_reducible exact inv_regGetH $hS _)
macro_rules | `(tactic| inv_prim $hS) => `(tactic| with_reducible exact inv_pushRet $hS _ _)
macro_rules | `(tactic| inv_prim $hS) => `(tactic| with_reducible exact inv_regSetH $hS _ _ _)
macro_rules | `(tactic| inv_prim $hS) => `(tactic| with_reducible exact inv_memOrRegH $hS _ _)
macro_rules | `(tactic| inv_prim $hS) => `(tactic| with_reducible exact inv_popArgs $hS _)

/-! ## The register file: `regSetRegs` keeps ids distinct -/

/-- The register ids are distinct. -/
def RegIds (regs : Array (Nat × ByteArray)) : Prop := (regs.toList.map Prod.fst).Nodup

theorem regSetRegs_nodup {regs : Array (Nat × ByteArray)} (h : RegIds regs) (id : Nat) (d : ByteArray) :
    RegIds (regSetRegs regs id d) := by
  unfold regSetRegs RegIds at *
  split
  · rename_i i hi
    obtain ⟨hlt, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
    simp only [decide_eq_true_eq] at hp
    rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds, List.map_set]
    have e : (regs.toList.map Prod.fst).set i id = regs.toList.map Prod.fst := by
      apply List.ext_getElem (by simp)
      intro j h1 h2
      rw [List.getElem_set]
      split
      · simp_all
      · rfl
    simpa [e] using h
  · rename_i hn
    rw [Array.findIdx?_eq_none_iff] at hn
    rw [Array.toList_push, List.map_append, List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    intro a ha b hb
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    have := hn x (by simpa using hx)
    simp only [decide_eq_false_iff_not] at this
    rw [hb]; exact this

/-- `regSetH`'s new register file is `regSetRegs`. -/
theorem regSetH_regs_eq (regs : Array (Nat × ByteArray)) (id : Nat) (d : ByteArray) :
    (match regs.findIdx? (·.1 = id) with
      | some i => regs.set! i (id, d)
      | none => regs.push (id, d)) = regSetRegs regs id d := rfl

/-! ## `writeBytes` acts on the pages only -/

/-- The pages after `writeBytes`: a function of the pages alone. -/
def wbPages (pg : Array ByteArray) (a : Nat) (d : ByteArray) : Array ByteArray :=
  (List.range' 0 d.size).foldl
    (fun pg i => pg.modify ((a + i) / pageSize) (fun p => p.set! ((a + i) % pageSize) d[i]!)) pg

theorem foldl_writeByte (a : Nat) (d : ByteArray) :
    ∀ (l : List Nat) (s : St), l.foldl (fun s i => writeByte s (a + i) d[i]!) s =
      { s with pages := (l.foldl
          (fun pg i => pg.modify ((a + i) / pageSize) (fun p => p.set! ((a + i) % pageSize) d[i]!)) s.pages) }
  | [], _ => rfl
  | i :: l, s => by
    simp only [List.foldl_cons]
    rw [foldl_writeByte a d l]
    rfl

/-- **`writeBytes` changes only `pages`** (by `wbPages`). -/
theorem writeBytes_split (s : St) (a : Nat) (d : ByteArray) :
    writeBytes s a d = { s with pages := wbPages s.pages a d } := by
  rw [writeBytes_eq, foldl_writeByte]; rfl

theorem wbPages_size (pg : Array ByteArray) (a : Nat) (d : ByteArray) : (wbPages pg a d).size = pg.size := by
  unfold wbPages
  generalize List.range' 0 d.size = l
  induction l generalizing pg with
  | nil => rfl
  | cons i l ih => simp only [List.foldl_cons]; rw [ih]; simp

theorem writeBytes_pagesOK {s : St} (hP : PagesOK s) (a : Nat) (d : ByteArray) : PagesOK (writeBytes s a d) := by
  rw [writeBytes_eq]
  generalize List.range' 0 d.size = l
  induction l generalizing s with
  | nil => exact hP
  | cons i l ih => simp only [List.foldl_cons]; exact ih (writeByte_ok hP _ _)

/-! ## The host invariant `HInv` -/

/-- An operand-stack value a host function may leave: an integer. -/
def IsInt : Val → Prop
  | .i32 _ => True
  | .i64 _ => True
  | _ => False

/-- **The host invariant relative to a reference state `W0`**: the frame stack, globals, table,
element/data segments and stack budget are `W0`'s; the page count is `W0`'s and pages stay
well-sized; register ids are distinct; every operand-stack value is an integer. -/
structure HInv (W0 s : St) : Prop where
  frames : s.frames = W0.frames
  globals : s.globals = W0.globals
  table : s.table = W0.table
  tableMax : s.tableMax = W0.tableMax
  elems : s.elems = W0.elems
  datas : s.datas = W0.datas
  stackRem : s.stackRem = W0.stackRem
  npages : s.pages.size = W0.pages.size
  pok : PagesOK W0 → PagesOK s
  regs : RegIds s.registers
  stk : ∀ v ∈ s.stack.toList, IsInt v

theorem hinv_stab (W0 : St) : Stab (HInv W0) where
  side := by
    intro s s' h hv
    simp only [vis, Vis.mk.injEq] at hv
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hv
    exact ⟨h2 ▸ h.frames, h4 ▸ h.globals, h6 ▸ h.table, h7 ▸ h.tableMax, h8 ▸ h.elems, h9 ▸ h.datas,
      h10 ▸ h.stackRem, h3 ▸ h.npages, fun hp => by unfold PagesOK; rw [h3]; exact h.pok hp,
      h5 ▸ h.regs, h1 ▸ h.stk⟩
  pop := by
    intro s h
    rw [StepRegs.popN_snd]
    exact ⟨h.frames, h.globals, h.table, h.tableMax, h.elems, h.datas, h.stackRem, h.npages, h.pok, h.regs,
      fun v hv => h.stk v (by simp only [popV, Array.toList_pop] at hv; exact (List.dropLast_sublist _).subset hv)⟩
  push64 := by
    intro s v h
    refine ⟨h.frames, h.globals, h.table, h.tableMax, h.elems, h.datas, h.stackRem, h.npages, h.pok, h.regs,
      fun x hx => ?_⟩
    simp only [pushI64, pushV, Array.toList_push, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h.stk x hx
    · trivial
  push32 := by
    intro s v h
    refine ⟨h.frames, h.globals, h.table, h.tableMax, h.elems, h.datas, h.stackRem, h.npages, h.pok, h.regs,
      fun x hx => ?_⟩
    simp only [pushI32, pushV, Array.toList_push, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h.stk x hx
    · trivial
  wb := by
    intro s a d h
    have hp := writeBytes_pagesOK (s := s) (a := a) (d := d)
    rw [writeBytes_split] at hp ⊢
    exact ⟨h.frames, h.globals, h.table, h.tableMax, h.elems, h.datas, h.stackRem,
      by rw [wbPages_size]; exact h.npages, fun h0 => hp (h.pok h0), h.regs, h.stk⟩
  regset := by
    intro s id d u h
    exact ⟨h.frames, h.globals, h.table, h.tableMax, h.elems, h.datas, h.stackRem, h.npages, h.pok,
      regSetRegs_nodup h.regs id d, h.stk⟩

end HostFoot
end WasmBase
