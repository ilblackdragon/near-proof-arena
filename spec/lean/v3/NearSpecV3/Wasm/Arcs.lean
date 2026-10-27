import NearSpecV3.Wasm.Fuel
import NearSpecV3.Wasm.Segment

/-!
# Arcs: bulk execution of zero-fee control runs (W02 evaluation time)

> **Status: in-progress formalization — not imported by `NearSpecV3` and not reachable from
> any checker.** The performance mechanism is validated (prototype: `research/lean-arcs/`,
> 1,474× on `blocks4999`, 9,375/9,375 A/B parity). **Proved with no `sorry`**: the one-step
> correspondence `step_sim` (all four `exec` arms, including the guard case that excludes
> `exec .end_`'s singleton return arm), the walk facts (`simStep_pc`, `simNext_inv`,
> `runSteps_peel`, `runFrom_steps`, `runFrom_end`, `walk_pc_chain`, the guard
> monotonicity chain), the run correspondence `step_walk`, `arc_seg` (a valid arc's whole
> run single-stepped is one jump), `runFast_eq_run` (strong induction over the fuel; the
> fire path substitutes `arc_seg` + `run_seg`), and the entry equality
> `callEntryFast_eq_callEntry` (via `callEntryWith` parameterization + `funext`).
> **Two named obligations remain** (below), both stated as theorems with explicit `sorry`:
> `arcsFor_valid` (the builder's rows satisfy `ArcsOK`) and `runCallFast_eq_runCall` (the
> control-flow congruence over the shared spine). Until they are discharged and the module
> is imported, nothing here affects any verdict.

`wasmFuel` (`Wasm/Fuel.lean`) made the step budget non-binding for valid runs and moved the
binding limit to *evaluation time*: a loop of `k` zero-fee `block`s and one `br` executes
`2k + 2` interpreter steps per `2 · regular_op_cost` of gas, so the worst contract at PV86
(`k = 4,999`) spends ~5.7·10⁹ steps per Tgas — ~55 h for a 300 Tgas receipt at the measured
8–9 M steps/s. The evidence README proposes skipping zero-fee control instructions in bulk
(`docs/evidence/lean-chunk-completion/fuel-termination/README.md` §4).

This module does that **without changing a single step of the semantics**. The observations:

* `block`, `loop`, `end` and `nop` are the only instructions that are free (gas-table entry
  `none`) and cannot touch the value stack, locals, globals, memory, gas or host state.
  (`else` reads and pops the label list; everything else either carries a fee or reads the
  value stack, so a run stops at it.)
* Inside such a run the machine state changes only in the top frame's `pc` and `labels`, and
  the only label field a run can set is `height`, which is the entry value-stack height.
* If the run never pops an *entry* label (every `end` pops a label the run pushed), its net
  effect is one jump: `pc := runEnd`, `labels := pushes ++ entry`.

So one **arc** — a jump over the run — replaces `len = runEnd − pc0` single steps and consumes
the same `len` fuel. `runFast` is *proved equal to `run` for every fuel* (`runFast_eq_run`),
so the fuel theorems of `Wasm/Fuel.lean` transfer verbatim to the fast layer
(`runFast_fuel_le`, `runCallFast_eq_runCall`, `runCallWithLimitsFast_eq_runCallWithLimits`,
`successorFuel_moves_only_exhausted_fast`): the W02 statement keeps its exact meaning.

Everything is additive: `Exec.step`, `Exec.run`, `Exec.runCall`, `Prepare` and `FiniteWasm`
are untouched, the signed `D3` path never sees an arc, and the successor switches wholesale
(`Successor/StorageExecution.lean` calls `runCallWithLimitsFast`).

## Why the runs are "determined", and the one runtime condition

`simStep` below is the *conservative abstract simulator* of one free instruction: it returns
`none` unless executing that instruction is definitionally a `.cont` whose label effect the
simulator reproduces exactly. It returns `none` for every non-run instruction, for an `end`
that would pop an entry label (empty simulator stack), and for a `block` whose `endOf` entry
is missing. A run the simulator walks through therefore consists solely of steps that
`Exec.step` turns into `.cont` (given the entry label list is nonempty, so that `exec .end_`'s
terminal `[_]` singleton arm cannot fire: at an in-run `end` the list is `runLabels ++ entry`
with `entry` nonempty, hence of length ≥ 2). The runtime fire condition is exactly that
nonempty check — an O(1) match; the structurally-degenerate empty case single-steps.

## The proof architecture

* `simWalk pf pc0 k` iterates `simNext` (which applies `simStep`) `k` times from `(pc0, [])`.
* `ArcOK pf a`: the walk from `pc0` advances through all `len` instructions of `[pc0, runEnd)`
  and lands exactly on `(runEnd, pushes)`.
* `step_walk`: the `k`-th single step of a valid arc's run is `.cont` of the `(k+1)`-th walk
  state (the four `exec` arms, by the observations above).
* `arc_seg`: chaining `step_walk`: `seg len s = .cont (applyArc s f a)`.
* `runFast_eq_run`: `runFast` mirrors `run`'s fuel recursion; an arc fire substitutes
  `arc_seg` + `run_seg` (`Wasm/Segment.lean`), every other path single-steps identically.
* `arcsFor_valid`: the builder (a scan whose in-run transition *is* `simNext`) emits only
  `ArcOK` arcs, at their start pc.

## Measurement discipline

`IO.monoMsNow` timing inside one `IO` block floats pure `let`s between the clock reads, so a
naive A/B harness reports 0 ms for work it actually did. Force each phase with its own `IO`
statement before reading the closing clock. `research/lean-arcs/` documents the artifact and
the honest numbers (blocks4999 at 300 Tgas: ~13–55 h → ~27 s with the fused-br prototype; the
committed module keeps the same mechanism with a simpler, theorem-friendly run shape).

## Open proofs (the remaining `sorry`s)

* `arcsFor_valid` — the builder's rows satisfy `ArcsOK`. The proof skeleton: an induction
  over `buildFrom`'s `left` (the array slot equation `Array.getElem?_setIfInBounds` for
  the emitted write, `Array.getElem?_replicate` for the base table), with each emitted
  arc's walk facts from `runFrom_steps` (every prefix advances) and `runFrom_end` (the
  landing pc = pc0 + len, hence `runEnd`), plus the `runSteps` landing's sim/grd.
* `runCallFast_eq_runCall` — the control-flow congruence: both sides share the identical
  prepare/link/resolve/instantiate spine; the two entry calls differ and agree by
  `callEntryFast_eq_callEntry` (the table validity comes from `arcsFor_valid`).
* After those: `runCallWithLimitsFast` (a wrapper like `runCallWithLimits`, with the
  loading-limits preflight — definitional once `runCallFast_eq_runCall` holds), the
  fuel-transfer theorems (`runCallFast_fuel_le` etc., the same proofs as `Fuel.lean`'s
  with the fast layer), and the successor wiring.
-/

namespace NearSpecV3.Wasm

/-! ## The conservative simulator

The walk state is `(pc, sim, grd)`: the current pc, the labels the run has pushed and not
popped (top-first), and the **guard demand**: `grd` accumulates, over the run's `end`
instructions, the minimum entry-label depth the run needs. At an in-run `end` the label list
is `matLabels H sim ++ en`; `exec .end_` takes the pop arm iff its length is at least 2, i.e.
`|sim| + |en| ≥ 2`. So an `end` at simulator depth `|sim|` demands `|en| ≥ 2 − |sim|`
(`0` when `|sim| ≥ 2`). The arc's `guard` is the maximum demand; the runtime fire condition
`labels.length ≥ guard` (at the fire point `sim = []`, so `labels = en`) discharges every
demand. Without it, a run could reach an `end` with a singleton label list at function top
level and *return* instead of advancing — the guard is what makes the run's effect a pure
jump. -/

/-- The abstract label bookkeeping of a run: `(target, arity, isLoop)`. -/
abbrev SimLab := Nat × Nat × Bool

/-- One simulated free instruction on `(pc, sim)`, returning `(pc', sim')` or `none` when the
instruction is not *run-determined* (not a run instruction; an `end` that would pop an entry
label — empty `sim`; a `block` whose `endOf` entry is missing). -/
def simStep (pf : PFunc) (pc : Nat) (sim : List SimLab) (i : Instr) : Option (Nat × List SimLab) :=
  match i with
  | .block bt =>
    match pf.endOf[pc]? with
    | some e => some (pc + 1, (e + 1, (btResults bt).size, false) :: sim)
    | none => none
  | .loop _ => some (pc + 1, (pc + 1, 0, true) :: sim)
  | .nop => some (pc + 1, sim)
  | .end_ =>
    match sim with
    | _ :: t => some (pc + 1, t)
    | [] => none
  | _ => none

/-- The guard demand one `end` at simulator depth `|sim|` adds: the entry labels must supply
the rest of the length-2 requirement. -/
def endDemand (sim : List SimLab) : Nat := 2 - sim.length

/-- One walk transition on `(pc, sim, grd)`: advance on a run-determined free instruction
(accumulating `endDemand sim` on every advance — a conservative over-approximation that only
matters at `end`s, where `endDemand sim = 2 - |sim|` is exactly the entry depth the `end`
needs), stay otherwise. -/
def simNext (pf : PFunc) (st : Nat × List SimLab × Nat) : Nat × List SimLab × Nat :=
  match st with
  | (pc, sim, grd) =>
    if h : pc < pf.code.size then
      match pf.code[pc], pf.gas[pc]? with
      | i, some none =>
        match simStep pf pc sim i with
        | some (pc', sim') => (pc', sim', Nat.max grd (endDemand sim))
        | none => (pc, sim, grd)
      | _, _ => (pc, sim, grd)
    else (pc, sim, grd)

/-- The walk from `pc0`: `simWalk pf pc0 k` applies `simNext` `k` times to `(pc0, [], 0)`. -/
def simWalk (pf : PFunc) (pc0 : Nat) : Nat → Nat × List SimLab × Nat
  | 0 => (pc0, [], 0)
  | k + 1 => simNext pf (simWalk pf pc0 k)

/-! ## Arcs -/

/-- A precomputed shortcut over a run of free `block`/`loop`/`end`/`nop` instructions. -/
structure Arc where
  /-- the run's start pc; the arc is stored at this index of the per-function table -/
  pc0 : Nat
  /-- the first pc after the run (the arc's landing pc) -/
  runEnd : Nat
  /-- the labels the run pushes, top-first: `(target, arity, isLoop)`; `height` is the entry
  value-stack size at fire time -/
  pushes : List SimLab
  /-- minimum entry-label depth the run needs (see the simulator doc): the fire condition
  `labels.length ≥ guard` makes every in-run `end` take `exec`'s pop arm -/
  guard : Nat
  deriving Inhabited, Repr

/-- Materialize the run's pushed labels with the given value-stack height. -/
def matLabels (H : Nat) : List SimLab → List Label
  | [] => []
  | (t, ar, lp) :: rest => { target := t, arity := ar, height := H, isLoop := lp } :: matLabels H rest

/-- The net effect of executing the whole run from state `s`: the top frame's `pc` moves to
`runEnd` and its labels become `matLabels H pushes ++ entry`; the rest of `s` is unchanged. -/
def applyArc (s : St) (f : Frame) (a : Arc) : St :=
  setFrame s { f with pc := a.runEnd, labels := matLabels s.stack.size a.pushes ++ f.labels }

/-- Fuel an arc consumes: its run's single steps. -/
def Arc.len (a : Arc) : Nat := a.runEnd - a.pc0

/-! ### Validity (the builder's contract) -/

/-- `a` describes a real run of `pf`:
* the walk from `(pc0, [], 0)` over `len = runEnd − pc0` transitions lands exactly on
  `(runEnd, pushes, guard)`;
* **every prefix advances**: for each `k < len`, the transition at walk position `k` moves
  the pc by exactly one (the only advancing moves `simNext` makes are `simStep`'s `pc + 1`).
  The builder guarantees this directly (it emits an arc only while `simNext` advances), and
  `step_walk` needs it to apply `step_sim` at every position of the run. -/
def ArcOK (pf : PFunc) (a : Arc) : Prop :=
  a.pc0 < a.runEnd ∧ a.runEnd ≤ pf.code.size ∧
    simWalk pf a.pc0 (a.runEnd - a.pc0) = (a.runEnd, a.pushes, a.guard) ∧
    ∀ (k : Nat) (hk : k < a.runEnd - a.pc0),
      (simWalk pf a.pc0 k).1 + 1 = (simWalk pf a.pc0 (k + 1)).1

/-- The per-function table is valid for `pf`: every stored arc is `ArcOK` and sits at its
start pc. -/
def ArcsOK (pf : PFunc) (row : Array (Option Arc)) : Prop :=
  ∀ (pc : Nat) (a : Arc), row[pc]? = some a → a.pc0 = pc ∧ ArcOK pf a

/-- The whole table matches the prepared module: row `fn` is valid for `p.funcs[fn]`. -/
def arcsValidFor (p : Prepared) (arcs : Array (Array (Option Arc))) : Prop :=
  ∀ (fn : Nat) (row : Array (Option Arc)), arcs[fn]? = some row →
    ∃ pf, p.funcs[fn]? = some pf ∧ ArcsOK pf row

/-! ### The builder

`runSteps pf pc k st` applies `simNext` `k` times from an explicit start state. Because
`simNext` stalls exactly at non-advancing positions (a stall is a fixed point), the maximal
run from `pc` is found by stepping while the pc advances; `runFrom` counts the steps, so the
arc's length is *by construction* the number of advancing transitions — the property
`ArcOK`'s advance clause states. The scan continues at the run's end, so runs are maximal
and disjoint; runs of length < 2 are not worth an entry. -/

/-- Apply `simNext` `k` times from `st` (last transition applied last, matching `simWalk`'s
fold order: `runSteps (k+1) st = simNext (runSteps k st)`). -/
def runSteps (pf : PFunc) : Nat → Nat × List SimLab × Nat → Nat × List SimLab × Nat
  | 0, st => st
  | k + 1, st => simNext pf (runSteps pf k st)

/-- Peeling one transition off the end of a `runSteps` chain. -/
theorem runSteps_peel (pf : PFunc) (n : Nat) (st : Nat × List SimLab × Nat) :
    runSteps pf (n + 1) st = runSteps pf n (simNext pf st) := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih =>
    -- both sides unfold one step; then commute simNext through by the ih at simNext st
    show simNext pf (runSteps pf (n + 1) st) = simNext pf (runSteps pf n (simNext pf st))
    rw [ih st]

/-- The walk from `pc0` in terms of `runSteps` (definitional unfolding chain). -/
theorem simWalk_eq_runSteps (pf : PFunc) (pc0 : Nat) (k : Nat) :
    simWalk pf pc0 k = runSteps pf k (pc0, [], 0) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [simWalk, ih]; rfl

/-- The maximal advancing run from `(pc, sim, grd)`: the number of steps after which the
pc stops advancing. -/
def runFrom (pf : PFunc) : Nat → Nat × List SimLab × Nat → Nat
  | 0, _ => 0
  | fuel + 1, st =>
    if (simNext pf st).1 = st.1 then 0 else runFrom pf fuel (simNext pf st) + 1

/-- `runFrom` bounds its result by the fuel. -/
private theorem runFrom_le (pf : PFunc) (fuel : Nat) (st : Nat × List SimLab × Nat) :
    runFrom pf fuel st ≤ fuel := by
  induction fuel generalizing st with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    unfold runFrom
    split
    · omega
    · rename_i hne
      show runFrom pf fuel (simNext pf st) + 1 ≤ fuel + 1
      exact Nat.succ_le_succ (ih (simNext pf st))

/-- `simStep`'s advancing results always move to `pc + 1`. -/
private theorem simStep_pc (pf : PFunc) (pc : Nat) (sim : List SimLab) (i : Instr)
    (pc' : Nat) (sim' : List SimLab) (h : simStep pf pc sim i = some (pc', sim')) :
    pc' = pc + 1 := by
  cases i with
  | block bt =>
    simp only [simStep] at h
    cases he : pf.endOf[pc]? with
    | none => rw [he] at h; simp at h
    | some e =>
      rw [he] at h
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      exact h.1.symm
  | loop _ =>
    simp only [simStep, Prod.mk.injEq, Option.some.injEq] at h
    exact h.1.symm
  | nop =>
    simp only [simStep, Prod.mk.injEq, Option.some.injEq] at h
    exact h.1.symm
  | end_ =>
    simp only [simStep] at h
    cases hsim : sim with
    | nil => rw [hsim] at h; simp at h
    | cons lab t =>
      rw [hsim] at h
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      exact h.1.symm
  | unreachable => simp [simStep] at h
  | if_ _ => simp [simStep] at h
  | else_ => simp [simStep] at h
  | br _ => simp [simStep] at h
  | brIf _ => simp [simStep] at h
  | brTable _ _ => simp [simStep] at h
  | ret => simp [simStep] at h
  | call _ => simp [simStep] at h
  | callIndirect _ _ => simp [simStep] at h
  | refNull _ => simp [simStep] at h
  | refIsNull => simp [simStep] at h
  | refFunc _ => simp [simStep] at h
  | drop => simp [simStep] at h
  | select _ => simp [simStep] at h
  | localGet _ => simp [simStep] at h
  | localSet _ => simp [simStep] at h
  | localTee _ => simp [simStep] at h
  | globalGet _ => simp [simStep] at h
  | globalSet _ => simp [simStep] at h
  | tableGet _ => simp [simStep] at h
  | tableSet _ => simp [simStep] at h
  | tableSize _ => simp [simStep] at h
  | tableGrow _ => simp [simStep] at h
  | tableFill _ => simp [simStep] at h
  | tableCopy _ _ => simp [simStep] at h
  | tableInit _ _ => simp [simStep] at h
  | elemDrop _ => simp [simStep] at h
  | load _ _ _ => simp [simStep] at h
  | store _ _ _ => simp [simStep] at h
  | memSize => simp [simStep] at h
  | memGrow => simp [simStep] at h
  | memCopy => simp [simStep] at h
  | memFill => simp [simStep] at h
  | memInit _ => simp [simStep] at h
  | dataDrop _ => simp [simStep] at h
  | i32Const _ => simp [simStep] at h
  | i64Const _ => simp [simStep] at h
  | num _ => simp [simStep] at h
  | float _ => simp [simStep] at h
  | f32Const _ => simp [simStep] at h
  | f64Const _ => simp [simStep] at h
  | floatLoad _ _ _ => simp [simStep] at h
  | floatStore _ _ _ => simp [simStep] at h

/-- The key inversion: if the transition from `(pc, sim, grd)` advances, it advances by
exactly one pc, and the resulting state is `simStep`'s result on a free instruction in range.
(The four `simStep` constructors are the only advancing moves `simNext` makes.) -/
private theorem simNext_inv (pf : PFunc) (pc : Nat) (sim : List SimLab) (grd : Nat)
    (hne : (simNext pf (pc, sim, grd)).1 ≠ pc) :
    ∃ (i : Instr) (sim' : List SimLab),
      pc < pf.code.size ∧ pf.code[pc]? = some i ∧ pf.gas[pc]? = some none ∧
        simStep pf pc sim i = some (pc + 1, sim') ∧
        simNext pf (pc, sim, grd) = (pc + 1, sim', Nat.max grd (endDemand sim)) := by
  unfold simNext at hne ⊢
  simp only at hne ⊢
  -- level 1: the dite on pc < code.size (split handles the dependent if, one binder)
  split at hne
  · -- in range: the pair match; case on the gas entry's shape via its equation
    rename_i hpc
    have hcode : pf.code[pc]? = some pf.code[pc] := Array.getElem?_eq_getElem hpc
    cases hgas : pf.gas[pc]? with
    | none =>
      -- the gas entry is missing: the pair match's second scrutinee is `none`, not
      -- `some none`, so the default (pc, sim, grd) applies — no advance, contradiction
      rw [hgas] at hne
      simp at hne
    | some g =>
      rw [hgas] at hne
      cases g with
      | none =>
        -- free instruction: simStep advance or stall (the goal's gas slot is already `none`)
        cases hss : simStep pf pc sim pf.code[pc] with
        | some p =>
          obtain ⟨pc'', sim'⟩ := p
          have hpc2 : pc'' = pc + 1 := simStep_pc pf pc sim _ pc'' sim' hss
          refine ⟨pf.code[pc], sim', hpc, hcode, rfl, ?_, ?_⟩
          · rw [hpc2] at hss; exact hss
          · show (if h : pc < pf.code.size then
                match pf.code[pc], (some none : Option (Option (IK × Fee))) with
                | i, some none =>
                  match simStep pf pc sim i with
                  | some (pc', sim') => (pc', sim', grd.max (endDemand sim))
                  | none => (pc, sim, grd)
                | x, x_1 => (pc, sim, grd)
              else (pc, sim, grd)) = _
            rw [hpc2] at hss
            -- reduce the pair match (iota on the literal `some none`) and the simStep
            -- match (hss); then the outer dite by hpc
            simp only [hss]
            rw [dif_pos hpc]
        | none =>
          -- the pair match binds i (with i := pf.code[pc] after iota); simp reduces both
          simp only [hss] at hne
          simp at hne
      | some _ =>
        simp at hne
  · -- out of range: simNext = (pc, sim, grd), contradicting hne (pc ≠ pc)
    rename_i hpc
    simp only at hne
    exact absurd rfl hne

/-- Every one of the first `runFrom pf fuel st` transitions advances the pc by exactly one.
(Maximality — that the run stops at a real stall — is *not* needed for soundness: an
early-stopping arc skips fewer instructions but is still a valid arc; `ArcOK` does not
require it.) -/
private theorem runFrom_steps (pf : PFunc) (fuel : Nat) (st : Nat × List SimLab × Nat) :
    ∀ (k : Nat) (hk : k < runFrom pf fuel st),
      (runSteps pf k st).1 + 1 = (runSteps pf (k + 1) st).1 := by
  induction fuel generalizing st with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ fuel ih =>
    intro k hk
    unfold runFrom at hk
    split at hk
    · -- stalled at the first transition: runFrom = 0, no k satisfies hk
      exact absurd hk (Nat.not_lt_zero k)
    · -- advanced: runFrom (fuel+1) st = runFrom fuel st' + 1, st' = simNext st
      rename_i hadv
      match k with
      | 0 =>
        -- the first transition: hadv says the pc changed; simNext_inv pins it to +1
        show (runSteps pf 0 st).1 + 1 = (runSteps pf 1 st).1
        -- runSteps 1 st = simNext (runSteps 0 st) = simNext st
        obtain ⟨i, sim', hpc, hcode, hgas, hss, hnext⟩ :=
          simNext_inv pf st.1 st.2.1 st.2.2 hadv
        -- hnext : simNext (st.1, st.2.1, st.2.2) = (st.1 + 1, sim', …); project the pc
        have h1 : (simNext pf st).1 = st.1 + 1 := by
          have : simNext pf st = simNext pf (st.1, st.2.1, st.2.2) := rfl
          rw [this]
          exact congrArg Prod.fst hnext
        show st.1 + 1 = (simNext pf (runSteps pf 0 st)).1
        show st.1 + 1 = (simNext pf st).1
        exact h1.symm
      | j + 1 =>
        -- later transitions: the ih at st' = simNext st
        have hk' : j < runFrom pf fuel (simNext pf st) := by
          -- hk : j + 1 < runFrom fuel st' + 1 (the split's else arm)
          omega
        -- peel one transition off each side (each equation's pattern is side-specific)
        have hL : runSteps pf (j + 1) st = runSteps pf j (simNext pf st) :=
          runSteps_peel pf j st
        have hR : runSteps pf (j + 1 + 1) st = runSteps pf (j + 1) (simNext pf st) :=
          runSteps_peel pf (j + 1) st
        rw [hL, hR]
        exact ih (simNext pf st) j hk'

/-- The pc after the run: `runSteps (runFrom fuel st) st` advanced `runFrom` times, each by
one, so its pc is the start's pc plus the count. -/
private theorem runFrom_end (pf : PFunc) (fuel : Nat) (st : Nat × List SimLab × Nat) :
    (runSteps pf (runFrom pf fuel st) st).1 = st.1 + runFrom pf fuel st := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel ih =>
    unfold runFrom
    split
    · -- stalled immediately: runFrom = 0
      rfl
    · -- advanced: runFrom (fuel+1) st = runFrom fuel st' + 1
      rename_i hadv
      -- the pc chain: runSteps (runFrom fuel st' + 1) st = runSteps (runFrom fuel st') st'
      -- (peeling the first transition), whose pc is st'.1 + runFrom fuel st' by ih,
      -- and st'.1 = st.1 + 1 by simNext_inv
      obtain ⟨i, sim', hpc, hcode, hgas, hss, hnext⟩ :=
        simNext_inv pf st.1 st.2.1 st.2.2 hadv
      have h1 : (simNext pf st).1 = st.1 + 1 := by
        have : simNext pf st = simNext pf (st.1, st.2.1, st.2.2) := rfl
        rw [this]
        exact congrArg Prod.fst hnext
      -- peel the last transition off
      rw [runSteps_peel pf (runFrom pf fuel (simNext pf st)) st]
      -- now the pc is (simNext st).1 + runFrom fuel (simNext st) by ih
      have hih := ih (simNext pf st)
      rw [hih]
      -- so the claim is (st.1 + 1) + runFrom fuel st' = st.1 + (runFrom fuel st' + 1)
      show (simNext pf st).1 + runFrom pf fuel (simNext pf st) = _
      rw [h1]
      omega

def buildFrom (pf : PFunc) (left : Nat) (out : Array (Option Arc)) : Array (Option Arc) :=
  if left = 0 then out else
    let pc := pf.code.size - left
    let len := runFrom pf left (pc, [], 0)
    if 2 ≤ len then
      let st := runSteps pf len (pc, [], 0)
      buildFrom pf (pf.code.size - st.1) (out.set! pc (some ⟨pc, st.1, st.2.1, st.2.2⟩))
    else buildFrom pf (left - 1) out
termination_by left
decreasing_by
  -- then-branch: st.1 = pc + len with 2 ≤ len, so code.size - st.1 < left
  · have hend := runFrom_end pf left (pc, [], 0)
    rename_i hlen
    -- hend : (runSteps len (pc, [], 0)).1 = pc + len; st is that same triple, so
    -- st.1 = pc + len by hend (both sides are the same projection of the same term)
    have hst : st.1 = pc + len := hend
    have hpc : pc = pf.code.size - left := rfl
    have hne : left ≠ 0 := by assumption
    have hlen' : len ≤ left := runFrom_le pf left (pc, [], 0)
    -- code.size - st.1 = code.size - (pc + len) with pc = code.size - left,
    -- so = left - len < left (len ≥ 2, left ≥ 1... need len < left, i.e. len ≤ left
    -- and len ≥ 2 with left > len impossible unless... left ≥ len ≥ 2 gives
    -- left - len ≥ 0; we need < left: left - len < left iff len > 0 ∧ left > 0 ✓
    have : pf.code.size - st.1 < left := by omega
    omega
  -- else-branch: left - 1 < left (left ≥ 1)
  · omega

/-- The arc table of one function (a slot per pc; `none` = no arc). -/
def arcsFor (pf : PFunc) : Array (Option Arc) :=
  buildFrom pf pf.code.size (Array.replicate pf.code.size none)

/-! ## The fast layer -/

/-- Find the arc at the top frame's pc, with the guard satisfied: at the fire point the walk's
`sim` is empty, so `f.labels` *is* the entry list the guard demands its length about. -/
def findArc (arcs : Array (Array (Option Arc))) (s : St) : Option (Arc × Frame) :=
  match s.frames with
  | f :: _ =>
    match (arcs[f.fn]?).bind (fun row => (row[f.pc]?).join) with
    | some a => if a.guard ≤ f.labels.length then some (a, f) else none
    | none => none
  | [] => none

/-- `runFast` is `run`, except that at an arc whose run fits the remaining budget the whole
run executes as one jump (`applyArc`), consuming its length in fuel; every other step is
exactly `Exec.step`. -/
def runFast (cfg : NearCfg) (p : Prepared) (arcs : Array (Array (Option Arc))) :
    Nat → St → Res
  | 0, _ => .unmodeled "fuel exhausted"
  | n + 1, s =>
    match findArc arcs s with
    | some (a, f) =>
      if a.runEnd - a.pc0 ≤ n + 1 ∧ 0 < a.runEnd - a.pc0 then
        runFast cfg p arcs (n + 1 - (a.runEnd - a.pc0)) (applyArc s f a)
      else
        match step cfg p s with
        | .cont s' => runFast cfg p arcs n s'
        | r => r
    | none =>
      match step cfg p s with
      | .cont s' => runFast cfg p arcs n s'
      | r => r

/-! ## The equivalence

`runFast = run` for every fuel, given `arcsValidFor`. The chain: a valid arc's run
single-steps through exactly the simulator's states (`step_walk`), so the `k` steps the arc
skips are `seg k` ending in `applyArc` (`arc_seg`), and `runFast`'s recursion is `run`'s with
that one substitution (`runFast_eq_run`). -/

/-- Two frames with equal fields are equal (eta + componentwise). -/
private theorem frame_congr {f g : Frame} (h1 : f.fn = g.fn) (h2 : f.pc = g.pc)
    (h3 : f.locals = g.locals) (h4 : f.labels = g.labels) (h5 : f.base = g.base) :
    f = g := by
  rw [show f = ⟨f.fn, f.pc, f.locals, f.labels, f.base⟩ from rfl,
      show g = ⟨g.fn, g.pc, g.locals, g.labels, g.base⟩ from rfl,
      h1, h2, h3, h4, h5]

/-- `matLabels` preserves length. -/
private theorem matLabels_length (H : Nat) : ∀ (l : List SimLab), (matLabels H l).length = l.length
  | [] => rfl
  | _ :: t => by simp only [matLabels, List.length_cons, matLabels_length H t]

/-- The frame part of `applyArc`: rebuilding the label list from the walk state. -/
private theorem applyArc_frames (s : St) (f : Frame) (fs : List Frame) (a : Arc)
    (hf : s.frames = f :: fs) :
    (applyArc s f a).frames =
        ({ f with pc := a.runEnd, labels := matLabels s.stack.size a.pushes ++ f.labels } : Frame) :: fs := by
  unfold applyArc
  rw [setFrame_frames hf]

/-- The run-relative invariant: the top frame's label list is the materialization of the
simulator's pushes above an *unchanged entry tail* `en`. `matLabels H sim ++ en` with `en`
independent of the run. This is what the walk preserves and `applyArc` re-establishes. -/
def SimInv (f : Frame) (fn : Nat) (pc : Nat) (sim : List SimLab) (en : List Label)
    (H : Nat) (locals : Array Val) (base : Nat) : Prop :=
  f.fn = fn ∧ f.pc = pc ∧ f.labels = matLabels H sim ++ en ∧
    f.locals = locals ∧ f.base = base

/-- Key correspondence, one run instruction: if the simulator advances from `(pc, sim)` to
`(pc', sim')`, then the real interpreter steps to `.cont` of the corresponding state,
preserving the invariant (same entry tail and stack height). For an in-run `end`,
`hend : 2 ≤ sim.length + en.length` is the guard condition that makes `exec .end_` take the
pop arm (the walk's `endDemand sim ≤ guard ≤ |en|` at fire time; `step_walk` propagates it). -/
private theorem step_sim {cfg : NearCfg} {p : Prepared} {pf : PFunc} {fn pc pc' : Nat}
    {sim sim' : List SimLab} {i : Instr} {en : List Label} {H : Nat}
    (hpff : p.funcs[fn]? = some pf)
    (hstep : simStep pf pc sim i = some (pc', sim'))
    (s : St) (f : Frame) (fs : List Frame)
    (hi : pf.code[pc]? = some i) (hfree : pf.gas[pc]? = some none)
    (hf : s.frames = f :: fs) (hfn : f.fn = fn)
    (hinv : SimInv f fn pc sim en H f.locals f.base)
    (hend : i = .end_ → 2 ≤ sim.length + en.length)
    (hsH : s.stack.size = H) :
    ∃ s' : St, step cfg p s = .cont s' ∧
      ∃ f' : Frame, s' = { s with frames := f' :: fs } ∧ SimInv f' fn pc' sim' en H f.locals f.base ∧
        s'.stack.size = s.stack.size := by
  obtain ⟨hfn, hpc, hlab, hloc, hbase⟩ := hinv
  -- `hen` says the total label depth is ≥ 1: the only relevant sub-case is en ≠ [], because
  -- at an in-run `end` the list `matLabels H sim ++ en` must have length ≥ 2 to take the pop
  -- arm (a singleton list would make `exec .end_` return/pop). We case on the instruction.
  cases i with
  | block bt =>
    simp only [simStep] at hstep
    cases he : pf.endOf[pc]? with
    | some e =>
      rw [he] at hstep
      simp only [Option.some.injEq, Option.getD_some] at hstep
      obtain ⟨rfl, rfl⟩ : pc' = pc + 1 ∧
          sim' = ((e + 1, (btResults bt).size, false) : SimLab) :: sim := by
        simp only [Prod.mk.injEq] at hstep
        exact ⟨hstep.1.symm, hstep.2.symm⟩
      -- the state exec .block produces: label list = newlab :: (matLabels H sim ++ en)
      refine ⟨{ s with frames := ({ f with pc := pc + 1, labels :=
        ({ target := e + 1, arity := (btResults bt).size, height := H, isLoop := false } : Label)
          :: (matLabels H sim ++ en) } : Frame) :: fs }, ?_, ?_⟩
      · simp only [step, hf, hpff, hfn, hpc, hi, hfree]
        simp only [exec, setFrame, hf, hfn, hpc]
        rw [he, hlab, hsH]
      · -- the frame witness: state shape by rfl, SimInv components, size kept
        refine ⟨{ f with pc := pc + 1, labels :=
          ({ target := e + 1, arity := (btResults bt).size, height := H, isLoop := false } : Label)
            :: (matLabels H sim ++ en) }, rfl, ?_, rfl⟩
        exact ⟨hfn, rfl, rfl, hloc, hbase⟩
    | none =>
      -- simulator stalls (no endOf entry): contradiction with hstep
      rw [he] at hstep
      simp at hstep
  | loop bt =>
    -- simulator: (pc+1, (pc+1, 0, true) :: sim)
    simp only [simStep, Option.some.injEq, Prod.mk.injEq] at hstep
    obtain ⟨rfl, rfl⟩ : pc' = pc + 1 ∧
        sim' = ((pc + 1, 0, true) : SimLab) :: sim := ⟨hstep.1.symm, hstep.2.symm⟩
    refine ⟨{ s with frames := ({ f with pc := pc + 1, labels :=
      ({ target := pc + 1, arity := 0, height := H, isLoop := true } : Label)
        :: (matLabels H sim ++ en) } : Frame) :: fs }, ?_, ?_⟩
    · simp only [step, hf, hpff, hfn, hpc, hi, hfree]
      simp only [exec, setFrame, hf]
      rw [hlab, hsH, hfn, hpc]
    · refine ⟨{ f with pc := pc + 1, labels :=
        ({ target := pc + 1, arity := 0, height := H, isLoop := true } : Label)
          :: (matLabels H sim ++ en) }, rfl, ?_, rfl⟩
      exact ⟨hfn, rfl, rfl, hloc, hbase⟩
  | nop =>
    -- simulator: (pc+1, sim); nop keeps the label list
    simp only [simStep, Option.some.injEq, Prod.mk.injEq] at hstep
    obtain ⟨rfl, rfl⟩ : pc' = pc + 1 ∧ sim' = sim := ⟨hstep.1.symm, hstep.2.symm⟩
    refine ⟨{ s with frames := ({ f with pc := pc + 1, labels := f.labels } : Frame) :: fs }, ?_, ?_⟩
    · simp only [step, hf, hpff, hfn, hpc, hi, hfree]
      simp only [exec, setFrame, hf]
      rw [hfn, hpc]
    · exact ⟨{ f with pc := pc + 1, labels := f.labels }, rfl,
        ⟨hfn, rfl, hlab, hloc, hbase⟩, rfl⟩
  | end_ =>
    -- simulator: pops a run label (sim = lab :: t)
    simp only [simStep] at hstep
    match hsim : sim with
    | [] => simp at hstep
    | lab :: t =>
      simp only [hsim, Option.some.injEq, Prod.mk.injEq] at hstep
      rcases hstep with ⟨rfl, hsim'⟩
      -- labels at this end: matLabels H (lab :: t) ++ en; its length is ≥ 2 by the guard
      have hlen : 2 ≤ (matLabels H (lab :: t) ++ en).length := by
        have h1 := hend rfl
        simp only [List.length_cons, List.length_append, matLabels_length] at h1 ⊢
        omega
      refine ⟨{ s with frames := ({ f with pc := pc + 1, labels := matLabels H t ++ en } : Frame)
        :: fs }, ?_, ?_⟩
      · -- step: exec .end_ with the label list of length ≥ 2 takes the pop arm
        simp only [step, hf, hpff, hfn, hpc, hi, hfree]
        rw [exec.eq_7]
        -- rewrite f.labels to the literal cons, then case the tail
        obtain ⟨tg, ar, lp⟩ := lab
        have hlab2 : f.labels = ({ target := tg, arity := ar, height := H, isLoop := lp } : Label)
            :: matLabels H t ++ en := by
          rw [hlab]
          simp only [matLabels]
        rw [hlab2]
        cases htail2 : (matLabels H t ++ en) with
        | nil =>
          -- singleton list — contradicts hlen: unfold matLabels on the cons (only hlen
          -- needs it; the goal's scrutinee is already the cons form), push the cons out
          -- of the append, rewrite the (empty) tail
          have hc : (matLabels H ((tg, ar, lp) :: t) ++ en).length
              = 1 + (matLabels H t ++ en).length := by
            simp only [matLabels, List.length_cons, List.length_append, matLabels_length]
            omega
          rw [hc, htail2, List.length_nil] at hlen
          -- hlen : 2 ≤ 1 + 0 — impossible; the guard excludes the singleton case
          omega
        | cons r rs =>
          -- the scrutinee is (lab' :: matLabels H t) ++ en; push the cons out, rewrite
          -- the tail to r :: rs, and the match iota-reduces to the pop arm
          rw [List.cons_append, htail2]
          -- normalize f.fn/f.pc/frame-update to the RHS shape
          simp only [setFrame, hf, hfn, hpc]
      · -- the frame witness: state shape, SimInv, size
        refine ⟨{ f with pc := pc + 1, labels := matLabels H t ++ en }, rfl, ?_, rfl⟩
        have hs : sim' = t := hsim'.symm
        rw [hs]
        exact ⟨hfn, rfl, rfl, hloc, hbase⟩
  | _ => simp [simStep] at hstep

/-! ## The walk's advance facts -/

/-- `simNext` never lowers the guard accumulator: it either keeps `grd` or takes
`max grd (endDemand sim)` at an in-run `end`. -/
private theorem simNext_grd_ge (pf : PFunc) (pc : Nat) (sim : List SimLab) (grd : Nat) :
    grd ≤ (simNext pf (pc, sim, grd)).2.2 := by
  -- unfold + iota-reduce the outer tuple match; the if and the pair match remain
  simp only [simNext]
  split
  · -- pc in range: the (code, gas) pair match
    rename_i hpc
    split
    · -- free: simStep advance (max) or stall (grd)
      rename_i i hgas
      -- one more level: simStep's advance or stall
      cases hss : simStep pf pc sim pf.code[pc] with
      | some p =>
        -- advance: the accumulator is Nat.max grd (endDemand sim)
        obtain ⟨pc', sim'⟩ := p
        show grd ≤ Nat.max grd (endDemand sim)
        exact Nat.le_max_left grd (endDemand sim)
      | none => exact Nat.le_refl _
    · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- The walk's guard accumulator is monotone along the walk: position `k`'s accumulator
is at most position `k + j`'s. -/
private theorem simWalk_grd_mono (pf : PFunc) (pc0 : Nat) :
    ∀ (k j : Nat), (simWalk pf pc0 k).2.2 ≤ (simWalk pf pc0 (k + j)).2.2 := by
  intro k
  induction k with
  | zero =>
    intro j
    induction j with
    | zero => exact Nat.le_refl _
    | succ j ih =>
      -- simWalk (0+(j+1)) = simNext (simWalk (0+j)) by the step equation
      rw [show (0 + (j + 1)) = (0 + j) + 1 from rfl, simWalk.eq_2]
      obtain ⟨a, b, c, heq⟩ : ∃ a b c, simWalk pf pc0 (0 + j) = (a, b, c) :=
        ⟨_, _, _, rfl⟩
      rw [heq] at ih ⊢
      exact Nat.le_trans ih (simNext_grd_ge pf a b c)
  | succ k ih =>
    intro j
    induction j with
    | zero => exact Nat.le_refl _
    | succ j ihj =>
      -- goal: (simWalk (k+1)).grd ≤ (simWalk ((k+1+j)+1)).grd
      -- rewrite only the RHS's step: simWalk (X+1) = simNext (simWalk X)
      obtain ⟨a, b, c, heq⟩ : ∃ a b c, simWalk pf pc0 (k + 1 + j) = (a, b, c) :=
        ⟨_, _, _, rfl⟩
      have hstep : simWalk pf pc0 (k + 1 + j + 1) = simNext pf (simWalk pf pc0 (k + 1 + j)) := rfl
      show (simWalk pf pc0 (k + 1)).2.2 ≤ (simNext pf (simWalk pf pc0 (k + 1 + j))).2.2
      rw [heq] at ihj ⊢
      -- ihj : (simWalk (k+1)).2.2 ≤ (a, b, c).2.2 — and (a,b,c).2.2 is definitionally c
      exact Nat.le_trans ihj (simNext_grd_ge pf a b c)


/-- A valid arc's landing guard: for positions `j ≤ len`, the walk's accumulator at `j` is at
most `a.guard` (the landing state's third component). -/
private theorem walk_grd_le_landing (pf : PFunc) {a : Arc} (hok : ArcOK pf a) (j : Nat)
    (hj : j ≤ a.runEnd - a.pc0) :
    (simWalk pf a.pc0 j).2.2 ≤ a.guard := by
  -- monotonicity: (walk j).grd ≤ (walk (j + (len - j))).grd = (walk len).grd = a.guard
  have h1 := simWalk_grd_mono pf a.pc0 j (a.runEnd - a.pc0 - j)
  have hlen : j + (a.runEnd - a.pc0 - j) = a.runEnd - a.pc0 := by omega
  rw [hlen] at h1
  -- the landing: (walk len) = (runEnd, pushes, guard) by ArcOK
  have hlanding := hok.2.2.1
  rw [hlanding] at h1
  -- h1 : (walk j).grd ≤ (runEnd, pushes, a.guard).grd = a.guard
  exact h1

/-- If the walk from `pc0` advances at every position `< m`, its pc at position `k ≤ m`
is `pc0 + k`. -/
private theorem walk_pc_chain (pf : PFunc) (pc0 m : Nat)
    (hadv : ∀ (k : Nat) (hk : k < m), (simWalk pf pc0 k).1 + 1 = (simWalk pf pc0 (k + 1)).1)
    (k : Nat) (hk : k ≤ m) : (simWalk pf pc0 k).1 = pc0 + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hklt : k < m := Nat.lt_of_succ_le hk
    have h1 : (simWalk pf pc0 (k + 1)).1 = (simWalk pf pc0 k).1 + 1 := (hadv k hklt).symm
    show (simWalk pf pc0 (k + 1)).1 = pc0 + (k + 1)
    rw [h1, ih (Nat.le_of_succ_le hk)]
    rfl

/-- The walk and the real interpreter agree over a whole arc run: from a state satisfying the
invariant at `(pc0, [])` (entry labels `en` with `guard ≤ |en|`), the `k`-th single step of the
run is `.cont` of the `(k+1)`-th walk state, for every `k < len` (induction on the walk; the
guard's demand is exactly what `step_sim`'s `hend` needs at each in-run `end`). -/
private theorem step_walk {cfg : NearCfg} {p : Prepared} {pf : PFunc} {fn : Nat} {a : Arc} {en : List Label}
    {H : Nat} {s0 : St} {f0 : Frame} {fs : List Frame}
    (hpff : p.funcs[fn]? = some pf)
    (hvalid : ArcOK pf a)
    (hf : s0.frames = f0 :: fs) (hfn : f0.fn = fn) (hpc0 : f0.pc = a.pc0)
    (hlab0 : f0.labels = en) (hgrd : a.guard ≤ en.length)
    (hsH : s0.stack.size = H) :
    ∀ (k : Nat) (hk : k ≤ a.runEnd - a.pc0),
      ∃ (s : St) (f : Frame), seg cfg p k s0 = .cont s ∧
        s = { s0 with frames := f :: fs } ∧
          SimInv f fn (a.pc0 + k) (simWalk pf a.pc0 k).2.1 en H f0.locals f0.base ∧
          s.stack.size = s0.stack.size := by
  intro k
  induction k with
  | zero =>
    -- zero steps: the state is s0 itself; the walk at 0 is (pc0, [], 0)
    intro _
    refine ⟨s0, f0, rfl, ?_, ?_, rfl⟩
    · -- s0 = {s0 with frames := f0 :: fs}, given hf : s0.frames = f0 :: fs
      rw [← hf]
    · exact ⟨hfn, hpc0, by rw [hlab0]; rfl, rfl, rfl⟩
  | succ k ih =>
    -- the (k+1)-th step: `seg (k+1) = step >>= seg k`; by ih the state after k steps
    -- satisfies the invariant at walk position k; the advance clause (ArcOK) + simNext_inv
    -- make the instruction run-determined, and step_sim gives the .cont continuation.
    intro hk
    have hk' : k ≤ a.runEnd - a.pc0 := Nat.le_of_succ_le hk
    obtain ⟨s1, f1, hseg1, hshape1, hinv1, hstack1⟩ := ih hk'
    obtain ⟨hfn1, hpc1, hlab1, hloc1, hbase1⟩ := hinv1
    -- the walk state at position k
    obtain ⟨pc_k, sim_k, grd_k, hwk⟩ :
        ∃ pc_k sim_k grd_k, simWalk pf a.pc0 k = (pc_k, sim_k, grd_k) :=
      ⟨_, _, _, rfl⟩
    -- the advance clause of ArcOK (k < len since k+1 ≤ len)
    have hklt : k < a.runEnd - a.pc0 := Nat.lt_of_succ_le hk
    have hadvk := hvalid.2.2.2 k hklt
    -- the walk's pc at k: pc0 + k (the advance chain)
    have hpc_k : (simWalk pf a.pc0 k).1 = a.pc0 + k :=
      walk_pc_chain pf a.pc0 (a.runEnd - a.pc0) (fun j hj => hvalid.2.2.2 j hj) k hk'
    -- link the walk's sim to sim_k and f1's labels to sim_k (via hwk)
    have hsims : (simWalk pf a.pc0 k).2.1 = sim_k := by rw [hwk]
    rw [hsims] at hlab1
    -- f1.pc = pc_k (both are pc0 + k)
    have hpc_k' : pc_k = a.pc0 + k := by
      have h := hpc_k
      rw [hwk] at h
      exact h
    have hfpk : f1.pc = pc_k := by rw [hpc1, hpc_k']
    -- the advance at position k: the simNext transition from (pc_k, sim_k, grd_k)
    -- moved the pc, so simNext_inv applies
    have hadv : (simNext pf (pc_k, sim_k, grd_k)).1 ≠ pc_k := by
      -- simWalk (k+1) = simNext (simWalk k) = simNext (pc_k, sim_k, grd_k)
      have h1 : simWalk pf a.pc0 (k + 1) = simNext pf (pc_k, sim_k, grd_k) := by
        rw [simWalk.eq_2 (pf := pf) (pc0 := a.pc0) (k := k), hwk]
      -- hadvk : (simWalk k).1 + 1 = (simWalk (k+1)).1, so the pc moved
      have h2 : (simWalk pf a.pc0 k).1 + 1 = (simWalk pf a.pc0 (k + 1)).1 := hadvk
      rw [hwk] at h2
      rw [← h1]
      show (simWalk pf a.pc0 (k + 1)).1 ≠ pc_k
      have h2' : pc_k + 1 = (simWalk pf a.pc0 (k + 1)).1 := h2
      omega
    obtain ⟨i, sim', hpcIR, hcode, hgas, hss, hnext⟩ := simNext_inv pf pc_k sim_k grd_k hadv
    -- the guard condition for step_sim's hend: at an in-run end, 2 ≤ |sim_k| + |en|
    -- (from the walk's guard demand: endDemand sim_k ≤ the accumulated guard ≤ a.guard
    -- ≤ |en|; and |sim_k| ≥ 1 since simStep's end pops one of sim)
    have hend : i = .end_ → 2 ≤ sim_k.length + en.length := by
      intro hi
      -- simStep's end arm with result some (pc+1, sim') implies sim_k is nonempty
      cases hsimk : sim_k with
      | nil =>
        -- simStep on .end_ with empty sim is none, contradicting hss
        rw [hi] at hss
        rw [hsimk] at hss
        simp [simStep] at hss
      | cons lab t =>
        -- the walk at position k advanced (hadvk), so its accumulator absorbed
        -- endDemand sim_k on this transition; monotonicity carries it to the landing
        -- guard, and the fire-time guard bounds that by |en|:
        --   endDemand (lab :: t) ≤ grd_{k+1} ≤ a.guard ≤ |en|
        -- endDemand (lab :: t) = 2 - (lab :: t).length, and |lab :: t| ≥ 1, so
        -- 2 ≤ |lab :: t| + |en| follows from 2 - |lab::t| ≤ |en|.
        have hmon : (simWalk pf a.pc0 (k + 1)).2.2 ≤ a.guard :=
          walk_grd_le_landing pf hvalid (k + 1) hk
        -- the walk's accumulator at k+1 absorbed endDemand sim_k on the advance (the
        -- transition at position k advanced and sim_k is the pre-state sim): extract it
        -- from the transition equation
        have habs : Nat.max grd_k (endDemand sim_k) ≤ (simWalk pf a.pc0 (k + 1)).2.2 := by
          -- simWalk (k+1) = simNext (simWalk k) = simNext (pc_k, sim_k, grd_k);
          -- the advance case of simNext sets the accumulator to max grd_k (endDemand sim_k)
          rw [show simWalk pf a.pc0 (k + 1) = simNext pf (pc_k, sim_k, grd_k) from by
              rw [simWalk.eq_2 (pf := pf) (pc0 := a.pc0) (k := k), hwk]]
          rw [hnext]
          exact Nat.le_refl _
        -- so endDemand (lab :: t) ≤ max grd_k (endDemand sim_k) ≤ walk(k+1).grd ≤ a.guard
        -- ≤ |en|; with endDemand = 2 - |lab::t|:
        have hd : endDemand (lab :: t) ≤ en.length := by
          have h2 : Nat.max grd_k (endDemand sim_k) ≤ (simWalk pf a.pc0 (k + 1)).2.2 := habs
          have h3 := Nat.le_trans h2 hmon
          have h4 : a.guard ≤ en.length := hgrd
          -- endDemand sim_k = endDemand (lab :: t) (sim_k = lab :: t by the cases)
          rw [hsimk] at *
          have h5 : endDemand (lab :: t) ≤ Nat.max grd_k (endDemand (lab :: t)) :=
            Nat.le_max_right _ _
          exact Nat.le_trans (Nat.le_trans h5 h3) h4
        -- endDemand (lab :: t) = 2 - (1 + t.length) ≤ |en| gives 2 ≤ 1 + t.length + |en|
        unfold endDemand at hd
        have hlen' : (lab :: t).length = 1 + t.length := by
          simp only [List.length_cons]
          omega
        rw [hlen'] at hd
        -- goal: 2 ≤ (lab :: t).length + en.length = 1 + t.length + |en|
        show 2 ≤ (lab :: t).length + en.length
        omega
    -- apply step_sim: the real step from s1 is .cont of the walk-advanced state
    -- step_sim needs s1.frames = f1 :: fs: project it from hshape1
    have hframes1 : s1.frames = f1 :: fs := by rw [hshape1]
    obtain ⟨s2, hstep2, f2, hshape2, hinv2, hsizes2⟩ :=
      step_sim (p := p) (pf := pf) (fn := fn) (pc := pc_k) (pc' := pc_k + 1)
        (sim := sim_k) (sim' := sim') (i := i) (en := en) (H := H)
        hpff hss s1 f1 fs hcode hgas hframes1 hfn1
        ⟨hfn1, hfpk, hlab1, rfl, rfl⟩ hend
        (by rw [hstack1]; exact hsH)
    -- chain: seg (k+1) s0 = seg k s0 >>= seg 1; the first k steps reach s1 (hseg1),
    -- the last step is hstep2
    have hseg2 : seg cfg p (k + 1) s0 = .cont s2 := by
      -- seg (k+1) = seg k then seg 1 (Segment.seg_add); the first part is hseg1
      rw [seg_add cfg p k 1 s0, hseg1]
      -- (cont s1).bind (seg 1) = seg 1 s1; seg 1 = step then seg 0 (the identity on cont)
      show (Res.cont s1).bind (seg cfg p 1) = Res.cont s2
      -- beta-reduce the bind: = seg cfg p 1 s1; then unfold seg 1 = step >>= seg 0
      show seg cfg p 1 s1 = Res.cont s2
      rw [show seg cfg p 1 s1 = (step cfg p s1).bind (seg cfg p 0) from rfl]
      rw [hstep2]
      rfl
    -- the frame's invariant at the walk's (k+1) position: pc' = pc_k + 1 = pc0 + (k+1),
    -- sim' = the walk's (k+1) sim
    have hwalknext : (simWalk pf a.pc0 (k + 1)).2.1 = sim' := by
      -- simWalk (k+1) = simNext (simWalk k) = simNext (pc_k, sim_k, grd_k) = (pc_k+1, sim', …)
      show (simNext pf (simWalk pf a.pc0 k)).2.1 = sim'
      rw [hwk]
      rw [hnext]
    -- s2's stack size: preserved by the step (hsizes2), and s1's was s0's (hstack1)
    have hstack2 : s2.stack.size = s0.stack.size := by
      rw [hsizes2, hstack1]
    refine ⟨s2, f2, hseg2, ?_, ?_, hstack2⟩
    · -- s2 = {s1 with frames := f2 :: fs} (hshape2) and s1 = {s0 with frames := f1 :: fs}
      -- (hshape1): compose into s2 = {s0 with frames := f2 :: fs}
      rw [hshape2, hshape1]
    · -- the SimInv: fn by hfn2, pc/labels by the walk landing, locals/base composed
      obtain ⟨hfn2, hpc2, hlab2, hloc2, hbase2⟩ := hinv2
      have hloc2' : f2.locals = f0.locals := by rw [hloc2, hloc1]
      have hbase2' : f2.base = f0.base := by rw [hbase2, hbase1]
      refine ⟨hfn2, ?_, ?_, hloc2', hbase2'⟩
      · -- f2.pc = pc0 + (k+1): pc_k + 1 = (pc0 + k) + 1
        show f2.pc = a.pc0 + (k + 1)
        rw [hpc2]
        have : pc_k = a.pc0 + k := hpc_k'
        omega
      · -- f2.labels = matLabels H (walk (k+1) sim) ++ en
        show f2.labels = matLabels H (simWalk pf a.pc0 (k + 1)).2.1 ++ en
        rw [hwalknext]
        exact hlab2
-- The walk's stall/advance facts are not needed as separate lemmas: `ArcOK` carries the
-- advance clause directly (the builder's `runFrom`-counted runs provide it), and the
-- guard monotonicity above transfers the fire-time guard to every in-run `end`.


/-! ## The arc-run equivalence -/

/-- A valid arc's whole run, single-stepped, is `.cont` of `applyArc`'s state: the run
(`step_walk` over `len` positions) ends at the walk's landing state, which is exactly
`applyArc` (pc at `runEnd`, labels `matLabels H pushes ++ en`). -/
private theorem arc_seg {cfg : NearCfg} {p : Prepared} {pf : PFunc} {fn : Nat} {a : Arc} {en : List Label}
    {H : Nat} {s0 : St} {f0 : Frame} {fs : List Frame}
    (hpff : p.funcs[fn]? = some pf)
    (hvalid : ArcOK pf a)
    (hf : s0.frames = f0 :: fs) (hfn : f0.fn = fn) (hpc0 : f0.pc = a.pc0)
    (hlab0 : f0.labels = en) (hgrd : a.guard ≤ en.length)
    (hsH : s0.stack.size = H) :
    seg cfg p a.len s0 = .cont (applyArc s0 f0 a) := by
  -- the landing state: pc = runEnd, labels = pushes (ArcOK's walk-landing)
  -- the walk's pc at len (the pc chain over ArcOK's advance clause)
  have hpclen : (simWalk pf a.pc0 (a.runEnd - a.pc0)).1 = a.pc0 + (a.runEnd - a.pc0) :=
    walk_pc_chain pf a.pc0 (a.runEnd - a.pc0) (fun j hj => hvalid.2.2.2 j hj)
      (a.runEnd - a.pc0) (Nat.le_refl _)
  -- the landing's pc IS a.runEnd (ArcOK's landing, projected)
  have hpcend : (simWalk pf a.pc0 (a.runEnd - a.pc0)).1 = a.runEnd := by rw [hvalid.2.2.1]
  -- so runEnd = pc0 + len
  have hrunEnd : a.runEnd = a.pc0 + a.len := by
    have : a.len = a.runEnd - a.pc0 := rfl
    omega
  -- the walk's pushes at len = a.pushes
  have hpush : (simWalk pf a.pc0 (a.runEnd - a.pc0)).2.1 = a.pushes := by rw [hvalid.2.2.1]
  -- the state after len steps (step_walk)
  obtain ⟨s1, f1, hseg1, hshape1, hinv1, hsizes1⟩ :=
    step_walk hpff hvalid hf hfn hpc0 hlab0 hgrd hsH (a.runEnd - a.pc0) (Nat.le_refl _)
  obtain ⟨hfn1, hpc1, hlab1, hloc1, hbase1⟩ := hinv1
  -- f1 is the landing frame: pc = pc0 + len = runEnd; labels = matLabels H pushes ++ en
  -- (hpc1's pc0 + len is the walk's landing pc = runEnd; hlab1's sim is the landing pushes)
  have hpc1' : f1.pc = a.runEnd := by
    rw [hpc1]
    -- the invariant's pc is pc0 + (runEnd - pc0) = runEnd
    omega
  have hlab1' : f1.labels = matLabels s0.stack.size a.pushes ++ f0.labels := by
    rw [hlab1, hpush, hlab0]
    -- the height H is s0.stack.size (hsH)
    rw [hsH]
  -- f1 vs the update: all five fields agree (fn, pc, labels, locals, base)
  have hf1' : f1 = { f0 with pc := a.runEnd, labels := matLabels s0.stack.size a.pushes ++ f0.labels } :=
    frame_congr (f := f1) (g := { f0 with pc := a.runEnd, labels := matLabels s0.stack.size a.pushes ++ f0.labels })
      (by rw [hfn1, hfn]) hpc1' hloc1 hlab1' hbase1
  have hs1 : s1 = applyArc s0 f0 a := by
    rw [hshape1, hf1']
    -- applyArc = setFrame s0 {f0 with pc/labels}; setFrame on f0 :: fs (by hf)
    unfold applyArc setFrame
    rw [hf]
  rw [← hs1]
  exact hseg1


/-- `runFast` equals `run` at every fuel, on a valid table (strong induction on the
fuel): the arc fire path replaces `seg len` + the remainder (by `arc_seg` + `run_seg`),
every other path single-steps identically. -/
private theorem runFast_eq_run (cfg : NearCfg) (p : Prepared)
    (arcs : Array (Array (Option Arc))) (hvalid : arcsValidFor p arcs) :
    ∀ (fuel : Nat) (s : St), runFast cfg p arcs fuel s = run cfg p fuel s := by
  intro fuel
  -- strong induction: the recursive calls are at strictly smaller fuels (the arc's
  -- length is >= 1 by ArcOK, so fuel+1-len < fuel+1; the single-step path recurses at
  -- fuel < fuel+1)
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro s
    match hfind : findArc arcs s with
    | none =>
      -- both single-step; the fuel must be a successor (zero gives fuel-exhausted = rfl)
      cases hfuel : fuel with
      | zero =>
        -- both report fuel exhausted (equations)
        show runFast cfg p arcs 0 s = run cfg p 0 s
        simp only [runFast, run]
      | succ m =>
        -- both single-step and recurse at m
        show runFast cfg p arcs (m + 1) s = run cfg p (m + 1) s
        unfold runFast run
        rw [hfind]
        show (match step cfg p s with
              | .cont s' => runFast cfg p arcs m s'
              | r => r) = (match step cfg p s with
              | .cont s' => run cfg p m s'
              | r => r)
        split
        · rename_i s' hs'
          have hlt : m < fuel := by rw [hfuel]; exact Nat.lt_succ_self m
          exact ih m hlt s'
        · rfl
    | some (a, f) =>
      -- the arc fire: extract the frame/arc facts from findArc's reduced form
      obtain ⟨fs, hf, hslotraw, hgrd, harceq⟩ :
          ∃ (fs : List Frame),
            s.frames = f :: fs ∧
              ((arcs[f.fn]?).bind fun row => (row[f.pc]?).join) = some a ∧
                a.guard ≤ f.labels.length ∧ a = a := by
        unfold findArc at hfind
        split at hfind
        · rename_i f0 frs hfr
          split at hfind
          · rename_i a₁ hlookup
            split at hfind
            · rename_i hgrd
              have h1 : (a₁, f0) = (a, f) := (Option.some.injEq ..) |>.mp hfind
              have hf0 : f0 = f := (Prod.mk.injEq ..) |>.mp h1 |>.2
              have ha₁ : a₁ = a := (Prod.mk.injEq ..) |>.mp h1 |>.1
              rw [hf0] at hfr hlookup hgrd
              rw [ha₁] at hlookup hgrd
              exact ⟨frs, hfr, hlookup, hgrd, rfl⟩
            · exact absurd hfind (by simp)
          · exact absurd hfind (by simp)
        · exact absurd hfind (by simp)
      -- the table's validity at f.fn gives ArcOK
      have hrow : ∃ pf, p.funcs[f.fn]? = some pf ∧
          ArcsOK pf (arcs[f.fn]?.getD #[]) := by
        obtain ⟨row, hroweq⟩ : ∃ row, arcs[f.fn]? = some row := by
          cases h : arcs[f.fn]? with
          | none => rw [h] at hslotraw; simp at hslotraw
          | some row => exact ⟨row, rfl⟩
        have hrowget : arcs[f.fn]?.getD #[] = row := by rw [hroweq]; rfl
        exact hvalid f.fn _ (by rw [hrowget]; exact hroweq)
      obtain ⟨pf, hpff, hrowok⟩ := hrow
      -- the slot at f.pc: from the bind chain
      have hslot : (arcs[f.fn]?.getD #[])[f.pc]? = some a := by
        obtain ⟨row, hroweq⟩ : ∃ row, arcs[f.fn]? = some row := by
          cases h : arcs[f.fn]? with
          | none => rw [h] at hslotraw; simp at hslotraw
          | some row => exact ⟨row, rfl⟩
        have hbind : (arcs[f.fn]?.bind fun r => (r[f.pc]?).join) = some a := hslotraw
        rw [hroweq] at hbind
        have hjoin : (row[f.pc]?).join = some a := hbind
        cases hrowpc : row[f.pc]? with
        | none => rw [hrowpc] at hjoin; simp at hjoin
        | some opt =>
          rw [hrowpc] at hjoin
          cases hopt : opt with
          | none => rw [hopt] at hjoin; simp at hjoin
          | some a₁ =>
            rw [hopt] at hjoin
            have ha₁ : a₁ = a := (Option.some.injEq ..) |>.mp hjoin
            show (arcs[f.fn]?.getD #[])[f.pc]? = some a
            rw [hroweq]
            have hget : (some row).getD #[] = row := rfl
            rw [hget, hrowpc, hopt, ha₁]
            rfl
      have haok : ArcOK pf a := (hrowok f.pc a hslot).2
      have hpc0 : a.pc0 = f.pc := (hrowok f.pc a hslot).1
      -- the fire vs run: the fuel must be a successor for any firing
      cases hfuel : fuel with
      | zero =>
        -- the goal's fuel was already substituted by the cases; close via the equations
        show runFast cfg p arcs 0 s = run cfg p 0 s
        simp only [runFast, run]
      | succ m =>
        show runFast cfg p arcs (m + 1) s = run cfg p (m + 1) s
        unfold runFast
        rw [hfind]
        -- the option match's scrutinee is the literal some (a, f): iota-reduce it so the
        -- split sees only the inner if
        show (if a.runEnd - a.pc0 ≤ m + 1 ∧ 0 < a.runEnd - a.pc0 then
              runFast cfg p arcs (m + 1 - (a.runEnd - a.pc0)) (applyArc s f a)
            else
              match step cfg p s with
              | .cont s' => runFast cfg p arcs m s'
              | r => r) = run cfg p (m + 1) s
        split
        · -- fits (the split's hypothesis is the conjunction)
          rename_i hfit
          obtain ⟨hfitlen, hfitpos⟩ := hfit
          -- run's side: seg + remainder
          have harc : seg cfg p (a.runEnd - a.pc0) s = .cont (applyArc s f a) :=
            arc_seg (p := p) (pf := pf) (fn := f.fn) (en := f.labels)
              (H := s.stack.size) hpff haok hf rfl (by rw [hpc0]) rfl hgrd rfl
          have hsplit : m + 1 = (a.runEnd - a.pc0) + (m + 1 - (a.runEnd - a.pc0)) := by
            have := hfitlen
            omega
          -- run's side: rewrite the fuel with hsplit (forward: m+1 → the sum), which
          -- makes run_seg applicable; then the seg is the jump (harc)
          rw [hsplit]
          -- normalize the LHS's fuel arithmetic (X + rest - X = rest)
          have hnorm : a.runEnd - a.pc0 + (m + 1 - (a.runEnd - a.pc0)) - (a.runEnd - a.pc0)
              = m + 1 - (a.runEnd - a.pc0) := by omega
          rw [hnorm, run_seg, harc]
          -- the recursive fuel: m+1-len < m+1 (len >= 1), so the strong ih applies
          have hlt : m + 1 - (a.runEnd - a.pc0) < m + 1 := by
            have := haok.1
            omega
          have hltm : m + 1 - (a.runEnd - a.pc0) < fuel := by rw [hfuel]; exact hlt
          exact ih _ hltm (applyArc s f a)
        · -- the inner if fails (the fuel does not fit): single-step on both sides
          show (match step cfg p s with
                | .cont s' => runFast cfg p arcs m s'
                | r => r) = run cfg p (m + 1) s
          rw [show run cfg p (m + 1) s = (match step cfg p s with
                | .cont s' => run cfg p m s'
                | r => r) from rfl]
          split
          · rename_i s' hs'
            have hlt : m < fuel := by rw [hfuel]; exact Nat.lt_succ_self m
            exact ih m hlt s'
          · rfl

/-! ## The call-level fast layer -/

/-- `callEntry` parameterized by the run function: `callEntryWith cfg p run fuel s fi`. -/
def callEntryWith (p : Prepared) (run : Nat → St → Res) (fuel : Nat) (s : St) (fi : Nat) :
    Except String (St × Option String) :=
  let s := { s with gas := { s.gas with g := s.gas.remaining }, stack := #[], frames := [] }
  let r := match enter p s fi with
    | .cont s => run fuel s
    | r => r
  match r with
  | .fin s => (sync s).map (·, none)
  | .abort s e => (sync s).map (·, some e)
  | .unmodeled why => .error why
  | .cont _ => .error "cont"

/-- `callEntry` is `callEntryWith` with the plain `run`. -/
theorem callEntry_eq_callEntryWith (cfg : NearCfg) (p : Prepared) (fuel : Nat) (s : St) (fi : Nat) :
    callEntry cfg p fuel s fi = callEntryWith p (run cfg p) fuel s fi := rfl

/-- The fast entry: `callEntryWith` with `runFast`. -/
def callEntryFast (cfg : NearCfg) (p : Prepared) (arcs : Array (Array (Option Arc)))
    (fuel : Nat) (s : St) (fi : Nat) : Except String (St × Option String) :=
  callEntryWith p (runFast cfg p arcs) fuel s fi

/-- The fast entry equals the plain one: the run functions agree by `runFast_eq_run`. -/
private theorem callEntryFast_eq_callEntry (cfg : NearCfg) (p : Prepared)
    (arcs : Array (Array (Option Arc))) (hvalid : arcsValidFor p arcs)
    (fuel : Nat) (s : St) (fi : Nat) :
    callEntryFast cfg p arcs fuel s fi = callEntry cfg p fuel s fi := by
  -- both are callEntryWith; the run functions agree on every state by runFast_eq_run,
  -- so the bodies are equal by a funext + pointwise rewrite
  rw [callEntryFast, callEntry_eq_callEntryWith cfg p fuel s fi]
  show callEntryWith p (runFast cfg p arcs) fuel s fi = callEntryWith p (run cfg p) fuel s fi
  have hfun : runFast cfg p arcs = run cfg p := by
    funext fuel' s'
    exact runFast_eq_run cfg p arcs hvalid fuel' s'
  rw [hfun]

/-- `runCall` with the fast table: identical control flow, the entries by `callEntryFast`. -/
def runCallFast (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (fuel : Nat) (blockLevel : Bool := true) (full : Bool := false)
    (real : Option TTN.RealStore := none) : NearSpecV3.Wasm.Run :=
  let emptySt (gs : Gas) : St :=
    { pages := #[], globals := #[], table := #[], tableMax := 0, elems := #[], datas := #[],
      stackRem := 0, gas := gs, ctx := ctx }
  let ext (s : St) : String := if full then fullExtra s else ""
  let nop (e : String) : NearSpecV3.Wasm.Run :=
    .line (s!"abort 0 0 {e}" ++ ext (emptySt (Gas.init ctx.prepaidGas)))
  if method.isEmpty then nop "MethodResolveError(MethodEmptyName)" else
  match prepare cfg code blockLevel with
  | .outOfDomain why => .line s!"out-of-domain {why}"
  | .unmodeled why => .line s!"unmodeled {why}"
  | .prepErr v _ => nop s!"CompilationError(PrepareError({v}))"
  | .compileErr k _ =>
    nop s!"CompilationError(WasmtimeCompileError \{ msg: \"failed to compile: wasm[0]::function[{k}]\" })"
  | .ok p =>
    if !cfg.curveHosts && real.isNone && p.m.imports.any (fun i => curveHosts.contains i.name) then
      .line "out-of-domain curve host function" else
    let gs : Gas := Gas.init ctx.prepaidGas
    let loaded := match payPer gs C.contractLoadingBytes code.size with
      | (gs, none) => payBase gs C.contractLoadingBase
      | r => r
    match loaded with
    | (gs, some _) => .line (s!"abort {gs.burnt} {gs.used} {errGasExceeded}" ++ ext (emptySt gs))
    | (gs, none) =>
      match link p with
      | .linkError msg => .line (s!"abort {gs.burnt} {gs.used} LinkError \{ msg: \"{msg}\" }" ++ ext (emptySt gs))
      | .invariant why => .line s!"unmodeled invariant: {why}"
      | .ok =>
        match resolve p method with
        | .notFound => nop "MethodResolveError(MethodNotFound)"
        | .invalidSignature => nop "MethodResolveError(MethodInvalidSignature)"
        | .invariant why => .line s!"unmodeled invariant: {why}"
        | .ok mi =>
          match instantiate cfg p gs with
          | .error e => .line (s!"abort {gs.burnt} {gs.used} {e}" ++ ext (emptySt gs))
          | .ok s =>
            let s := { s with ctx := ctx, balance := ctx.accountBalance + ctx.attachedDeposit,
                              storageUsage := ctx.storageUsage, real := real,
                              curveHosts := cfg.curveHosts }
            let arcs := p.funcs.map arcsFor
            let afterStart : Except String (St × Option String) :=
              match p.m.start with
              | some st => callEntryFast cfg p arcs fuel s st
              | none => .ok (s, none)
            match afterStart with
            | .error why => .line s!"unmodeled {why}"
            | .ok (s, some e) => .done s (some e)
            | .ok (s, none) =>
              match callEntryFast cfg p arcs fuel s mi with
              | .error why => .line s!"unmodeled {why}"
              | .ok (s, e) => .done s e

/-- `runCallFast = runCall`: identical control flow; the entries agree by
`callEntryFast_eq_callEntry` (the table validity comes from the builder:
`arcsFor_valid`). -/
private theorem runCallFast_eq_runCall (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) (fuel : Nat) (blockLevel full : Bool) (real : Option TTN.RealStore) :
    runCallFast cfg code method ctx fuel blockLevel full real =
      runCall cfg code method ctx fuel blockLevel full real := by
  -- the bodies are syntactically identical except:
  -- (a) the fast side builds the arcs table (only consumed by its entries),
  -- (b) the entry calls: callEntryFast vs callEntry.
  -- Since callEntryFast reduces to callEntryWith (runFast) and callEntry to
  -- callEntryWith (run cfg p), and the runs are equal by runFast_eq_run (with the
  -- table's validity from arcsFor_valid), the bodies are equal after zeta-reduction.
  -- The proof: simp both sides with the defining equations and the entry theorem.
  sorry

/-- The builder's rows satisfy `ArcsOK`: every emitted arc is a real run of its
function (by `runFrom_steps`/`runFrom_end` and the `runSteps` landing), and it sits at
its start pc. -/
theorem arcsFor_valid (pf : PFunc) : ArcsOK pf (arcsFor pf) := by
  sorry

end NearSpecV3.Wasm
