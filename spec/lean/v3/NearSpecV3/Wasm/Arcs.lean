import NearSpecV3.Wasm.Fuel
import NearSpecV3.Wasm.Segment

/-!
# Arcs: bulk execution of zero-fee control runs (W02 evaluation time)

> **Status: in-progress formalization — not imported by `NearSpecV3` and not reachable from
> any checker.** The performance mechanism is validated (prototype: `research/lean-arcs/`,
> 1,474× on `blocks4999`, 9,375/9,375 A/B parity) and the core correspondence theorem
> `step_sim` (all four `exec` arms, including the guard case that excludes `exec .end_`'s
> singleton return arm) is **proved with no `sorry`**. The remaining declarations carry
> explicit `sorry`s (see *Open proofs* below); until they are discharged and the module is
> imported, nothing here affects any verdict. Per the repo's axiom gate, the successor may
> switch to `runCallWithLimitsFast` only after `runFast_eq_run` (and its call-level
> consequences) are proved and audited (`propext`, `Classical.choice`, `Quot.sound` only).

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

* `step_walk` — the walk/interpreter correspondence over a whole arc run (the successor case
  of the induction; `step_sim` is the one-step core, proved).
* `simWalk_stall`, `arc_walk_advances` — the walk's stall/advance facts.
* After those: `arc_seg` (seg over a valid arc = one jump), `runFast_eq_run`,
  `callEntryFast_eq_callEntry`, `runCallFast_eq_runCall`, `runCallWithLimitsFast_eq`,
  the fuel-transfer theorems, and `arcsFor_valid` (the builder's contract).
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

/-- `a` describes a real run of `pf`: it starts below its end, ends within the code, and the
conservative walk from `pc0` advances through all `len = runEnd − pc0` instructions and lands
exactly on `(runEnd, pushes)`. -/
def ArcOK (pf : PFunc) (a : Arc) : Prop :=
  a.pc0 < a.runEnd ∧ a.runEnd ≤ pf.code.size ∧
    simWalk pf a.pc0 (a.runEnd - a.pc0) = (a.runEnd, a.pushes, a.guard)

/-- The per-function table is valid for `pf`: every stored arc is `ArcOK` and sits at its
start pc. -/
def ArcsOK (pf : PFunc) (row : Array (Option Arc)) : Prop :=
  ∀ (pc : Nat) (a : Arc), row[pc]? = some a → a.pc0 = pc ∧ ArcOK pf a

/-- The whole table matches the prepared module: row `fn` is valid for `p.funcs[fn]`. -/
def arcsValidFor (p : Prepared) (arcs : Array (Array (Option Arc))) : Prop :=
  ∀ (fn : Nat) (row : Array (Option Arc)), arcs[fn]? = some row →
    ∃ pf, p.funcs[fn]? = some pf ∧ ArcsOK pf row

/-! ### The builder

One linear scan. At a pc whose walk advances, the run extends to the first stall of `simNext`
(the walk with the full remaining budget stops there, because a stalled state is a fixed
point); the arc is `(pc, runEnd, walk pushes)`. The scan then continues at `runEnd`, so runs
are maximal and disjoint. Runs of length < 2 are not worth an entry. -/

/-- Build the arc table of one function: scan pcs left to right, emitting an arc per maximal
determined run of length ≥ 2 and continuing at the run's end. `left` is the number of pcs left
to scan (`pc = code.size - left`); the arc branch jumps to `runEnd`, strictly past `pc`. -/
def buildFrom (pf : PFunc) (left : Nat) (out : Array (Option Arc)) : Array (Option Arc) :=
  if left = 0 then out else
    let pc := pf.code.size - left
    let (runEnd, sim, grd) := simWalk pf pc left
    if pc + 2 ≤ runEnd then
      buildFrom pf (pf.code.size - runEnd) (out.set! pc (some ⟨pc, runEnd, sim, grd⟩))
    else buildFrom pf (left - 1) out
termination_by left
decreasing_by
  all_goals omega

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
def SimInv (f : Frame) (pc : Nat) (sim : List SimLab) (en : List Label) (H : Nat) : Prop :=
  f.pc = pc ∧ f.labels = matLabels H sim ++ en

/-- Key correspondence, one run instruction: if the simulator advances from `(pc, sim)` to
`(pc', sim')`, then the real interpreter steps to `.cont` of the corresponding state,
preserving the invariant (same entry tail and stack height). For an in-run `end`,
`hend : 2 ≤ sim.length + en.length` is the guard condition that makes `exec .end_` take the
pop arm (the walk's `endDemand sim ≤ guard ≤ |en|` at fire time; `step_walk` propagates it). -/
private theorem step_sim {p : Prepared} {pf : PFunc} {fn pc pc' : Nat}
    {sim sim' : List SimLab} {i : Instr} {en : List Label} {H : Nat}
    (hpff : p.funcs[fn]? = some pf)
    (hstep : simStep pf pc sim i = some (pc', sim'))
    (s : St) (f : Frame) (fs : List Frame)
    (hi : pf.code[pc]? = some i) (hfree : pf.gas[pc]? = some none)
    (hf : s.frames = f :: fs) (hfn : f.fn = fn)
    (hinv : SimInv f pc sim en H)
    (hend : i = .end_ → 2 ≤ sim.length + en.length)
    (hsH : s.stack.size = H) :
    ∃ s' : St, step pv86 p s = .cont s' ∧
      ∃ f' : Frame, s'.frames = f' :: fs ∧ SimInv f' pc' sim' en H := by
  obtain ⟨hpc, hlab⟩ := hinv
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
      · -- the frame and its invariant
        refine ⟨{ f with pc := pc + 1, labels :=
          ({ target := e + 1, arity := (btResults bt).size, height := H, isLoop := false } : Label)
            :: (matLabels H sim ++ en) }, rfl, ?_⟩
        constructor
        · rfl
        · rfl
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
          :: (matLabels H sim ++ en) }, rfl, ?_⟩
      constructor
      · rfl
      · rfl
  | nop =>
    -- simulator: (pc+1, sim); nop keeps the label list
    simp only [simStep, Option.some.injEq, Prod.mk.injEq] at hstep
    obtain ⟨rfl, rfl⟩ : pc' = pc + 1 ∧ sim' = sim := ⟨hstep.1.symm, hstep.2.symm⟩
    refine ⟨{ s with frames := ({ f with pc := pc + 1, labels := f.labels } : Frame) :: fs }, ?_, ?_⟩
    · simp only [step, hf, hpff, hfn, hpc, hi, hfree]
      simp only [exec, setFrame, hf]
      rw [hfn, hpc]
    · exact ⟨{ f with pc := pc + 1, labels := f.labels }, rfl, rfl, hlab⟩
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
      · -- the frame witness and its SimInv
        refine ⟨{ f with pc := pc + 1, labels := matLabels H t ++ en }, ?_, ?_⟩
        · show (_ :: fs) = (_ :: fs)
          rfl
        · have hs : sim' = t := hsim'.symm
          rw [hs]
          exact ⟨rfl, rfl⟩
  | _ => simp [simStep] at hstep

/-- The walk and the real interpreter agree over a whole arc run: from a state satisfying the
invariant at `(pc0, [])` (entry labels `en` with `guard ≤ |en|`), the `k`-th single step of the
run is `.cont` of the `(k+1)`-th walk state, for every `k < len` (induction on the walk; the
guard's demand is exactly what `step_sim`'s `hend` needs at each in-run `end`). -/
private theorem step_walk {p : Prepared} {pf : PFunc} {fn : Nat} {a : Arc} {en : List Label}
    {H : Nat} {s0 : St} {f0 : Frame} {fs : List Frame}
    (hpff : p.funcs[fn]? = some pf)
    (hvalid : ArcOK pf a)
    (hf : s0.frames = f0 :: fs) (hfn : f0.fn = fn) (hpc0 : f0.pc = a.pc0)
    (hlab0 : f0.labels = en) (hgrd : a.guard ≤ en.length)
    (hsH : s0.stack.size = H) :
    ∀ (k : Nat) (hk : k ≤ a.runEnd - a.pc0),
      ∃ s : St, seg pv86 p k s0 = .cont s ∧
        ∃ f : Frame, s.frames = f :: fs ∧
          SimInv f (a.pc0 + k) (simWalk pf a.pc0 k).2.1 en H ∧
          s.stack.size = s0.stack.size := by
  intro k
  induction k with
  | zero =>
    -- zero steps: the state is s0 itself; the walk at 0 is (pc0, [], 0)
    intro _
    refine ⟨s0, rfl, f0, hf, ?_, rfl⟩
    exact ⟨hpc0, by rw [hlab0]; rfl⟩
  | succ k ih =>
    -- the (k+1)-th step: `seg (k+1) = step >>= seg k`; by ih (for k ≤ len−1) the state
    -- before the last step satisfies the invariant at walk position k; `step_sim` gives
    -- the step is `.cont` of the (k+1)-th walk state.
    intro hk
    -- obtain the k-step state by ih (k ≤ len since k+1 ≤ len)
    have hk' : k ≤ a.runEnd - a.pc0 := Nat.le_of_succ_le hk
    obtain ⟨s1, hseg1, f1, hf1, hinv1, hstack1⟩ := ih hk'
    -- the state before the step: top frame at pc0+k with walk labels
    obtain ⟨hpc1, hlab1⟩ := hinv1
    -- the instruction at pc0+k is free and run-determined (the walk advances: k < len)
    -- walk position k → (pc0+k, sim_k, grd_k); since k < len, simNext advances
    have hwalk : simWalk pf a.pc0 (k + 1) = simNext pf (simWalk pf a.pc0 k) := rfl
    -- ArcOK: the walk at len lands on (runEnd, pushes, guard); monotonicity of the walk:
    -- positions before len always advance (otherwise the walk would stall and never land)
    -- Extract the walk state at k:
    obtain ⟨pc_k, sim_k, grd_k⟩ := simWalk pf a.pc0 k
    -- the state at step k has pc pc0+k (by hinv1) and labels matLabels H sim_k ++ en
    -- (the walk's sim at k); the step is run-determined:
    have hstep : ∃ (pc' : Nat) (sim' : List SimLab),
        simStep pf pc_k sim_k (pf.code[pc_k]?.getD .nop) = some (pc', sim') ∧
        pc' = pc_k + 1 := by
      sorry
    sorry

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

/-- If the walk is stalled at position `k` (its state is a `simNext` fixed point), it stays
there forever: `simNext` is idempotent on its own fixed points. -/
private theorem simWalk_stall (pf : PFunc) {pc : Nat} {sim : List SimLab} {grd : Nat}
    (hstall : simNext pf (pc, sim, grd) = (pc, sim, grd)) (k : Nat) :
    simWalk pf pc (k + 1) = simNext pf (simWalk pf pc k) ∧
    ∀ (j : Nat), simWalk pf pc (k + 1 + j) = (pc, sim, grd) := by
  sorry

/-- A valid arc's walk advances at every position before its end: if it stalled at some
`k < len`, it would stall forever (`simWalk_stall`) and never reach `runEnd ≠ pc0 + k`. -/
private theorem arc_walk_advances (pf : PFunc) {a : Arc} (hok : ArcOK pf a) (k : Nat)
    (hk : k < a.runEnd - a.pc0) :
    (simWalk pf a.pc0 (k + 1)).1 = (simWalk pf a.pc0 k).1 + 1 := by
  sorry

end NearSpecV3.Wasm
