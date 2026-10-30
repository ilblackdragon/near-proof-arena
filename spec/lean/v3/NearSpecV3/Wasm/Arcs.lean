import NearSpecV3.Wasm.Fuel
import NearSpecV3.Wasm.Segment

/-!
# Arcs: bulk execution of zero-fee control runs (W02 evaluation time)

`wasmFuel` (`Wasm/Fuel.lean`) made the step budget non-binding for valid runs and moved the
binding limit to *evaluation time*: a loop of `k` zero-fee `block`/`end` pairs and one `br`
executes `2k + 2` interpreter steps per `2 · regular_op_cost` of gas, so the worst contract at
PV86 (`k = 4,999`) spends ~5.7·10⁹ steps per Tgas (`docs/evidence/lean-chunk-completion/
fuel-termination/README.md` §4). This module removes that cost **without changing a single step
of the semantics**:

* `run`, `callEntry`, `runCall`, `runCallWithLimits` and `outcome` (`Wasm/Exec.lean`) stay the
  definitions. Every relation (`RelD3`, `Tier.rel`), kernel non-vacuity theorem and existing proof
  is about them and is untouched.
* `runFast` executes a precomputed **arc** — a maximal run of free `block`/`loop`/`end`/`nop`
  instructions, optionally fused with the `br` that ends it — as one jump, and is otherwise
  `step` by `step`. An arc consumes exactly the fuel of the single steps it replaces.
* `runFast_eq_run`: `runFast = run` for **every** fuel, configuration and state, given a valid arc
  table; `arcsOf_valid`: the builder's table is valid. So `callEntry = callEntryArcs`,
  `runCall = runCallFast`, `runCallWithLimits = runCallWithLimitsFast` and
  `outcome = outcomeFast` hold unconditionally, and they are registered as `@[csimp]` lemmas.
  A `@[csimp]` lemma rewrites references in code compiled *after* it is in scope, so the
  compiled callers import this module: `Wasm/ChunkStorage` and `D3/FunctionCall` (and through it
  `Successor/StorageExecution`, `Logged/D3L` and the successor checker), and `MainRuntime`.
  The kernel and every proof only ever see the original definitions. `run` itself has no
  `@[csimp]` replacement (the table would be rebuilt on every `run` call); compiled code that
  calls `run` directly, and the logged mirror `Logged/WasmRun.runL` (its own step loop), still
  single-step.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only (`#print axioms` at the end).

## Why a run is a jump

`block`, `loop`, `end` and `nop` never read or write the value stack, locals, globals, memory,
gas or host state; when free (gas-table entry `none`) a step of one of them changes only the top
frame's `pc` (to `pc + 1`) and its label list. Read back to front, a run is a label-list
transformer: drop `pops` entry labels, push `pushes` labels whose `height` is the (constant)
value-stack size. The only runtime condition is the **guard** `guard ≤ labels.length`: it makes
every in-run `end` take `exec .end_`'s pop arm (the singleton/empty arms would return from the
function) and, for a fused `br l`, makes `doBr` take the branch arm (not `doReturn`).

The builder computes, in one backward pass per function, the arc of **every** pc of a run (the
arc of `pc` is the arc of `pc + 1` extended by the instruction at `pc`, `extend`): a branch that
lands in the middle of a run still finds an arc. Pushes are stored bottom-first so that the
extension is O(1) and arcs of one run share their push lists.

## Fused `br`

When the run ends at `br l`, the arc also executes the branch. A loop back-edge discards the
labels the run pushed, so the fused arc never materializes them (`brFast`): the per-iteration
cost of `blocks4999` is O(1) instead of O(run length). A charge point on the `br` keeps the real
`charge` call; if it does not continue (out of gas, overflow) the arc falls back to `step` on
the exact single-stepped state, so the failure result is the single-stepped one by definition.

## Cost and limits

The table is built once per call (`runCallFast`), one backward pass per function: O(code size),
≈ 5 ms for a 10,000-instruction function. `runFast` looks the table up only at a free run
instruction, so a step of any other instruction costs what `step` costs.

Label lists are `List Label`, so an arc that *keeps* `m` pushed labels still materializes them
(O(m)), and a `br_if`/`br_table` is never fused (it reads the value stack). A contract that
pushes many labels in one run and pops them in another, separated by a charged instruction,
still costs O(`max_blocks_per_function`) list cells per iteration: ~3× faster than
single-stepping, not O(1). Measurements: `docs/evidence/lean-chunk-completion/eval-time/`.
-/

namespace NearSpecV3.Wasm

/-! ## Run cores -/

/-- A label pushed by a run, without its height: `(target, arity, isLoop)`. -/
abbrev SimLab := Nat × Nat × Bool

/-- Materialize a pushed label at value-stack height `H`. -/
def SimLab.mk (H : Nat) : SimLab → Label
  | (t, ar, lp) => { target := t, arity := ar, height := H, isLoop := lp }

/-- Materialize bottom-first pushes onto the label list `L` (the last element ends on top). -/
def matOnto (H : Nat) : List SimLab → List Label → List Label
  | [], L => L
  | x :: r, L => matOnto H r (SimLab.mk H x :: L)

/-- The net effect of a run of `len` free control instructions: drop `pops` entry labels, then
push `pushes` (bottom-first, `nPush` of them). `grd` is the entry label depth the run needs. -/
structure Core where
  len : Nat
  pushes : List SimLab
  nPush : Nat
  pops : Nat
  grd : Nat
  deriving Inhabited, Repr

def Core.empty : Core := ⟨0, [], 0, 0, 0⟩

/-- Prepend an instruction that pushes `x` to the run `c`. -/
def Core.push (c : Core) (x : SimLab) : Core :=
  match c.pops with
  | 0 => { c with len := c.len + 1, pushes := x :: c.pushes, nPush := c.nPush + 1, grd := c.grd - 1 }
  | k + 1 => { c with len := c.len + 1, pops := k, grd := c.grd - 1 }

/-- Prepend the instruction at `pc` to the run `c` that starts at `pc + 1`; `none` unless that
instruction is a free `block` (with an `endOf` entry), `loop`, `nop` or `end`. -/
def extend (pf : PFunc) (pc : Nat) (c : Core) : Option Core :=
  match pf.gas[pc]? with
  | some none =>
    match pf.code[pc]? with
    | some (.block bt) =>
      match pf.endOf[pc]? with
      | some e => some (c.push (e + 1, (btResults bt).size, false))
      | none => none
    | some (.loop _) => some (c.push (pc + 1, 0, true))
    | some .nop => some { c with len := c.len + 1 }
    | some .end_ => some { c with len := c.len + 1, pops := c.pops + 1, grd := Nat.max 2 (c.grd + 1) }
    | _ => none
  | _ => none

/-- The run of length `k` from `pc`, if the `k` instructions at `pc …` are all run instructions. -/
def runFrom (pf : PFunc) (pc : Nat) : Nat → Option Core
  | 0 => some Core.empty
  | k + 1 => (runFrom pf (pc + 1) k).bind (extend pf pc)

/-! ## Arcs and their validity -/

/-- An arc: a run, the guard to fire it, and the fused `br l` at the run's end with its gas-table
entry (if the run ends at a `br`). -/
structure Arc where
  core : Core
  guard : Nat
  br : Option (Nat × Option (IK × Fee))
  deriving Inhabited

/-- `a` is a correct arc of `pf` at `pc`. -/
def ArcOK (pf : PFunc) (pc : Nat) (a : Arc) : Prop :=
  0 < a.core.len ∧ runFrom pf pc a.core.len = some a.core ∧ a.core.grd ≤ a.guard ∧
    match a.br with
    | none => True
    | some (l, g) => pf.code[pc + a.core.len]? = some (.br l) ∧ pf.gas[pc + a.core.len]? = some g ∧
        a.core.pops + l + 2 - a.core.nPush ≤ a.guard

/-- A table whose row `fn` holds correct arcs of `p.funcs[fn]`. -/
def ArcsValid (p : Prepared) (arcs : Array (Array (Option Arc))) : Prop :=
  ∀ (fn : Nat) (row : Array (Option Arc)), arcs[fn]? = some row →
    ∃ pf, p.funcs[fn]? = some pf ∧ ∀ (pc : Nat) (a : Arc), row[pc]? = some (some a) → ArcOK pf pc a

/-! ## The builder -/

/-- Shortest plain arc worth a table entry. Any value is correct. Measured on the `mixed` probe
(30 Tgas, min of 3, loaded host; `docs/evidence/lean-chunk-completion/eval-time/`): 2 → 2,562 ms,
4 → 2,558, 8 → 2,741, no plain arcs → 2,704, single-step 2,543–2,623. Short arcs cost nothing
measurable (the cost is the table lookup, which happens only at run instructions), so the
shortest useful length is taken. -/
def arcMinLen : Nat := 2

/-- Shortest fused (`br`-ending) arc worth an entry. Any value ≥ 1 is correct. -/
def arcMinLenBr : Nat := 1

/-- The arc stored at `pc` for the run `c` that starts there. -/
def arcEntry (pf : PFunc) (pc : Nat) (c : Core) : Option Arc :=
  let e := pc + c.len
  let br : Option (Nat × Option (IK × Fee)) :=
    match pf.code[e]? with
    | some (.br l) => (pf.gas[e]?).map (fun g => (l, g))
    | _ => none
  match br with
  | some (l, g) =>
    if arcMinLenBr ≤ c.len ∧ 0 < c.len then
      some ⟨c, Nat.max c.grd (c.pops + l + 2 - c.nPush), some (l, g)⟩
    else none
  | none => if arcMinLen ≤ c.len ∧ 0 < c.len then some ⟨c, c.grd, none⟩ else none

/-- Backward pass: `buildGo pf k cur acc` processes pcs `k-1, …, 0`; `cur` is the maximal run
from `k`, `acc` the entries of pcs `k, k+1, …`. -/
def buildGo (pf : PFunc) : Nat → Core → List (Option Arc) → List (Option Arc)
  | 0, _, acc => acc
  | k + 1, cur, acc =>
    let c := (extend pf k cur).getD Core.empty
    buildGo pf k c (arcEntry pf k c :: acc)

/-- The arc table of one function: one slot per pc. -/
def arcsFor (pf : PFunc) : Array (Option Arc) :=
  (buildGo pf pf.code.size Core.empty []).toArray

/-- The arc table of a prepared module. -/
def arcsOf (p : Prepared) : Array (Array (Option Arc)) := p.funcs.map arcsFor

/-! ## The fast interpreter -/

/-- `n ≤ l.length`, in O(n). -/
def lenGe {α : Type} : Nat → List α → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | n + 1, _ :: t => lenGe n t

/-- The instructions a run consists of (arcs start only at these). -/
def isRunInstr : Instr → Bool
  | .block _ | .loop _ | .end_ | .nop => true
  | _ => false

/-- The arc stored for the top frame `f` at a run instruction `i`. Only run instructions look the
table up, so every other step pays one constructor test; `getD`, not `[·]?`, so a miss allocates
no `Option` cell. -/
def arcAt (arcs : Array (Array (Option Arc))) (f : Frame) (i : Instr) : Option Arc :=
  if isRunInstr i then (arcs.getD f.fn #[]).getD f.pc none else none

/-- The state after the arc's run: what `len` single steps produce. -/
def applyArc (s : St) (f : Frame) (a : Arc) : St :=
  setFrame s { f with pc := f.pc + a.core.len,
                      labels := matOnto s.stack.size a.core.pushes (f.labels.drop a.core.pops) }

/-- The end of `doBr` once the target label and the remaining labels are known. -/
def finishBr (s : St) (f : Frame) (lab : Label) (labels : List Label) : Res :=
  let vals := s.stack.extract (s.stack.size - lab.arity) s.stack.size
  let s := { s with stack := s.stack.extract 0 lab.height ++ vals }
  .cont (setFrame s { f with pc := lab.target, labels := labels })

/-- The fused `br l` after the arc's run, computed from the entry frame `f` without materializing
the pushed labels the branch discards. -/
def brFast (s : St) (f : Frame) (a : Arc) (l : Nat) : Res :=
  let H := s.stack.size
  let c := a.core
  if l < c.nPush then
    let lab := SimLab.mk H (c.pushes.getD (c.nPush - 1 - l) default)
    finishBr s f lab
      (matOnto H (c.pushes.take (c.nPush - (if lab.isLoop then l else l + 1))) (f.labels.drop c.pops))
  else
    match f.labels[c.pops + (l - c.nPush)]? with
    | some lab => finishBr s f lab (f.labels.drop (c.pops + (if lab.isLoop then l else l + 1) - c.nPush))
    | none => .unmodeled "invariant: branch to an unknown label"

/-- The arc's run followed by its fused `br l` (gas entry `g`). -/
def fuseBr (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (a : Arc) (l : Nat)
    (g : Option (IK × Fee)) : Res :=
  match g with
  | none => brFast s f a l
  | some (k, fee) =>
    match charge s fee (if k = .linear then topCount s else 0) with
    | .cont s' => brFast s' f a l
    | _ => step cfg p (applyArc s f a)

/-- `run`, with arcs. The body is `step`'s dispatch (same order, same results) with one extra
branch: at a free run instruction whose arc's guard holds, the whole arc executes and consumes the
fuel of the steps it replaces. -/
def runFast (cfg : NearCfg) (p : Prepared) (arcs : Array (Array (Option Arc))) : Nat → St → Res
  | 0, _ => .unmodeled "fuel exhausted"
  | n + 1, s =>
    match s.frames with
    | [] => .fin s
    | f :: _ =>
      match p.funcs[f.fn]? with
      | none => .unmodeled "bad frame"
      | some pf =>
        match pf.code[f.pc]? with
        | none => .unmodeled "pc out of range"
        | some i =>
          match pf.gas[f.pc]? with
          | none => .unmodeled "invariant: gas table shorter than the code"
          | some none =>
            match arcAt arcs f i with
            | some a =>
              if lenGe a.guard f.labels then
                match a.br with
                | some (l, g) =>
                  if a.core.len ≤ n then
                    match fuseBr cfg p s f a l g with
                    | .cont s' => runFast cfg p arcs (n - a.core.len) s'
                    | r => r
                  else
                    match exec cfg p s f pf i with
                    | .cont s' => runFast cfg p arcs n s'
                    | r => r
                | none =>
                  if h : 0 < a.core.len ∧ a.core.len ≤ n + 1 then
                    runFast cfg p arcs (n + 1 - a.core.len) (applyArc s f a)
                  else
                    match exec cfg p s f pf i with
                    | .cont s' => runFast cfg p arcs n s'
                    | r => r
              else
                match exec cfg p s f pf i with
                | .cont s' => runFast cfg p arcs n s'
                | r => r
            | none =>
              match exec cfg p s f pf i with
              | .cont s' => runFast cfg p arcs n s'
              | r => r
          | some (some (k, fee)) =>
            match charge s fee (if k = .linear then topCount s else 0) with
            | .cont s1 =>
              match exec cfg p s1 f pf i with
              | .cont s' => runFast cfg p arcs n s'
              | r => r
            | r => r
termination_by n => n
decreasing_by all_goals omega

/-! ## Proofs: a run is its single steps -/

theorem setFrame_stack (s : St) (F : Frame) : (setFrame s F).stack = s.stack := by
  unfold setFrame; split <;> rfl

theorem setFrame_setFrame {s : St} {f : Frame} {fs : List Frame} (hf : s.frames = f :: fs)
    (F1 F2 : Frame) : setFrame (setFrame s F1) F2 = setFrame s F2 := by
  simp [setFrame, hf]

theorem setFrame_self {s : St} {f : Frame} {fs : List Frame} (hf : s.frames = f :: fs) :
    setFrame s f = s := by
  cases s; simp_all [setFrame]

theorem lenGe_iff {α : Type} : ∀ (n : Nat) (l : List α), lenGe n l = true ↔ n ≤ l.length
  | 0, _ => by simp [lenGe]
  | _ + 1, [] => by simp [lenGe]
  | n + 1, _ :: t => by simp [lenGe, lenGe_iff n t]

theorem matOnto_eq (H : Nat) : ∀ (r : List SimLab) (L : List Label),
    matOnto H r L = (r.map (SimLab.mk H)).reverse ++ L
  | [], L => rfl
  | x :: r, L => by simp [matOnto, matOnto_eq H r]

theorem runFrom_len (pf : PFunc) : ∀ (k pc : Nat) (c : Core), runFrom pf pc k = some c →
    c.len = k ∧ c.nPush = c.pushes.length
  | 0, pc, c, h => by simp [runFrom, Core.empty] at h; subst h; simp
  | k + 1, pc, c, h => by
    simp only [runFrom, Option.bind_eq_some_iff] at h
    obtain ⟨c', h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := runFrom_len pf k (pc + 1) c' h1
    unfold extend at h2
    repeat' split at h2
    all_goals first
      | (cases h2; done)
      | (simp only [Option.some.injEq] at h2; subst h2
         first
           | (simp [ih1, ih2])
           | (unfold Core.push; split <;> simp_all))

/-- One run instruction: `step` is `.cont` of the frame with `pc + 1` and the instruction's label
effect, and the label effect composes with the rest of the run. -/
theorem extend_step (cfg : NearCfg) {p : Prepared} {pf : PFunc} {pc : Nat} {c c' : Core}
    (hext : extend pf pc c' = some c)
    {s : St} {f : Frame} {fs : List Frame} (hf : s.frames = f :: fs)
    (hpf : p.funcs[f.fn]? = some pf) (hpc : f.pc = pc) (hg : c.grd ≤ f.labels.length) :
    ∃ L1, step cfg p s = .cont (setFrame s { f with pc := pc + 1, labels := L1 }) ∧
      c'.grd ≤ L1.length ∧
      matOnto s.stack.size c'.pushes (L1.drop c'.pops) =
        matOnto s.stack.size c.pushes (f.labels.drop c.pops) := by
  subst hpc
  unfold extend at hext
  split at hext
  · rename_i hgas
    split at hext
    · rename_i bt hcode
      split at hext
      · rename_i e he
        simp only [Option.some.injEq] at hext
        subst hext
        refine ⟨SimLab.mk s.stack.size (e + 1, (btResults bt).size, false) :: f.labels, ?_, ?_, ?_⟩
        · simp only [step, hf, hpf, hcode, hgas, exec, he]
          rfl
        · unfold Core.push at hg; split at hg <;> simp at hg ⊢ <;> omega
        · unfold Core.push; split <;> simp_all [matOnto]
      · cases hext
    · rename_i bt hcode
      simp only [Option.some.injEq] at hext
      subst hext
      refine ⟨SimLab.mk s.stack.size (f.pc + 1, 0, true) :: f.labels, ?_, ?_, ?_⟩
      · simp only [step, hf, hpf, hcode, hgas, exec]
        try rfl
      · unfold Core.push at hg; split at hg <;> simp at hg ⊢ <;> omega
      · unfold Core.push; split <;> simp_all [matOnto]
    · rename_i hcode
      simp only [Option.some.injEq] at hext
      subst hext
      refine ⟨f.labels, ?_, ?_, rfl⟩
      · simp only [step, hf, hpf, hcode, hgas, exec]
        try rfl
      · simpa using hg
    · rename_i hcode
      simp only [Option.some.injEq] at hext
      subst hext
      simp only at hg
      have h2 : 2 ≤ f.labels.length := Nat.le_trans (Nat.le_max_left _ _) hg
      have h3 : c'.grd + 1 ≤ f.labels.length := Nat.le_trans (Nat.le_max_right _ _) hg
      match hL : f.labels with
      | a :: b :: rest =>
        rw [hL] at h3
        refine ⟨b :: rest, ?_, ?_, ?_⟩
        · simp only [step, hf, hpf, hcode, hgas, exec, hL]
          try rfl
        · simp at h3 ⊢; omega
        · simp
      | [a] => rw [hL] at h2; simp at h2
      | [] => rw [hL] at h2; simp at h2
    · cases hext
  · cases hext

/-- A valid run executes as its `k` single steps. -/
theorem seg_runFrom (cfg : NearCfg) {p : Prepared} {pf : PFunc} :
    ∀ (k : Nat) {pc : Nat} {c : Core}, runFrom pf pc k = some c →
    ∀ {s : St} {f : Frame} {fs : List Frame}, s.frames = f :: fs → p.funcs[f.fn]? = some pf →
      f.pc = pc → c.grd ≤ f.labels.length →
      seg cfg p k s = .cont (setFrame s
        { f with pc := pc + k, labels := matOnto s.stack.size c.pushes (f.labels.drop c.pops) })
  | 0, pc, c, h, s, f, fs, hf, _, hpc, _ => by
    simp [runFrom, Core.empty] at h
    subst h; subst hpc
    simp only [seg, Nat.add_zero, matOnto, List.drop_zero]
    exact (congrArg Res.cont (setFrame_self hf)).symm
  | k + 1, pc, c, h, s, f, fs, hf, hpf, hpc, hg => by
    simp only [runFrom, Option.bind_eq_some_iff] at h
    obtain ⟨c', h1, h2⟩ := h
    obtain ⟨L1, hstep, hg', hmat⟩ := extend_step cfg h2 hf hpf hpc hg
    have ih := seg_runFrom cfg k h1 (s := setFrame s { f with pc := pc + 1, labels := L1 })
      (f := { f with pc := pc + 1, labels := L1 }) (fs := fs) (setFrame_frames hf _) hpf rfl hg'
    simp only [seg, hstep, Res.cont_bind]
    rw [ih, setFrame_setFrame hf, setFrame_stack, hmat, show pc + 1 + k = pc + (k + 1) by omega]

/-! ## Proofs: the fused `br` -/

theorem mat_get_lt (H : Nat) (r : List SimLab) (D : List Label) {l : Nat} (hl : l < r.length) :
    (matOnto H r D)[l]? = some (SimLab.mk H (r.getD (r.length - 1 - l) default)) := by
  rw [matOnto_eq, List.getElem?_append_left (by simpa using hl),
    List.getElem?_reverse (by simpa using hl), List.getElem?_map, List.length_map,
    List.getElem?_eq_getElem (by omega), List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega)]
  rfl

theorem mat_drop_le (H : Nat) (r : List SimLab) (D : List Label) {k : Nat} (hk : k ≤ r.length) :
    (matOnto H r D).drop k = matOnto H (r.take (r.length - k)) D := by
  rw [matOnto_eq, matOnto_eq, List.drop_append_of_le_length (by simpa using hk), List.drop_reverse,
    List.length_map, List.map_take]

theorem mat_get_ge (H : Nat) (r : List SimLab) (L : List Label) (pops : Nat) {l : Nat}
    (hl : r.length ≤ l) : (matOnto H r (L.drop pops))[l]? = L[pops + (l - r.length)]? := by
  rw [matOnto_eq, List.getElem?_append_right (by simpa using hl), List.getElem?_drop]
  simp

theorem mat_drop_ge (H : Nat) (r : List SimLab) (L : List Label) (pops : Nat) {k : Nat}
    (hk : r.length ≤ k) : (matOnto H r (L.drop pops)).drop k = L.drop (pops + k - r.length) := by
  rw [matOnto_eq, List.drop_append, List.drop_drop]
  have : (r.map (SimLab.mk H)).reverse.drop k = [] := by
    apply List.drop_eq_nil_of_le; simpa using hk
  rw [this, List.nil_append]
  simp only [List.length_reverse, List.length_map]
  congr 1
  omega

theorem mat_length (H : Nat) (r : List SimLab) (D : List Label) :
    (matOnto H r D).length = r.length + D.length := by
  simp [matOnto_eq]

/-- The fused branch computes `doBr` on the state after the run. -/
theorem brFast_eq (p : Prepared) (a : Arc) (l : Nat) {t : St} {f : Frame} {fs : List Frame}
    (hf : t.frames = f :: fs) (hn : a.core.nPush = a.core.pushes.length)
    (hg : a.core.pops + l + 2 - a.core.nPush ≤ f.labels.length) (X : Nat) :
    doBr p (setFrame t
        { f with pc := X, labels := matOnto t.stack.size a.core.pushes (f.labels.drop a.core.pops) })
      { f with pc := X, labels := matOnto t.stack.size a.core.pushes (f.labels.drop a.core.pops) } l
    = brFast t f a l := by
  have hlen : ¬ (l + 1 ≥ (matOnto t.stack.size a.core.pushes (f.labels.drop a.core.pops)).length) := by
    rw [mat_length, List.length_drop]; omega
  unfold doBr brFast
  simp only
  simp only [hlen, ↓reduceIte]
  by_cases hl : l < a.core.nPush
  · simp only [hl, ↓reduceIte]; rw [mat_get_lt _ _ _ (by omega)]
    simp only [finishBr, hn]
    rw [hn] at hl
    generalize SimLab.mk t.stack.size (a.core.pushes.getD (a.core.pushes.length - 1 - l) default) = lab
    cases hlp : lab.isLoop <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;>
      rw [mat_drop_le _ _ _ (by omega), setFrame_stack] <;> simp [setFrame, hf]
  · simp only [hl, ↓reduceIte]; rw [mat_get_ge _ _ _ _ (by omega), hn]
    rw [hn] at hl
    cases hlab : f.labels[a.core.pops + (l - a.core.pushes.length)]? with
    | none => rfl
    | some lab =>
      simp only [finishBr]
      cases hlp : lab.isLoop <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;>
        rw [mat_drop_ge _ _ _ _ (by omega), setFrame_stack] <;> simp [setFrame, hf]

theorem setFrame_gas (s : St) (F : Frame) : (setFrame s F).gas = s.gas := by
  unfold setFrame; split <;> rfl

theorem charge_cont_stack (s : St) (fee : Fee) (c : Nat) (s' : St)
    (h : charge s fee c = .cont s') : s'.stack = s.stack := by
  simp only [charge] at h
  by_cases h1 : c * fee.l + fee.c ≥ u64Bound
  · simp only [h1, ite_true] at h
    repeat' split at h
    all_goals cases h
  · simp only [h1, ite_false] at h
    by_cases h2 : c * fee.l + fee.c > s.gas.g
    · simp only [h2, ite_true] at h
      repeat' split at h
      all_goals cases h
    · simp only [h2, ite_false] at h
      cases h; rfl

/-- Charging only touches gas: it commutes with replacing the top frame. -/
theorem charge_setFrame {s s' : St} {fee : Fee} {c : Nat} (h : charge s fee c = .cont s')
    (F : Frame) : charge (setFrame s F) fee c = .cont (setFrame s' F) := by
  simp only [charge] at h ⊢
  rw [setFrame_gas]
  by_cases h1 : c * fee.l + fee.c ≥ u64Bound
  · simp only [h1, ite_true] at h
    repeat' split at h
    all_goals cases h
  · simp only [h1, ite_false] at h ⊢
    by_cases h2 : c * fee.l + fee.c > s.gas.g
    · simp only [h2, ite_true] at h
      repeat' split at h
      all_goals cases h
    · simp only [h2, ite_false] at h ⊢
      cases h
      cases hs : s.frames <;> simp [setFrame, hs]

theorem topCount_setFrame (s : St) (F : Frame) : topCount (setFrame s F) = topCount s := by
  unfold topCount; rw [setFrame_stack]

/-- The fused arc is the run followed by one `step` of its `br`. -/
theorem fuseBr_eq (cfg : NearCfg) {p : Prepared} {pf : PFunc} {pc : Nat} {a : Arc} {l : Nat}
    {g : Option (IK × Fee)} (hok : ArcOK pf pc a) (hbr : a.br = some (l, g))
    {s : St} {f : Frame} {fs : List Frame} (hf : s.frames = f :: fs)
    (hpf : p.funcs[f.fn]? = some pf) (hpc : f.pc = pc) (hguard : a.guard ≤ f.labels.length) :
    fuseBr cfg p s f a l g = step cfg p (applyArc s f a) := by
  obtain ⟨_, hrun, _, hb⟩ := hok
  rw [hbr] at hb
  obtain ⟨hcode, hgas, hdem⟩ := hb
  have hn := (runFrom_len pf _ pc _ hrun).2
  have hg : a.core.pops + l + 2 - a.core.nPush ≤ f.labels.length := Nat.le_trans hdem hguard
  subst hpc
  unfold applyArc
  simp only [step, setFrame_frames hf, hpf, hcode, hgas]
  unfold fuseBr
  cases g with
  | none => exact (brFast_eq p a l hf hn hg _).symm
  | some kf =>
    obtain ⟨k, fee⟩ := kf
    simp only [topCount_setFrame]
    cases hc : charge s fee (if k = .linear then topCount s else 0) with
    | cont s' =>
      simp only
      rw [charge_setFrame hc]
      simp only [exec]
      have hf' : s'.frames = f :: fs := (charge_cont_frames _ _ _ _ hc).trans hf
      have hst : s'.stack = s.stack := charge_cont_stack _ _ _ _ hc
      have := brFast_eq p a l hf' hn hg (f.pc + a.core.len)
      rw [hst] at this
      exact this.symm
    | fin _ => simp only [applyArc, step, setFrame_frames hf, hpf, hcode, hgas, topCount_setFrame]
    | abort _ _ => simp only [applyArc, step, setFrame_frames hf, hpf, hcode, hgas, topCount_setFrame]
    | unmodeled _ => simp only [applyArc, step, setFrame_frames hf, hpf, hcode, hgas, topCount_setFrame]

/-! ## Proofs: `runFast = run` -/

theorem arcAt_spec {arcs : Array (Array (Option Arc))} {f : Frame} {i : Instr} {a : Arc}
    (h : arcAt arcs f i = some a) :
    ∃ row, arcs[f.fn]? = some row ∧ row[f.pc]? = some (some a) := by
  unfold arcAt at h
  split at h
  · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?] at h
    cases hrow : arcs[f.fn]? with
    | none => rw [hrow] at h; simp at h
    | some row =>
      rw [hrow, Option.getD_some] at h
      cases hpc : row[f.pc]? with
      | none => rw [hpc] at h; simp at h
      | some e =>
        rw [hpc, Option.getD_some] at h
        exact ⟨row, rfl, by rw [hpc, h]⟩
  · cases h

/-- A valid arc's run is `seg` of its length. -/
theorem seg_arc (cfg : NearCfg) {p : Prepared} {pf : PFunc} {a : Arc} {s : St} {f : Frame}
    {fs : List Frame} (hok : ArcOK pf f.pc a) (hf : s.frames = f :: fs)
    (hpf : p.funcs[f.fn]? = some pf) (hguard : a.guard ≤ f.labels.length) :
    seg cfg p a.core.len s = .cont (applyArc s f a) := by
  obtain ⟨_, hrun, hgrd, _⟩ := hok
  exact seg_runFrom cfg a.core.len hrun hf hpf rfl (Nat.le_trans hgrd hguard)

theorem seg_one (cfg : NearCfg) (p : Prepared) (s : St) : seg cfg p 1 s = step cfg p s := by
  simp only [seg]
  exact Res.bind_cont _

/-- **`runFast` is `run`**, for every fuel and state, given a valid arc table. -/
theorem runFast_eq_run (cfg : NearCfg) (p : Prepared) (arcs : Array (Array (Option Arc)))
    (hv : ArcsValid p arcs) : ∀ (n : Nat) (s : St), runFast cfg p arcs n s = run cfg p n s := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro s
  cases n with
  | zero => rw [runFast, run]
  | succ n =>
    -- continuing after one step: the fast and the reference recursion agree
    have hK : ∀ r : Res, (match r with
        | .cont s' => runFast cfg p arcs n s'
        | r => r) = (match r with
        | .cont s' => run cfg p n s'
        | r => r) := by
      intro r
      cases r with
      | cont s' => exact ih n (by omega) s'
      | fin _ => rfl
      | abort _ _ => rfl
      | unmodeled _ => rfl
    rw [runFast, run]
    cases hfr : s.frames with
    | nil => simp only [step, hfr]
    | cons f fs =>
      simp only
      cases hpf : p.funcs[f.fn]? with
      | none => simp only [step, hfr, hpf]
      | some pf =>
        simp only
        cases hcode : pf.code[f.pc]? with
        | none => simp only [step, hfr, hpf, hcode]
        | some i =>
          simp only
          cases hgas : pf.gas[f.pc]? with
          | none => simp only [step, hfr, hpf, hcode, hgas]
          | some g =>
            cases g with
            | some kf =>
              obtain ⟨k, fee⟩ := kf
              simp only [step, hfr, hpf, hcode, hgas]
              cases charge s fee (if k = .linear then topCount s else 0) with
              | cont s1 => exact hK _
              | fin _ => rfl
              | abort _ _ => rfl
              | unmodeled _ => rfl
            | none =>
              have hst : step cfg p s = exec cfg p s f pf i := by
                simp only [step, hfr, hpf, hcode, hgas]
              simp only
              rw [hst]
              cases harc : arcAt arcs f i with
              | none => exact hK _
              | some a =>
                simp only
                by_cases hgd : lenGe a.guard f.labels = true
                · simp only [hgd, ↓reduceIte]
                  have hg := (lenGe_iff _ _).1 hgd
                  obtain ⟨row, hrow, ha⟩ := arcAt_spec harc
                  obtain ⟨pf', hpf', hrowok⟩ := hv _ _ hrow
                  rw [hpf] at hpf'
                  cases hpf'
                  have hok := hrowok _ _ ha
                  have hseg := seg_arc cfg hok hfr hpf hg
                  -- back to the reference recursion: `run (n+1) s` itself
                  rw [← hst, ← run]
                  cases hbr : a.br with
                  | some lg =>
                    obtain ⟨l, g⟩ := lg
                    simp only
                    by_cases hlen : a.core.len ≤ n
                    · simp only [hlen, ↓reduceIte]; rw [fuseBr_eq cfg hok hbr hfr hpf rfl hg]
                      have hrun : run cfg p (n + 1) s =
                          (seg cfg p (a.core.len + 1) s).bind (run cfg p (n - a.core.len)) := by
                        rw [← run_seg]; congr 1; omega
                      rw [hrun, seg_add, hseg, Res.cont_bind, seg_one]
                      cases step cfg p (applyArc s f a) with
                      | cont s' => exact ih _ (by omega) s'
                      | fin _ => rfl
                      | abort _ _ => rfl
                      | unmodeled _ => rfl
                    · simp only [hlen, ↓reduceIte]
                      rw [run, hst]; exact hK _
                  | none =>
                    simp only
                    by_cases hlen : 0 < a.core.len ∧ a.core.len ≤ n + 1
                    · simp only [hlen, ↓reduceDIte, and_self]; rw [ih _ (by omega)]
                      have hrun : run cfg p (n + 1) s =
                          (seg cfg p a.core.len s).bind (run cfg p (n + 1 - a.core.len)) := by
                        rw [← run_seg]; congr 1; omega
                      rw [hrun, hseg, Res.cont_bind]
                    · simp only [hlen, ↓reduceDIte]
                      rw [run, hst]; exact hK _
                · simp only [hgd, Bool.false_eq_true, ↓reduceIte]
                  exact hK _

/-! ## Proofs: the builder emits only valid arcs -/

theorem arcEntry_ok {pf : PFunc} {pc : Nat} {c : Core} (hrun : runFrom pf pc c.len = some c)
    {a : Arc} (h : arcEntry pf pc c = some a) : ArcOK pf pc a := by
  unfold arcEntry at h
  simp only at h
  split at h
  · rename_i l g hbr
    split at h
    · rename_i hlen
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨hlen.2, hrun, Nat.le_max_left _ _, ?_⟩
      simp only
      split at hbr
      · rename_i l' hcode
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hbr
        obtain ⟨g', hg', rfl, rfl⟩ := hbr
        exact ⟨hcode, hg', Nat.le_max_right _ _⟩
      · cases hbr
    · cases h
  · split at h
    · rename_i hlen
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hlen.2, hrun, Nat.le_refl _, trivial⟩
    · cases h

theorem buildGo_ok (pf : PFunc) : ∀ (k : Nat) (cur : Core) (acc : List (Option Arc)),
    runFrom pf k cur.len = some cur →
    (∀ (j : Nat) (a : Arc), acc[j]? = some (some a) → ArcOK pf (k + j) a) →
    ∀ (j : Nat) (a : Arc), (buildGo pf k cur acc)[j]? = some (some a) → ArcOK pf j a
  | 0, cur, acc, _, hacc => by
    intro j a h
    simp only [buildGo] at h
    simpa using hacc j a h
  | k + 1, cur, acc, hcur, hacc => by
    simp only [buildGo]
    have hc : runFrom pf k ((extend pf k cur).getD Core.empty).len =
        some ((extend pf k cur).getD Core.empty) := by
      cases he : extend pf k cur with
      | none => rfl
      | some c =>
        have h1 : runFrom pf k (cur.len + 1) = some c := by
          simp only [runFrom, hcur, Option.bind_some, he]
        have := (runFrom_len pf _ _ _ h1).1
        simp only [Option.getD_some]
        rw [this]; exact h1
    apply buildGo_ok pf k _ _ hc
    intro j a h
    cases j with
    | zero => exact arcEntry_ok hc (by simpa using h)
    | succ j =>
      have := hacc j a (by simpa using h)
      rwa [show k + 1 + j = k + (j + 1) by omega] at this

theorem arcsFor_ok (pf : PFunc) (pc : Nat) (a : Arc) (h : (arcsFor pf)[pc]? = some (some a)) :
    ArcOK pf pc a := by
  unfold arcsFor at h
  rw [List.getElem?_toArray] at h
  exact buildGo_ok pf _ Core.empty [] rfl (by simp) pc a h

/-- The module's own table is valid. -/
theorem arcsOf_valid (p : Prepared) : ArcsValid p (arcsOf p) := by
  intro fn row h
  unfold arcsOf at h
  rw [Array.getElem?_map] at h
  cases hpf : p.funcs[fn]? with
  | none => rw [hpf] at h; cases h
  | some pf =>
    rw [hpf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨pf, rfl, arcsFor_ok pf⟩

/-! ## Label memo: O(1) label work for loops that keep their labels

An arc that *keeps* labels (`pushpop`: push `m` labels, a charged group, pop them) and a branch
that is not fused (`br_if l` back-edge, `br_table`) cost O(label depth) per execution, because
labels are a `List Label` in `St`: the pushes are materialized, and `doBr` walks the list
(`length`, `[l]?`, `drop`). In a loop the label list at a given pc is usually the *same object*
every iteration (the run pushes onto, and the branch drops back to, the same tail). `runMemo`
caches, per pc, the label work of the last execution: the input label list, the value-stack height
(arcs) or branch depth (branches), and the result. A hit needs the input to be equal to the cached
one; `labsEq` decides that with a pointer-equality shortcut at every cell (`withPtrEq`, whose
contract is that the shortcut is taken only where the full comparison answers `true`), so a loop
that returns to the same list object hits in O(1), and anything else costs at most one comparison
walk. The memo is a fixed array of `memoSlots` slots (direct-mapped by `(fn, pc)`), so it retains a
bounded number of lists. Label work smaller than `memoMin` is recomputed, never memoized.

`doBr` itself is also replaced (`brInfo`) by an O(`l`) form: `l + 1 ≥ labels.length` is decided by
`lenGe` instead of `length`, so a shallow branch in a deeply nested function no longer walks all
labels.

Proved: `runMemo_eq_runFast` (given a valid memo, for every fuel and state), so with
`runFast_eq_run` the call layer below is still `run` exactly. -/

deriving instance DecidableEq for Label

/-- Label-list equality with a pointer-equality shortcut at every cell. -/
def labsEqS : (a b : List Label) → {r : Bool // r = true ↔ a = b}
  | [], [] => ⟨true, by simp⟩
  | [], _ :: _ => ⟨false, by simp⟩
  | _ :: _, [] => ⟨false, by simp⟩
  | x :: xs, y :: ys =>
    ⟨withPtrEq (x :: xs) (y :: ys) (fun _ => decide (x = y) && (labsEqS xs ys).1)
      (fun h => by
        simp only [List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [(labsEqS xs xs).2]),
     by simp only [withPtrEq, Bool.and_eq_true, decide_eq_true_eq, (labsEqS xs ys).2,
          List.cons.injEq]⟩

@[inline] def labsEq (a b : List Label) : Bool := (labsEqS a b).1

theorem labsEq_iff (a b : List Label) : labsEq a b = true ↔ a = b := (labsEqS a b).2

/-- The label part of the fused `br l` (`brFast` without the value stack). -/
def brLab (a : Arc) (L : List Label) (H l : Nat) : Option (Label × List Label) :=
  let c := a.core
  if l < c.nPush then
    let lab := SimLab.mk H (c.pushes.getD (c.nPush - 1 - l) default)
    some (lab, matOnto H (c.pushes.take (c.nPush - (if lab.isLoop then l else l + 1))) (L.drop c.pops))
  else
    match L[c.pops + (l - c.nPush)]? with
    | some lab => some (lab, L.drop (c.pops + (if lab.isLoop then l else l + 1) - c.nPush))
    | none => none

/-- `brFast` once its label part is known. -/
def brFin (s : St) (f : Frame) : Option (Label × List Label) → Res
  | some (lab, ls) => finishBr s f lab ls
  | none => .unmodeled "invariant: branch to an unknown label"

theorem brFast_brLab (s : St) (f : Frame) (a : Arc) (l : Nat) :
    brFast s f a l = brFin s f (brLab a f.labels s.stack.size l) := by
  unfold brFast brLab
  simp only
  split
  · rfl
  · split <;> simp only [brFin]

/-- What an arc's label work yields: the plain run's labels, or the fused branch's label part. -/
inductive ArcRes where
  | plain (L : List Label)
  | br (r : Option (Label × List Label))

/-- The label work of arc `a` on labels `L` at stack height `H`; `none` when the guard fails. -/
def arcRes (a : Arc) (L : List Label) (H : Nat) : Option ArcRes :=
  if lenGe a.guard L then
    some (match a.br with
      | none => .plain (matOnto H a.core.pushes (L.drop a.core.pops))
      | some (l, _) => .br (brLab a L H l))
  else none

/-- What `doBr` decides from the labels alone. -/
inductive BrI where
  | ret
  | bad
  | go (lab : Label) (ls : List Label)

/-- `doBr`'s label work, in O(`l`): `l + 1 ≥ length` is `¬ lenGe (l + 2)`. -/
def brInfo (L : List Label) (l : Nat) : BrI :=
  if !lenGe (l + 2) L then .ret
  else
    match L[l]? with
    | none => .bad
    | some lab => .go lab (if lab.isLoop then L.drop l else L.drop (l + 1))

/-- `doBr` once its label work is known. -/
def doBrI (p : Prepared) (s : St) (f : Frame) : BrI → Res
  | .ret => doReturn p s
  | .bad => .unmodeled "invariant: branch to an unknown label"
  | .go lab ls =>
    let vals := s.stack.extract (s.stack.size - lab.arity) s.stack.size
    let s := { s with stack := s.stack.extract 0 lab.height ++ vals }
    .cont (setFrame s { f with pc := lab.target, labels := ls })

theorem doBr_brInfo (p : Prepared) (s : St) (f : Frame) (l : Nat) :
    doBr p s f l = doBrI p s f (brInfo f.labels l) := by
  unfold doBr brInfo
  by_cases h : l + 1 ≥ f.labels.length
  · have h' : (!lenGe (l + 2) f.labels) = true := by
      cases hb : lenGe (l + 2) f.labels
      · rfl
      · have := (lenGe_iff _ _).1 hb; omega
    simp only [h, ↓reduceIte, h', doBrI]
  · have h' : (!lenGe (l + 2) f.labels) = false := by
      have : lenGe (l + 2) f.labels = true := (lenGe_iff _ _).2 (by omega)
      simp [this]
    simp only [h, ↓reduceIte, h', Bool.false_eq_true]
    split <;> rename_i heq <;> simp only [heq, doBrI]

/-- What a memo entry caches. -/
inductive MOut where
  | arc (r : Option ArcRes)
  | br (r : BrI)

/-- One memo entry: its pc, the input labels, the stack height (arc) or branch depth (branch), and
the result. -/
structure MEntry where
  fn : Nat
  pc : Nat
  inp : List Label
  key : Nat
  out : MOut

/-- Number of memo slots (direct-mapped by `(fn, pc)`). Any value is correct. -/
def memoSlots : Nat := 256

/-- Label work below this size is recomputed rather than memoized. Any value is correct. -/
def memoMin : Nat := 16

abbrev Memo := Array (Option MEntry)

def Memo.empty : Memo := Array.replicate memoSlots none

@[inline] def memoSlot (fn pc : Nat) : Nat := (pc + 7 * fn) % memoSlots

/-- The arc stored at `(fn, pc)`. -/
def arcOfKey (arcs : Array (Array (Option Arc))) (fn pc : Nat) : Option Arc :=
  (arcs.getD fn #[]).getD pc none

/-- An entry is correct: its result is the label work of its input. -/
def EntryOK (arcs : Array (Array (Option Arc))) (e : MEntry) : Prop :=
  match e.out with
  | .arc r => ∀ a, arcOfKey arcs e.fn e.pc = some a → r = arcRes a e.inp e.key
  | .br r => r = brInfo e.inp e.key

def MemoOK (arcs : Array (Array (Option Arc))) (m : Memo) : Prop :=
  ∀ (j : Nat) (e : MEntry), m[j]? = some (some e) → EntryOK arcs e

theorem memoOK_empty (arcs : Array (Array (Option Arc))) : MemoOK arcs Memo.empty := by
  intro j e h
  simp [Memo.empty, Array.getElem?_replicate] at h

theorem memoOK_set {arcs : Array (Array (Option Arc))} {m : Memo} (hm : MemoOK arcs m)
    (i : Nat) {e : MEntry} (he : EntryOK arcs e) : MemoOK arcs (m.setIfInBounds i (some e)) := by
  intro j e' h
  rw [Array.getElem?_setIfInBounds] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; exact he
    · cases h
  · exact hm j e' h

/-- The arc's label work, memoized when it is large. -/
def memoArc (m : Memo) (fn pc : Nat) (a : Arc)
    (L : List Label) (H : Nat) : Option ArcRes × Memo :=
  if a.guard + a.core.nPush < memoMin then (arcRes a L H, m) else
  let j := memoSlot fn pc
  let fresh := fun (_ : Unit) =>
    let r := arcRes a L H
    (r, m.setIfInBounds j (some ⟨fn, pc, L, H, .arc r⟩))
  match m[j]? with
  | some (some ⟨fn', pc', inp, H', .arc r⟩) =>
    if fn' == fn && pc' == pc && H' == H && labsEq L inp then (r, m) else fresh ()
  | _ => fresh ()

theorem memoArc_spec {arcs : Array (Array (Option Arc))} {m : Memo} (hm : MemoOK arcs m)
    {fn pc : Nat} {a : Arc} (ha : arcOfKey arcs fn pc = some a) (L : List Label) (H : Nat) :
    (memoArc m fn pc a L H).1 = arcRes a L H ∧ MemoOK arcs (memoArc m fn pc a L H).2 := by
  unfold memoArc
  split
  · exact ⟨rfl, hm⟩
  · have hfresh : MemoOK arcs
        (m.setIfInBounds (memoSlot fn pc) (some ⟨fn, pc, L, H, .arc (arcRes a L H)⟩)) :=
      memoOK_set hm _ (fun a' ha' => by simp only at ha'; rw [ha] at ha'; cases ha'; rfl)
    simp only
    split
    · rename_i fn' pc' inp H' r hj
      split
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hl⟩ := hc
        have hl := (labsEq_iff _ _).1 hl
        subst hl
        have := hm _ _ hj
        exact ⟨this a ha, hm⟩
      · exact ⟨rfl, hfresh⟩
    · exact ⟨rfl, hfresh⟩

/-- `doBr`'s label work, memoized when the branch is deep. -/
def memoBr (m : Memo) (fn pc : Nat) (L : List Label) (l : Nat) : BrI × Memo :=
  if l < memoMin then (brInfo L l, m) else
  -- the depth is part of the slot, so a `br_table` alternating between targets does not thrash
  let j := memoSlot fn (pc + 13 * l)
  let fresh := fun (_ : Unit) =>
    let r := brInfo L l
    (r, m.setIfInBounds j (some ⟨fn, pc, L, l, .br r⟩))
  match m[j]? with
  | some (some ⟨fn', pc', inp, l', .br r⟩) =>
    if fn' == fn && pc' == pc && l' == l && labsEq L inp then (r, m) else fresh ()
  | _ => fresh ()

theorem memoBr_spec {arcs : Array (Array (Option Arc))} {m : Memo} (hm : MemoOK arcs m)
    (fn pc : Nat) (L : List Label) (l : Nat) :
    (memoBr m fn pc L l).1 = brInfo L l ∧ MemoOK arcs (memoBr m fn pc L l).2 := by
  unfold memoBr
  split
  · exact ⟨rfl, hm⟩
  · have hfresh : MemoOK arcs
        (m.setIfInBounds (memoSlot fn (pc + 13 * l)) (some ⟨fn, pc, L, l, .br (brInfo L l)⟩)) :=
      memoOK_set hm _ rfl
    simp only
    split
    · rename_i fn' pc' inp l' r hj
      split
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hl⟩ := hc
        have hl := (labsEq_iff _ _).1 hl
        subst hl
        exact ⟨hm _ _ hj, hm⟩
      · exact ⟨rfl, hfresh⟩
    · exact ⟨rfl, hfresh⟩

/-- `exec` with memoized branch label work. -/
def execM (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (i : Instr) (m : Memo) :
    Res × Memo :=
  match i with
  | .br l =>
    let r := memoBr m f.fn f.pc f.labels l
    (doBrI p s f r.1, r.2)
  | .brIf l =>
    let (c, s1) := popN s
    if c ≠ 0 then
      let r := memoBr m f.fn f.pc f.labels l
      (doBrI p s1 f r.1, r.2)
    else (exec cfg p s f pf i, m)
  | .brTable ls d =>
    let (c, s1) := popN s
    let r := memoBr m f.fn f.pc f.labels (ls[c]?.getD d)
    (doBrI p s1 f r.1, r.2)
  | _ => (exec cfg p s f pf i, m)

theorem execM_spec (cfg : NearCfg) (p : Prepared) {arcs : Array (Array (Option Arc))} {m : Memo}
    (hm : MemoOK arcs m) (s : St) (f : Frame) (pf : PFunc) (i : Instr) :
    (execM cfg p s f pf i m).1 = exec cfg p s f pf i ∧ MemoOK arcs (execM cfg p s f pf i m).2 := by
  unfold execM
  split
  · rename_i l
    obtain ⟨h1, h2⟩ := memoBr_spec hm f.fn f.pc f.labels l
    exact ⟨by simp only [exec, h1, doBr_brInfo], h2⟩
  · rename_i l
    obtain ⟨h1, h2⟩ := memoBr_spec (arcs := arcs) hm f.fn f.pc f.labels l
    rcases hp : popN s with ⟨c, s1⟩
    by_cases hc : c = 0
    · constructor
      · simp [hc]
      · simpa [hc] using hm
    · constructor
      · simp only [exec, hp, ne_eq, hc, not_false_eq_true, ↓reduceIte, h1, doBr_brInfo]
      · simpa [hc] using h2
  · rename_i ls d
    obtain ⟨h1, h2⟩ := memoBr_spec hm f.fn f.pc f.labels (ls[(popN s).1]?.getD d)
    exact ⟨by simp only [exec, h1, doBr_brInfo], h2⟩
  · exact ⟨rfl, hm⟩

/-- The fused branch once its label part is known (`fuseBr` with `brFin`). -/
def fuseBrM (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (a : Arc)
    (g : Option (IK × Fee)) (blab : Option (Label × List Label)) : Res :=
  match g with
  | none => brFin s f blab
  | some (k, fee) =>
    match charge s fee (if k = .linear then topCount s else 0) with
    | .cont s' => brFin s' f blab
    | _ => step cfg p (applyArc s f a)

theorem fuseBrM_eq (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (a : Arc) (l : Nat)
    (g : Option (IK × Fee)) :
    fuseBrM cfg p s f a g (brLab a f.labels s.stack.size l) = fuseBr cfg p s f a l g := by
  unfold fuseBrM fuseBr
  cases g with
  | none => exact (brFast_brLab s f a l).symm
  | some kf =>
    obtain ⟨k, fee⟩ := kf
    simp only
    cases hc : charge s fee (if k = .linear then topCount s else 0) with
    | cont s' =>
      simp only
      rw [brFast_brLab, charge_cont_stack _ _ _ _ hc]
    | fin _ => rfl
    | abort _ _ => rfl
    | unmodeled _ => rfl

/-- `runFast` with the label memo. The same dispatch; the arc's and the branches' label work comes
from `memoArc`/`memoBr`. -/
def runMemo (cfg : NearCfg) (p : Prepared) (arcs : Array (Array (Option Arc))) :
    Nat → Memo → St → Res
  | 0, _, _ => .unmodeled "fuel exhausted"
  | n + 1, m, s =>
    match s.frames with
    | [] => .fin s
    | f :: _ =>
      match p.funcs[f.fn]? with
      | none => .unmodeled "bad frame"
      | some pf =>
        match pf.code[f.pc]? with
        | none => .unmodeled "pc out of range"
        | some i =>
          match pf.gas[f.pc]? with
          | none => .unmodeled "invariant: gas table shorter than the code"
          | some none =>
            match arcAt arcs f i with
            | some a =>
              let am := memoArc m f.fn f.pc a f.labels s.stack.size
              match am.1 with
              | some (.br blab) =>
                match a.br with
                | some (_, g) =>
                  if a.core.len ≤ n then
                    match fuseBrM cfg p s f a g blab with
                    | .cont s' => runMemo cfg p arcs (n - a.core.len) am.2 s'
                    | r => r
                  else
                    match exec cfg p s f pf i with
                    | .cont s' => runMemo cfg p arcs n am.2 s'
                    | r => r
                | none => runFast cfg p arcs (n + 1) s
              | some (.plain L) =>
                if 0 < a.core.len ∧ a.core.len ≤ n + 1 then
                  runMemo cfg p arcs (n + 1 - a.core.len) am.2
                    (setFrame s { f with pc := f.pc + a.core.len, labels := L })
                else
                  match exec cfg p s f pf i with
                  | .cont s' => runMemo cfg p arcs n am.2 s'
                  | r => r
              | none =>
                match exec cfg p s f pf i with
                | .cont s' => runMemo cfg p arcs n am.2 s'
                | r => r
            | none =>
              let em := execM cfg p s f pf i m
              match em.1 with
              | .cont s' => runMemo cfg p arcs n em.2 s'
              | r => r
          | some (some (k, fee)) =>
            match charge s fee (if k = .linear then topCount s else 0) with
            | .cont s1 =>
              let em := execM cfg p s1 f pf i m
              match em.1 with
              | .cont s' => runMemo cfg p arcs n em.2 s'
              | r => r
            | r => r
termination_by n => n
decreasing_by all_goals omega

theorem arcAt_key {arcs : Array (Array (Option Arc))} {f : Frame} {i : Instr} {a : Arc}
    (h : arcAt arcs f i = some a) : arcOfKey arcs f.fn f.pc = some a := by
  unfold arcAt at h
  split at h
  · exact h
  · cases h

/-- **`runMemo` is `runFast`**, for every fuel and state, given a valid memo. -/
theorem runMemo_eq_runFast (cfg : NearCfg) (p : Prepared) (arcs : Array (Array (Option Arc))) :
    ∀ (n : Nat) (m : Memo) (s : St), MemoOK arcs m →
      runMemo cfg p arcs n m s = runFast cfg p arcs n s := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro m s hm
  cases n with
  | zero => rw [runMemo, runFast]
  | succ n =>
    have hK : ∀ (r : Res) (m' : Memo), MemoOK arcs m' → (match r with
        | .cont s' => runMemo cfg p arcs n m' s'
        | r => r) = (match r with
        | .cont s' => runFast cfg p arcs n s'
        | r => r) := by
      intro r m' hm'
      cases r with
      | cont s' => exact ih n (by omega) m' s' hm'
      | fin _ => rfl
      | abort _ _ => rfl
      | unmodeled _ => rfl
    rw [runMemo, runFast]
    cases hfr : s.frames with
    | nil => rfl
    | cons f fs =>
      simp only
      cases hpf : p.funcs[f.fn]? with
      | none => rfl
      | some pf =>
        simp only
        cases hcode : pf.code[f.pc]? with
        | none => rfl
        | some i =>
          simp only
          cases hgas : pf.gas[f.pc]? with
          | none => rfl
          | some g =>
            cases g with
            | some kf =>
              obtain ⟨k, fee⟩ := kf
              simp only
              cases charge s fee (if k = .linear then topCount s else 0) with
              | cont s1 =>
                simp only
                obtain ⟨h1, h2⟩ := execM_spec cfg p hm s1 f pf i
                rw [h1]
                exact hK _ _ h2
              | fin _ => rfl
              | abort _ _ => rfl
              | unmodeled _ => rfl
            | none =>
              simp only
              cases harc : arcAt arcs f i with
              | none =>
                simp only
                obtain ⟨h1, h2⟩ := execM_spec cfg p hm s f pf i
                rw [h1]
                exact hK _ _ h2
              | some a =>
                simp only
                obtain ⟨h1, h2⟩ := memoArc_spec hm (arcAt_key harc) f.labels s.stack.size
                generalize memoArc m f.fn f.pc a f.labels s.stack.size = am at h1 h2
                obtain ⟨ar, m'⟩ := am
                simp only at h1 h2 ⊢
                subst h1
                unfold arcRes
                by_cases hgd : lenGe a.guard f.labels = true
                · simp only [hgd, ↓reduceIte]
                  cases hbr : a.br with
                  | some lg =>
                    obtain ⟨l, g⟩ := lg
                    simp only
                    by_cases hlen : a.core.len ≤ n
                    · simp only [hlen, ↓reduceIte]
                      rw [fuseBrM_eq]
                      cases fuseBr cfg p s f a l g with
                      | cont s' => exact ih _ (by omega) m' s' h2
                      | fin _ => rfl
                      | abort _ _ => rfl
                      | unmodeled _ => rfl
                    · simp only [hlen, ↓reduceIte]
                      exact hK _ m' h2
                  | none =>
                    simp only
                    by_cases hlen : 0 < a.core.len ∧ a.core.len ≤ n + 1
                    · simp only [hlen, ↓reduceDIte, and_self, ↓reduceIte]
                      rw [ih _ (by omega) m' _ h2]
                      rfl
                    · simp only [hlen, ↓reduceDIte, ↓reduceIte]
                      exact hK _ m' h2
                · simp only [hgd, Bool.false_eq_true, ↓reduceIte]
                  exact hK _ m' h2

/-! ## The fast call layer (copies of `Exec`'s call layer with `runFast`) -/

/-- `callEntry` with arcs. -/
def callEntryFast (cfg : NearCfg) (p : Prepared) (arcs : Array (Array (Option Arc))) (fuel : Nat)
    (s : St) (fi : Nat) : Except String (St × Option String) :=
  let s := { s with gas := { s.gas with g := s.gas.remaining }, stack := #[], frames := [] }
  let r := match enter p s fi with
    | .cont s => runMemo cfg p arcs fuel Memo.empty s
    | r => r
  match r with
  | .fin s => (sync s).map (·, none)
  | .abort s e => (sync s).map (·, some e)
  | .unmodeled why => .error why
  | .cont _ => .error "cont"

/-- `callEntry` with the module's own arc table. -/
def callEntryArcs (cfg : NearCfg) (p : Prepared) (fuel : Nat) (s : St) (fi : Nat) :
    Except String (St × Option String) :=
  callEntryFast cfg p (arcsOf p) fuel s fi

/-- `runCall` with arcs: verbatim `Exec.runCall`, the arc table built once per call. -/
def runCallFast (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (fuel : Nat)
    (blockLevel : Bool := true) (full : Bool := false) (real : Option TTN.RealStore := none) : Run :=
  let emptySt (gs : Gas) : St :=
    { pages := #[], globals := #[], table := #[], tableMax := 0, elems := #[], datas := #[],
      stackRem := 0, gas := gs, ctx := ctx }
  let ext (s : St) : String := if full then fullExtra s else ""
  let nop (e : String) : Run := .line (s!"abort 0 0 {e}" ++ ext (emptySt (Gas.init ctx.prepaidGas)))
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
            let arcs := arcsOf p
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

/-- `runCallWithLimits` over `runCallFast`. -/
def runCallWithLimitsFast (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (fuel : Nat) (blockLevel : Bool := true) (full : Bool := false)
    (real : Option TTN.RealStore := none) : Run :=
  let fallback := fun (_ : Unit) => runCallFast cfg code method ctx fuel blockLevel full real
  if !cfg.loadingLimits then fallback () else
  match prepare cfg code blockLevel with
  | .ok p =>
    if instanceAllocationFits p.m then fallback () else
      .line ("abort 0 0 " ++ instanceLoadingError ++
        (if full then " || compute 0 || logs  || actions  || trie " else ""))
  | _ => fallback ()

/-- `outcome` over `runCallWithLimitsFast`. -/
def outcomeFast (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (fuel : Nat)
    (blockLevel : Bool := true) (full : Bool := false) : String :=
  let ext (s : St) : String := if full then fullExtra s else ""
  match runCallWithLimitsFast cfg code method ctx fuel blockLevel full with
  | .line l => l
  | .done s (some e) => s!"abort {s.gas.burnt} {s.gas.used} {e}" ++ ext s
  | .done s none =>
    let ret := match s.ret with
      | some (.inl d) => hex d
      | some (.inr r) => s!"receipt{r}"
      | none => "-"
    s!"ok {s.gas.burnt} {s.gas.used} {ret} {s.balance}" ++ ext s
/-! ## Proofs: the call layer, and the compiler replacement -/

theorem callEntryFast_eq (cfg : NearCfg) (p : Prepared) (arcs : Array (Array (Option Arc)))
    (hv : ArcsValid p arcs) (fuel : Nat) (s : St) (fi : Nat) :
    callEntryFast cfg p arcs fuel s fi = callEntry cfg p fuel s fi := by
  unfold callEntryFast callEntry
  simp only [runMemo_eq_runFast cfg p arcs _ _ _ (memoOK_empty arcs), runFast_eq_run cfg p arcs hv]
  rfl

/-- Compiled `callEntry` runs with the module's arc table. -/
@[csimp] theorem callEntry_eq_arcs : @callEntry = @callEntryArcs := by
  funext cfg p fuel s fi
  exact (callEntryFast_eq cfg p (arcsOf p) (arcsOf_valid p) fuel s fi).symm

/-- Compiled `runCall` runs with arcs (table built once per call). -/
@[csimp] theorem runCall_eq_fast : @runCall = @runCallFast := by
  funext cfg code method ctx fuel blockLevel full real
  unfold runCall runCallFast
  simp only [callEntryFast_eq _ _ _ (arcsOf_valid _)]
  rfl

@[csimp] theorem runCallWithLimits_eq_fast : @runCallWithLimits = @runCallWithLimitsFast := by
  funext cfg code method ctx fuel blockLevel full real
  unfold runCallWithLimits runCallWithLimitsFast
  rw [runCall_eq_fast] <;> rfl

@[csimp] theorem outcome_eq_fast : @outcome = @outcomeFast := by
  funext cfg code method ctx fuel blockLevel full
  unfold outcome outcomeFast
  rw [runCallWithLimits_eq_fast] <;> rfl


end NearSpecV3.Wasm

#print axioms NearSpecV3.Wasm.runFast_eq_run
#print axioms NearSpecV3.Wasm.runMemo_eq_runFast
#print axioms NearSpecV3.Wasm.arcsOf_valid
#print axioms NearSpecV3.Wasm.callEntry_eq_arcs
#print axioms NearSpecV3.Wasm.runCall_eq_fast
#print axioms NearSpecV3.Wasm.runCallWithLimits_eq_fast
#print axioms NearSpecV3.Wasm.outcome_eq_fast
