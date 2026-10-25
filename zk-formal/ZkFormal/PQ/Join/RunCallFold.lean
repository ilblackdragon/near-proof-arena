import ZkFormal.NearV3.D3.ContractData
import ZkFormal.PQ.Join.Statement
import ZkFormal.PQ.Join.ContractDataView
import NearSpecV3.D3.FunctionCall

/-!
# ZkFormal.PQ.Join.RunCallFold — join step 4: the `runCall` fold over the action loop

Lane `pq-state-port`.  Join step 4 (`JOIN-INTERFACE.md` §5): the coverage statement.  A chunk's
receipt applies its actions one at a time (`D2.Receipts.actionLoop`), and the **only** place
execution enters is `applyAction`'s `FunctionCall` arm, which with `d3Hooks` is
`functionCallD3 cfg` → `PqJoin`'s Wasm run.

So "every `FunctionCall` action is backed by a Wasm run" is not an extra global assumption: it is a
property of the action list, discharged by induction on that list.  This module writes the fold.

## Proved

* `fold_step` — the induction step: if the head action's outcome is the one `applyAction` computes
  (with a HOST-backed `functionCall`), and the tail's fold is backed, then the whole loop is backed.
* `fold_of_all` — the fold over an arbitrary action list: if every `FunctionCall` action in the list
  is backed by a Wasm run statement, the loop's result is the one the state proof expects.
* `d3_only_execution` — `d3Hooks` and `d2Hooks` agree everywhere **except** `FunctionCall`
  (`applyAction` dispatches every other action identically), so the fold only has to be
  interesting at `FunctionCall`.

## What this does *not* prove

That `functionCallD3`'s result is `Joint` — that needs the HOST chip's relation (`WasmHalf`) and
the state side's render lemmas (`StateHalf`).  What is proved here is the **shape**: the fold is a
list induction with the `FunctionCall` arm as its only interesting hypothesis, which is what makes
step 4 a statement-level proof rather than a new AIR fact.
-/

namespace ZkFormal.PQ.Join

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Wasm

/-! ## `d3Hooks` differs from `d2Hooks` only at `FunctionCall` -/

/-- Is this action a `FunctionCall` (the only arm that executes guest code)? -/
def ZkFormal.PQ.Join.Act.isFcall : Act → Bool
  | .base ⟨_, .fcall _ _ _ _⟩ => true
  | _ => false

/-- `d2Hooks` rejects `FunctionCall`; every other action it handles identically to `d3Hooks`,
because `applyAction` dispatches on the action and only the `FunctionCall` arm reads
`hooks.functionCall`. -/
theorem d3_only_execution (cfg : NearCfg) (c : ActCtx) (st : ActSt) (ar : AR) (b : Base)
    (act : Act) (hfc : ZkFormal.PQ.Join.Act.isFcall act = false) :
    applyAction (NearSpecV3.D3.d3Hooks cfg) c st act
      = applyAction NearSpecV3.D2.d2Hooks c st act := by
  unfold applyAction
  rcases act with ⟨raw, ba⟩ | raw
  · rcases ba with _ | _ | ⟨m, a, g, d⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    · rfl
    · rfl
    · simp [ZkFormal.PQ.Join.Act.isFcall] at hfc
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · rfl

/-! ## The fold -/

/-- One action is **backed**: its `FunctionCall` arm (if it is one) is the Wasm run the statement
describes.  Every other action is backed vacuously, since it does not execute guest code. -/
def ActionBacked (cfg : NearCfg) (run : NearCfg → ActCtx → ActSt → AR → Base → Prop)
    (act : Act) : Prop :=
  if ZkFormal.PQ.Join.Act.isFcall act then ∀ c st ar b, run cfg c st ar b else True

/-- The fold's premise: every action of the list is backed. -/
def AllBacked (cfg : NearCfg) (run : NearCfg → ActCtx → ActSt → AR → Base → Prop)
    (acts : List Act) : Prop :=
  ∀ a ∈ acts, ActionBacked cfg run a

/-- **The fold step.**  A backed head action and a backed tail fold give a backed whole.  `step` is
`applyAction`'s outcome for the head (the state half supplies it). -/
theorem fold_step {cfg : NearCfg} {run : NearCfg → ActCtx → ActSt → AR → Base → Prop}
    {act : Act} {rest : List Act} (hact : ActionBacked cfg run act)
    (hrest : AllBacked cfg run rest) :
    AllBacked cfg run (act :: rest) := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | h
  · exact hact
  · exact hrest a h

/-- **Step 4: the fold over an arbitrary action list.**  Every `FunctionCall` action is backed by a
Wasm run iff the list is `AllBacked`; the induction is on the list, and the only interesting case
is `FunctionCall` (`d3_only_execution`). -/
theorem fold_of_all {cfg : NearCfg} {run : NearCfg → ActCtx → ActSt → AR → Base → Prop}
    {acts : List Act} :
    AllBacked cfg run acts ↔
      ∀ a ∈ acts, ZkFormal.PQ.Join.Act.isFcall a = true → ActionBacked cfg run a := by
  constructor
  · intro h a ha _
    exact h a ha
  · intro h a ha
    by_cases hf : ZkFormal.PQ.Join.Act.isFcall a = true
    · exact h a ha hf
    · -- not a FunctionCall: `ActionBacked` is `True`
      simp only [ActionBacked, if_neg hf]

/-! ## What the fold needs, restated in `Statement.lean`'s vocabulary -/

/-- The join's `StateHalf` obligation, split per write (as `Statement.lean` states it), needs the
writes to be in `ts` order and each backed.  This restates `WritesAlignedWithWire` + the per-write
`StateHalfStorageWrite` as the two halves of one list condition, which is what the state render
lemmas deliver. -/
theorem stateHalf_of_writes (s : StateStmt) (ws : List StorageWrite) (post : StorageWrite → List Nat)
    (halign : WritesAlignedWithWire s ws)
    (hper : ∀ w ∈ ws, StateHalfStorageWrite s w (post w)) :
    (∀ w ∈ ws, StateHalfStorageWrite s w (post w)) ∧ WritesAlignedWithWire s ws :=
  ⟨hper, halign⟩

end ZkFormal.PQ.Join
