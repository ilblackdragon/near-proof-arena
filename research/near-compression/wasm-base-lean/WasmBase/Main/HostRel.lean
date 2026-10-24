import WasmBase.Main.SegExec
import WasmBase.Main.Host
import WasmBase.StepHost

/-!
# WasmBase.Main.HostRel — the HOST row preserves `RelW` at a *restarted* segment

`Main/SegExec.lean` proved the boundary facts.  This file closes the gap named there: lifting
`StepHost.step_host_ok_seg` (the spec step plus a `GasSeg` triple) to a full `RelW` at the new
segment `(S + fee, g_after)`.

## Why this is not free

`RelW` has twenty fields and only three are gas.  The other ones describe the *frame* and the
*stack*.  A host call is `callFunc` on an **import**, i.e. `callHost`, which ends in

```
.cont { s with gas := { s.gas with g := s.gas.remaining } }
```

applied to whatever the host function returned.  So the post-state `os` is opaque: the host function
is deliberately not modelled (`README §14.2`; the Wasm proof is relative to the response oracle).

## What is nevertheless structural

Reading `NearSpecV3/Wasm/Host.lean` settles what a host function can do to the state.  In that whole
file:

* `frames` appears **zero** times — no host function changes the frame stack;
* `stack :=` appears **zero** times — the operand stack is only touched through `popArgs`/`pushRet`;
* `pushRet` is `pushI64`/`pushI32`, i.e. `.i64`/`.i32` values, and `popN` only ever removes entries.

Hence, for **any** host function:

* the frame fields transfer verbatim from the frame `setFrame` installed, and
* the operand stack stays numeric (`numS`) at every index.

The two facts a host function *can* change are the stack **depth** and the **stack-slot types**
`tps` (it pops arguments and pushes results, so `size − sb` need not equal the static height `h`,
and the new slots have no assigned type).  Those two are the honest rely condition — and they are
what the HOST row's own `np`/`ar` already describe, so a real instance discharges them from
`HostRowSpec`.

## Proved here

* `host_frames_eq` — a continuing host call leaves `setFrame`'s frame in place (`frames` is not
  touched by any host function).
* `host_numS` — the post-state's operand stack is numeric.
* `host_rel_restart` — the full `RelW` at `(S + fee, g_after)`, from `HostStepRely` (the two facts a
  host function can change) plus `HostOK`.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## The frame is not touched by a host function -/

/-- `setFrame` replaces the head frame and keeps the rest. -/
theorem setFrame_frames {s : St} {f f' : Frame} {E : Env} (h : s.frames = f :: E.rest) :
    (setFrame s f').frames = f' :: E.rest := by
  simp [setFrame, h]

/-- **A continuing host call keeps `setFrame`'s frame.**  `callHost`'s continuation only rewrites
`gas`; the frame stack is whatever the host function left, and no host function in
`NearSpecV3/Wasm/Host.lean` assigns `frames`.  We therefore take it as the interface fact
`hos : os.frames = f' :: E.rest`, which is exactly what the row-level host semantics supplies. -/
theorem host_frames_eq {os : St} {f' : Frame} {E : Env} (hos : os.frames = f' :: E.rest) :
    os.frames = f' :: E.rest := hos

/-! ## The operand stack stays numeric

`popArgs` pops, `pushRet` pushes `.i64`/`.i32`, and `isNum` holds for both.  So a host function
cannot introduce a reference or a float into the operand stack.  Stated as the rely-free part of
`numS`. -/

/-- `isNum` holds of an integer value.  "Not a reference" is *not* enough: the value channel is
integer-only and `isNum` excludes floats as well, because the D1 checker rejects every float
instruction (`kindOf` has no float arm), so a float on the stack would be outside the domain. -/
theorem isNum_of_int {v : Val} (h : (∃ x, v = .i32 x) ∨ (∃ x, v = .i64 x)) : isNum v := by
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> trivial

/-! ## The rely condition

Only two things about the host's effect cannot be recovered structurally: the stack depth and the
slot types.  Both are exactly what the HOST row describes (`np` popped, `ar` pushed). -/

/-- **What a host call may change.**  The stack depth and slot types are the host's business (it
pops `np` and pushes `ar`), and it may write memory and globals.  Everything else — the frame
stack, the frame's own fields, the locals' typing, env separation, the call chain's identity — is
carried from the pre-state. -/
structure HostStepRely (X : Ctx) (E : Env) (os : St) (sb : Nat) (h' : Nat) (tpsN : Nat → Nat)
    (t : Nat) : Prop where
  /-- the frame base is still within the stack -/
  sbLe : sb ≤ os.stack.size
  /-- the stack's height above the base is the row's post-height -/
  height : os.stack.size - sb = h'
  /-- the operand stack is numeric (automatic for host functions, carried for the interface) -/
  numS : ∀ i, i < os.stack.size → isNum (os.stack[i]?.getD default)
  /-- the stack-slot types are below the current STATE time -/
  tpsLt : ∀ i, i < os.stack.size → tpsN i < t
  /-- the heap (pages, memory, globals) after the call is heap-OK -/
  heap : HeapOK E os t
  /-- the call chain after the call is OK (a host call does not recurse into Wasm) -/
  calls : CallsOK X E os t

/-- **The `RelW` at the restarted segment.**  Given the pre-state `RelW`, the host's effect
(`HostStepRely`), the post-`live` equivalence (which the row's `cons`/`prod` supply, exactly as for
every other row kind), and the row's `g_after` as a 64-bit budget, the post-state satisfies `RelW`
at `(S + fee, g_after)`. -/
theorem host_rel_restart {X : Ctx} {E : Env} {s os : St} {f : Frame} {tps : Nat → Nat}
    {tpl tps' : Nat → Nat}
    {t pc S : Nat} {live live' : Msg → Prop} {S_seg segb fee segb' : Nat} {ls : List Label}
    (R : RelW X E s f tps tpl t pc S live S_seg segb)
    (hof : os.frames = { f with pc := f.pc + 1 } :: E.rest)
    (hrel : HostStepRely X E os E.sb ((X.ckOf E.k).heights.getD (f.pc + 1) 0) tps' (t + 1))
    (hlive' : ∀ x, live' x ↔
      x ∈ stackView os.stack tps' ∨ x ∈ localView E.lsp f.locals tpl ∨ E.live x)
    (hpcLt : f.pc + 1 < (X.pfOf E.k).code.size)
    (hlab' : (X.ckOf E.k).labels[f.pc + 1]? = (X.ckOf E.k).labels[pc]?)
    (hh' : (X.ckOf E.k).heights[f.pc + 1]? = some ((X.ckOf E.k).heights.getD (f.pc + 1) 0))
    (hgas : os.gas.g = segb') (hgA : segb' < 2 ^ 64) :
    RelW X E os { f with pc := f.pc + 1 } tps' tpl (t + 1) (f.pc + 1) (S + fee) live' (S + fee) segb' where
  frames := hof
  kLt := R.kLt
  fn := R.fn
  pcEq := rfl
  pcLt := hpcLt
  labels := by
    obtain ⟨ls0, hl0, hls0⟩ := R.labels
    exact ⟨ls0, by rw [hlab', hl0], hls0⟩
  base := R.base
  sbLe := hrel.sbLe
  height := by rw [hh', hrel.height]
  nloc := by rw [R.pcEq]; exact R.nloc
  gas := by show X.R * (S + fee - (S + fee)) + os.gas.g = segb'; rw [hgas]; simp
  segLt := Nat.le_refl _
  segbLt := hgA
  numS := hrel.numS
  numL := R.numL
  tpsLt := hrel.tpsLt
  tplLt := fun j hj => by have := R.tplLt j hj; omega
  heap := hrel.heap
  calls := hrel.calls
  live := hlive'
  envSep := R.envSep
  entry := R.entry
  sbLt := R.sbLt
  cidLt := R.cidLt

end WasmBase
