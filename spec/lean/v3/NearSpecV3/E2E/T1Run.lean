import Lean
import NearSpecV3.E2E.Statement
import NearSpecV3.Examples.RealCaseD3T1Data

/-!
# E2E-M11h: T1's accepting `CM` run, kernel-checked in two pieces (on demand)

`decide +kernel` of the whole checker on T1 (`acceptsSuccessor` at `allFeatures`) exceeds the
34 GB per-process cap (OOM-killed at 34 GB after ~105 s; the `d3c7` `06-h10006-s0` instance of
`RealChunk.lean` needed a 40 GB cap). The run is therefore checked in two kernel pieces, cut after
`INTAKE` (the first `CM` step):

1. **`t1_step0 : CM.step t1Init = .ok t1C0`**, with `t1C0 = eng t1I ⟨.start, initRec …⟩` and
   `t1I : Intake` a **literal**. The literal is produced at elaboration time by running `CM.step`
   in the interpreter and converting the resulting `Intake` with derived `Lean.ToExpr` instances
   (an untrusted oracle). The equation is closed by `Eq.refl` checked **by the kernel only**
   (`kernel_rfl`: the goal is assigned without elaborator unification, as `decide +kernel` does),
   so the kernel evaluates `INTAKE` on T1's bytes and compares the result with the literal.
2. **`t1_rest : okAcc (runN 12 t1C0) = true`** by `decide +kernel`: the remaining twelve `CM`
   steps (ten engine steps — one of them the `d3tiny` FunctionCall, executed by the spec's Wasm
   interpreter — then `FINAL`) from the literal intake, ending in an accepting configuration.

`t1_accepts : ∃ cf, StepsN 13 (.init T1) cf ∧ cf.accepting = true` combines them. Measured: one
`lean` process, 192 s wall, 27.1 GB peak RSS (piece 1 alone: 64 s, 12.6 GB).

Build (on demand, not in `defaultTargets`):
`HEAVY_MEM=34G /data/illia/nearproof-deps/bin/heavy lake build NearSpecV3.E2E.T1Run`.
-/

open Lean Meta Elab Command
open NearSpec NearSpecV3 NearSpecV3.Examples NearSpecV3.E2E

/-! ## `Lean.ToExpr` for the intake record (meta-level only: used to print the oracle literal) -/
deriving instance Lean.ToExpr for NearSpecV3.ChunkSlot
deriving instance Lean.ToExpr for NearSpecV3.BlockRec
deriving instance Lean.ToExpr for NearSpecV3.EpochRec
deriving instance Lean.ToExpr for NearSpecV3.ValidatorUpdateFacts
deriving instance Lean.ToExpr for NearSpecV3.SplitGate
deriving instance Lean.ToExpr for NearSpecV3.ApplyFacts
deriving instance Lean.ToExpr for NearSpecV3.Claim
deriving instance Lean.ToExpr for NearSpecV3.Congestion
deriving instance Lean.ToExpr for NearSpecV3.BwRequest
deriving instance Lean.ToExpr for NearSpecV3.ChunkInner
deriving instance Lean.ToExpr for NearSpecV3.Transition
deriving instance Lean.ToExpr for NearSpec.PublicKey
deriving instance Lean.ToExpr for NearSpecV3.D2.FcPerm
deriving instance Lean.ToExpr for NearSpecV3.D2.Perm
deriving instance Lean.ToExpr for NearSpecV3.D2.AK
deriving instance Lean.ToExpr for NearSpecV3.D3.L4.GcdMode
deriving instance Lean.ToExpr for NearSpecV3.D3.L4.DeployGlobal
deriving instance Lean.ToExpr for NearSpecV3.D3.L4.Gci
deriving instance Lean.ToExpr for NearSpecV3.D3.L4.UseGlobal
deriving instance Lean.ToExpr for NearSpecV3.D3.L4.StateInit
deriving instance Lean.ToExpr for NearSpecV3.D3.L4.Dsi
deriving instance Lean.ToExpr for NearSpecV3.D2.Base
deriving instance Lean.ToExpr for NearSpecV3.D2.BaseAct
deriving instance Lean.ToExpr for NearSpecV3.D2.Delegate
deriving instance Lean.ToExpr for NearSpecV3.D2.Act
deriving instance Lean.ToExpr for NearSpecV3.D2.ActionR
deriving instance Lean.ToExpr for NearSpecV3.D2.Distribution
deriving instance Lean.ToExpr for NearSpecV3.D2.RBody
deriving instance Lean.ToExpr for NearSpecV3.D2.Rcpt
deriving instance Lean.ToExpr for NearSpecV3.ShardProof
deriving instance Lean.ToExpr for NearSpecV3.EntryD2
deriving instance Lean.ToExpr for NearSpecV3.D2.TxD2
deriving instance Lean.ToExpr for NearSpecV3.StateWitnessD2
deriving instance Lean.ToExpr for NearSpecV3.BlockHdr
deriving instance Lean.ToExpr for NearSpecV3.Blk
deriving instance Lean.ToExpr for NearSpecV3.Layout
deriving instance Lean.ToExpr for NearSpecV3.RetainMode
deriving instance Lean.ToExpr for NearSpecV3.Successor.WalkTransition
deriving instance Lean.ToExpr for NearSpecV3.Successor.Walk
deriving instance Lean.ToExpr for NearSpecV3.ApplyCtx
deriving instance Lean.ToExpr for NearSpecV3.Scheduler.Params
deriving instance Lean.ToExpr for NearSpecV3.D2.HStore
deriving instance Lean.ToExpr for NearSpecV3.D2.Env
deriving instance Lean.ToExpr for NearSpec.Slot
deriving instance Lean.ToExpr for NearSpec.PTrie, NearSpec.Kids
deriving instance Lean.ToExpr for NearSpecV3.E2E.D2Fin
deriving instance Lean.ToExpr for NearSpecV3.E2E.Intake

namespace NearSpecV3.E2E.T1

/-- T1's initial configuration. -/
def t1Init : Conf := .init claimD3_02_h10196_s3 witnessD3_02_h10196_s3

/-- Close `l = r` by `Eq.refl l`, leaving the definitional check to the kernel. -/
elab "kernel_rfl" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (α, l, _) := t.eq? | throwError "kernel_rfl: not an equality"
  let u ← getLevel α
  g.assign (mkApp2 (mkConst ``Eq.refl [u]) α l)

/- The oracle: run `INTAKE` in the interpreter and add its `Intake` as the literal `t1I`. -/
run_cmd do
  match CM.step t1Init with
  | .ok (.eng I _) =>
    let dv : DefinitionVal := { name := `NearSpecV3.E2E.T1.t1I, levelParams := [], type := mkConst ``Intake, value := toExpr I, hints := .abbrev, safety := .safe }
    liftCoreM <| addDecl (.defnDecl dv)
  | _ => throwError "T1: INTAKE did not reach an engine configuration"

/-- The configuration after `INTAKE`. -/
noncomputable def t1C0 : Conf := .eng t1I ⟨.start, initRec afCfg.wasm t1I.env⟩

/-- **Piece 1** (kernel): `INTAKE` on T1's bytes yields the literal intake. -/
theorem t1_step0 : CM.step t1Init = .ok t1C0 := by kernel_rfl

/-- Accepting result of a run. -/
def okAcc : Except String Conf → Bool
  | .ok c => c.accepting
  | .error _ => false

set_option maxRecDepth 200000 in
/-- **Piece 2** (kernel): twelve more `CM` steps reach an accepting configuration. -/
theorem t1_rest : okAcc (runN 12 t1C0) = true := by decide +kernel

/-- **T1's accepting run** (13 `CM` steps). -/
theorem t1_accepts : ∃ cf, StepsN 13 t1Init cf ∧ cf.accepting = true := by
  have h := t1_rest
  unfold okAcc at h
  split at h
  · rename_i cf hr
    exact ⟨cf, .step t1_step0 (stepsN_of_runN 12 _ _ hr), h⟩
  · cases h

#print axioms t1_step0
#print axioms t1_rest
#print axioms t1_accepts

end NearSpecV3.E2E.T1
