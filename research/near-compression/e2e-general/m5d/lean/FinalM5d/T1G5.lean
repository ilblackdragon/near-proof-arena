import FinalM5d.Leaf
import FinalM5d.T1Check
import FinalM5d.T1G5Data

/-!
# FinalM5d.T1G5 — non-vacuity of the G-5 leaf statements on T1 (kernel, `decide +kernel`)

On the public values of T1's G-5 INIT and FINAL leaves (`T1G5Data`, generated from the proofs'
statements) and T1's FIN-row cells (`T1Data`):

* **`t1_init_c0`**: lane D's INIT wrapper (`InitWrap`) holds with `b = (0, h(c0))`, lane I's chain
  digest of the cut `c0 = B_0` (`t1/chain.py`), and `ctx` the leaf's claim digest; **`t1_final_c10`**:
  the FINAL wrapper (`FinWrap`) holds with `b' = (4, h(c10))`, the chain's `done` cut. The constant
  parts `K0` / `K10` are lane E's view constants (`k0_viewE`, `k10_viewE`) with lane B's `stD .none`
  at the chain's placeholder `0^42` (lane B has not published the constant).
* **`t1_fin_dig`**: `FinDig`'s two `B_out` digests on T1: the leaf's public `ctxD (.header H)` /
  `outD (.done o).1` are `BOut.ctxHeaderD (hdrOf hb)` / `BOut.outDoneD (outputsOf …)` of T1's row
  (SHA-384 of `3 ‖ Ser.enc H` and `Ser.enc o` in the kernel), and the counters 58..82 are the
  reversed `FinIn` cells (`t1_clear`).

`c1` (INIT's output, `ctxD (.intake I)`, lane B's INTAKE) and `c9` (FINAL's input, lane B's FINAL
half) are the other halves' boundaries; their chain values still carry placeholders.
-/

namespace FinalM5d.T1G5

open ZkFormal.Air ZkFormal.Algebra FinalM5d FinalM5d.Leaf FinalM5d.Link FinalM5d.T1
open NearSpec NearSpecV3 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.M8

def toFp (l : List Nat) : List Fp := l.map Fp.ofNat
def toB (l : List Nat) : Leaf.Bytes := l.map UInt8.ofNat

/-- `0^42`: the chain's placeholder for lane B's `stD .none`. -/
def z42 : Leaf.Bytes := List.replicate 42 0

/-- The view's `init` constants (phase 0, `outD .none`, `vmD []`, `clearE` = `clear0`). -/
def K0 : BndRec :=
  { claimDigest := bdigest [], phase := 0, blockIdx := 0, receiptIdx := 0, actionIdx := 0,
    inCall := false, t := 0, stRoot := z42, ctxRoot := [], gasUsed := 0, gasBurnt := 0,
    balanceBurnt := 0, compute := 0, rPrepaid := 0, rBurnt := 0, rUsed := 0,
    outcomeAcc := bdigest [], outRcptAcc := [], proposalsAcc := bdigest [], bwAcc := bdigest [0],
    vmAcc := bdigest [], wasm := none }

/-- The view's `done` constants (phase 4, `outD (.done o)`'s last three fields, `clearE`'s zeros). -/
def K10 : BndRec := { K0 with phase := 4, bwAcc := bdigest [2] }

theorem t1_init_c0 : InitWrap K0 (pubDig (toFp pubI) InitT.PV_CLAIM) (0, toB c0) (toFp pubI) :=
  ⟨rfl, by decide +kernel⟩

theorem t1_final_c10 : FinWrap K10 (pubDig (toFp pubF) PV_CLAIM) (4, toB c10) (toFp pubF) :=
  ⟨rfl, by decide +kernel⟩

/-- Both leaves carry the same statement digest (`claimDigest` of T1's `S`). -/
theorem t1_same_ctx : pubDig (toFp pubI) InitT.PV_CLAIM = pubDig (toFp pubF) PV_CLAIM := by
  decide +kernel

theorem t1_fin_dig :
    pubDig (toFp pubF) PV_HDR = BOut.ctxHeaderD (hdrOf (fn hb)) ∧
    pubDig (toFp pubF) PV_OUT = (BOut.outDoneD (outputsOf (fn fi) (fn ro) (fn rs) (fn rsh) n)).1 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

theorem t1_clear :
    pubBytes (toFp pubF) PV_GU 8 = (slice (fn fi) 75 8).reverse ∧
    pubBytes (toFp pubF) PV_BB 16 = (slice (fn fi) 83 16).reverse := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

section viewE
variable (lB : Leaf.Bytes → Nat) [Enc.Ser Intake] [Enc.Ser GFin]
  [Enc.Ser NearSpecV3.Successor.StorageExecution.CutW.VmQ] [Enc.Ser NearSpecV3.Wasm.Run]
  [Enc.Ser ChunkInner] [Enc.Ser Outputs]
  (κ : Intake → List Leaf.Bytes) (stD : StV → Leaf.Bytes) (wasmD : WmV → Option WasmBnd)

set_option maxRecDepth 100000 in
/-- `K0` is lane E's `init` record up to `ctxRoot`, with `stD .none = 0^42`. -/
theorem k0_viewE (hst : stD .none = z42) (hw : wasmD none = none) :
    InitView (ViewE.viewE lB κ stD wasmD) K0 := by
  intro cb wb
  simp only [ViewImpl.bnd, ViewE.viewE, split, ViewE.clearE, ViewE.clear0, ViewE.outDE, ViewE.vmDE,
    chainD, hst, hw, Leaf.initRec, K0, Option.isSome_none]
  rfl

set_option maxRecDepth 100000 in
/-- `K10` is lane E's `done` record up to the two digests and the two counters. -/
theorem k10_viewE (hst : stD .none = z42) (hw : wasmD none = none) :
    FinView (ViewE.viewE lB κ stD wasmD) K10 := by
  intro H o
  simp only [ViewImpl.bnd, ViewE.viewE, split, ViewE.clearE, ViewE.outDE, ViewE.vmDE, chainD, hst, hw,
    doneRec, K10, K0, Option.isSome_none]
  rfl

end viewE

end FinalM5d.T1G5
