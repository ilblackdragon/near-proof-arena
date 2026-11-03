import WasmBase.Main.SegSoundX
import WasmBase.Main.SegIface

/-!
# WasmBase.Main.SegDom — the out-boundary state is in `wasmD`'s AIR domain (E2E M4c, CORE)

`WasmView.InDom X s` (the domain of the AIR branch of lane E's Wasm view `wasmD`) from the boundary
relation at a cut.  Field by field (`seg_inDom`):

| `InDom` field | source |
|---|---|
| `ne` (a frame runs) | `RelW.frames` |
| `wf` (view `MsgWF`) | `seg_sound`'s conclusion (CUTO's range checks, `cutView_wf`) |
| `frames` (`FrameOK`) | top frame: `RelW.fn/pcLt/labels/base/numL` + `X.M.fns.Nodup` (`kOf_fnOf`); callers: `Chain` (`chain_frameOK`) |
| `numS`, `numG`, `pages` | `RelW.numS`, `HeapOK.glob`, `HeapOK.pages` |
| `regs` (`RegOK`) | `RegWF` (the same predicate) |
| `lt64`: global pc | `M2Ctx.off_bound` + the M2 checker's `codeSize < 2^20` |
| `lt64`: base, `stackRem` | `RelW.sbLt` (`< 2^28`), `CallsOK.chain` (`stackRem + charges < 2^30`) |
| `lt64`: page count | **not** in `RelW`: premise `hpg`, which follows from the public geometry `MemGeom pub s` (`pages_lt_of_memGeom`; owned by the memory sub-lane) |

`seg_wasmD`: with `InDom`, `wasmD`'s record of the cut configuration is on the AIR branch, and its
`framesDigest` is the first 42 bytes of `cutDigest (cutView X sN)` — the digest whose limbs
`seg_sound` puts in the public `ctx_out`.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

theorem fnOf_mem {X : Ctx} {k : Nat} (hk : k < X.nf) : X.fnOf k ∈ X.M.fns := by
  unfold Ctx.fnOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.getElem_mem hk

/-- Every caller frame of a chain is `FrameOK`. -/
theorem chain_frameOK {X : Ctx} (hnd : X.M.fns.Nodup) {t : Nat} :
    ∀ {cid sb k : Nat} {rest : List Frame} {sv : List Saved}, Chain X t cid sb k rest sv →
      ∀ fc ∈ rest, WasmView.FrameOK X fc
  | _, _, _, [], [], _, fc, h => by simp at h
  | _, _, _, f :: rest, c :: sv, hc, fc, h => by
    obtain ⟨a1, a2, a3, -, -, -, a7, ⟨ls, hls, hl⟩, -, -, a11, -, a13⟩ := hc
    rcases List.mem_cons.mp h with rfl | h
    · have hk : X.kOf fc.fn = c.k := by rw [a2]; exact kOf_fnOf hnd a1
      refine ⟨by rw [a2]; exact fnOf_mem a1, by rw [hk]; exact a7, ⟨ls, by rw [hk]; exact hls, by rw [a3]; exact hl⟩,
        fun j hj => (a11 j hj).1⟩
    · exact chain_frameOK hnd a13 fc h
  | _, _, _, [], _ :: _, h, _, _ => h.elim
  | _, _, _, _ :: _, [], h, _, _ => h.elim

/-- The page count is below `2^64` when the public block count is the spec memory's. -/
theorem pages_lt_of_memGeom {pub : List F} {s : St} (h : MemGeom pub s) : s.pages.size < 2 ^ 64 := by
  have hP := P_val
  have := (pub.getD pubNblk 0).toNat_lt
  have e := h.2
  unfold WasmView.nblkOf at e
  omega

/-- **`seg_inDom`: a related cut state is in the AIR domain of `wasmD`.**  From the boundary
relation (`Bnd`, the first conjunct of `BndC`), the register file's well-formedness, the view's
`MsgWF` (both are what `seg_sound` carries/concludes) and the page bound `hpg`. -/
theorem seg_inDom (X : M2Ctx) {sg : Nat → Nat × Nat} {s : St} {t S : Nat} {m : List F} {L : List Msg}
    (hB : Bnd X.toCtx sg s t S m L) (hw : RegWF s) (hwf : ∀ y ∈ cutView X.toCtx s, MsgWF y)
    (hpg : s.pages.size < 2 ^ 64) : WasmView.InDom X.toCtx s := by
  have hnd := M2Ctx.toCtx_fns_nodup X
  obtain ⟨k, pc, sb, cid, -, E, f, tps, tpl, -, -, hk, R⟩ := hB
  obtain ⟨sv, hc, -, -, hrl⟩ := R.calls.chain
  obtain ⟨tpg, hg, -⟩ := R.heap.glob
  have hfr := R.frames
  have hkf : X.toCtx.kOf f.fn = E.k := by rw [R.fn]; exact kOf_fnOf hnd R.kLt
  have hpc : f.pc < (X.toCtx.pfOf (X.toCtx.kOf f.fn)).code.size := by rw [hkf, R.pcEq]; exact R.pcLt
  refine ⟨by rw [hfr]; simp, hwf, ?_, R.numS, fun g hg' => (hg g hg').2, R.heap.pages, hw, ?_⟩
  · intro fc hfc
    rw [hfr] at hfc
    rcases List.mem_cons.mp hfc with rfl | hfc
    · obtain ⟨ls, hls, hl⟩ := R.labels
      refine ⟨by rw [R.fn]; exact fnOf_mem R.kLt, hpc, ⟨ls, by rw [hkf, R.pcEq]; exact hls, by rw [R.base]; exact hl⟩,
        R.numL⟩
    · exact chain_frameOK hnd hc fc hfc
  · rw [hfr]
    simp only [List.headD_cons]
    have hkL : E.k < X.nf := R.kLt
    have hob := X.off_bound hkL
    have htot : X.M.codeSize < 2 ^ 20 := X.mf.total
    have hsb := R.sbLt
    refine ⟨?_, by rw [R.base]; omega, by omega, hpg⟩
    unfold WasmView.gpc
    rw [hkf]
    have : f.pc < (X.pfOf E.k).code.size := by rw [hkf] at hpc; exact hpc
    show X.offOf E.k + f.pc < 2 ^ 64
    omega

#print axioms seg_inDom

/-- **`seg_wasmD`: the cut configuration is on `wasmD`'s AIR branch** (any Wasm-view parameters `P`
whose context of the entry is `X`, any fuel `n < 2^64`): `wasmD` reports the record, whose
`framesDigest` is the first 42 bytes of `cutDigest (cutView X sN)` and whose memory root, pc, base,
`stackRem`, fuel and page count are `sN`'s. -/
theorem seg_wasmD (P : WasmView.WasmViewParams) (X : M2Ctx) {sN : St} (hD : WasmView.InDom X.toCtx sN)
    {q : NearSpecV3.Wasm.CallCut.CallArgs} {p : Prepared} {k : NearSpecV3.Wasm.CallCut.EntK} {n : Nat}
    (hX : P.ctxOf q p k = some X.toCtx) (hn : n < 2 ^ 64) :
    let w : NearSpecV3.Wasm.CallCut.CallArgs × NearSpecV3.Wasm.CallCut.CallConf := (q, .ent p k (.cont sN) n)
    WasmView.wasmD P (some w) = some (WasmView.wasmBnd P w) ∧
    (WasmView.wasmBnd P w).framesDigest = (cutDigest (cutView X.toCtx sN)).take 42 ∧
    (WasmView.wasmBnd P w).memRoot = (WasmView.memRootOf sN).take 42 ∧
    (WasmView.wasmBnd P w).pc = WasmView.gpc X.toCtx (sN.frames.headD default) ∧
    (WasmView.wasmBnd P w).sp = (sN.frames.headD default).base ∧
    (WasmView.wasmBnd P w).stackRem = sN.stackRem ∧ (WasmView.wasmBnd P w).fuel = n ∧
    (WasmView.wasmBnd P w).memPages = sN.pages.size :=
  WasmView.wasmD_air P (WasmView.airOf_some P hX hD hn)

#print axioms seg_wasmD

end WasmBase
