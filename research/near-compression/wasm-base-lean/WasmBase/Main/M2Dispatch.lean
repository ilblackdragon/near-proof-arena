import WasmBase.Main.M2If
import WasmBase.Main.Final
/-!
# WasmBase.Main.M2Dispatch — row facts of every instruction row of a `wasmBaseM2Air` trace

The per-row half of the M2 soundness theorem: for every **active instruction row** of a
`Holds (wasmBaseM2Air …)` trace other than HOST (tables 1–14, IF 26, CONV 28, UNREACH 29), the
row's `RowFacts2` for the M2 context `X.toCtx`.  Everything is derived from `Holds`, the M2 checker
(`M2Ctx.hM`), the public-input layout (`PubOK`) and the CODE/FUNC commitment bindings
(`CodeOK`, `FuncOK`): no `hsend`/`hsendF` premise remains (`m2_hsend_r16`, `m2_hsend_fetch`).

What is **not** here (and is the remaining step to `wasm_base_sound_m2`): the STATE/CH bus
decomposition of `wasmBaseM2Air` into these rows plus HOST (22) and the non-instruction tables
(HOSTO, HOSTT, HOSTB, REG-C), and the composition with `exec_of_rows_seg`.
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-- The instruction table at index `t` of `wasmBaseM2Air` (HOST excluded). -/
def chipM2 (t : Nat) : Table :=
  if t = 26 then IfC.table else if t = 28 then Conv.table else if t = 29 then Unreach.table else chipT t

/-- The instruction-table indices of `wasmBaseM2Air` other than HOST. -/
def IsInstrM2 (t : Nat) : Prop := (1 ≤ t ∧ t ≤ 14) ∨ t = 26 ∨ t = 28 ∨ t = 29

/-- **The per-row dispatch of `wasmBaseM2Air`.**  Every active instruction row (tables 1–14, 26, 28,
29) of a satisfied M2 trace has `RowFacts2` for the M2 context. -/
theorem m2_rowfacts (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hpub : PubOK X.toCtx nloc ngl pub)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    {t r : Nat} (htI : IsInstrM2 t) (hr : r < tr.height t) (ha : rowAct (chipM2 t) tr pub t r) :
    RowFacts2 X.toCtx (rowIn (chipM2 t) tr pub t r) (rowOut (chipM2 t) tr pub t r)
      (rowCons (chipM2 t) tr pub t r) (rowProd (chipM2 t) tr pub t r) := by
  rcases htI with ⟨h1, h14⟩ | rfl | rfl | rfl
  · have hne : chipM2 t = chipT t := by
      simp only [chipM2]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [hne] at ha ⊢
    exact (chipFactsC X.toCtx (m2_holdsC H)).rows (looks_m2 X H hpub hcode hfunc) hpub t h1 h14 r hr ha
  · exact (if_rowfacts_m2 X H hpub hcode hr ha).two
  · exact conv_rowfacts_m2 X H hcode (m2_hsend_fetch H hpub) (m2_hsend_r16 H hpub) hr
      (by simpa [rowAct, chipM2, Conv.table, Conv.inters, stdState, stateIn] using ha)
  · exact unreach_rowfacts_m2 X H hcode (m2_hsend_fetch H hpub) hr
      (by simpa [rowAct, chipM2, Unreach.table, Unreach.inters, stateIn] using ha)

#print axioms m2_rowfacts

end WasmBase
