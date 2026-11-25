import WasmBase.Main.TmplPrep
import WasmBase.Main.WasmViewT1
/-!
# WasmBase.Main.PrepT1Ctx — T1's static context is the M2 checker's (A-T4)

`ctxM2_isM2 : TmplPrep.CtxIsM2 wasmViewParamsT1`, the hypothesis `TmplPrep.recordsCert_of` /
`prep_relC` take on the Wasm-view parameters.
-/
namespace WasmBase
namespace PrepT1
open NearSpecV3.Wasm WasmBase.TmplPrep WasmBase.WasmViewT1

theorem ctxM2_isM2 : CtxIsM2 wasmViewParamsT1 := by
  intro q p k X h
  simp only [wasmViewParamsT1, ctxM2] at h
  split at h
  · cases h
  · split at h
    · rename_i MH hM
      cases h
      exact ⟨MH, hM, rfl⟩
    · cases h

#print axioms ctxM2_isM2

end PrepT1
end WasmBase
