import WasmBase.Main.TmplPrep
import WasmBase.Main.WasmViewT1
/-!
# WasmBase.Main.PrepT1 — T1's PREP leaf: the trace-independent premises discharged (A-T4)

* `ctxM2_isM2 : CtxIsM2 wasmViewParamsT1` — T1's static context is the M2 checker's.
* `decFaithful_d3tiny` — `PrepDec.DecFaithfulAt` for T1's contract `d3tiny` (345 bytes, SHA-256
  `8152bed2…36bf9`), by kernel evaluation (`decide +kernel`: `prepare`, the reference walk and the
  reference decoder all evaluated by the kernel), for every configuration that differs from `pv86`
  only in `floats`, `curveHosts` and `globalActions`.

So for T1, `TmplPrep.RecordsCert` rests on the AIR's `DecodeCert` (`PrepDecSound.PrepDecodeSound`)
and the static residual `StaticCert` only.
-/
namespace WasmBase
namespace PrepT1
open NearSpecV3.Wasm WasmBase.TmplPrep WasmBase.WasmViewT1

/-- T1's contract code (corpus `d3/02-h10196-s3`, `d3tiny`). -/
def d3tiny : ArenaCore.Bytes := [0, 97, 115, 109, 1, 0, 0, 0, 1, 27, 5, 96, 1, 126, 0, 96, 1, 126, 1, 126, 96, 2, 126, 126, 0, 96, 5, 126, 126, 126, 126, 126, 1, 126, 96, 0, 0, 2, 106, 6, 3, 101, 110, 118, 5, 105, 110, 112, 117, 116, 0, 0, 3, 101, 110, 118, 12, 114, 101, 103, 105, 115, 116, 101, 114, 95, 108, 101, 110, 0, 1, 3, 101, 110, 118, 13, 114, 101, 97, 100, 95, 114, 101, 103, 105, 115, 116, 101, 114, 0, 2, 3, 101, 110, 118, 13, 115, 116, 111, 114, 97, 103, 101, 95, 119, 114, 105, 116, 101, 0, 3, 3, 101, 110, 118, 8, 108, 111, 103, 95, 117, 116, 102, 56, 0, 2, 3, 101, 110, 118, 12, 118, 97, 108, 117, 101, 95, 114, 101, 116, 117, 114, 110, 0, 2, 3, 2, 1, 4, 5, 3, 1, 0, 1, 7, 12, 2, 3, 114, 117, 110, 0, 6, 2, 99, 98, 0, 6, 10, 63, 1, 61, 1, 1, 126, 66, 0, 16, 0, 66, 0, 16, 1, 33, 0, 32, 0, 66, 224, 212, 3, 86, 4, 64, 66, 224, 212, 3, 33, 0, 11, 66, 0, 66, 16, 16, 2, 66, 1, 66, 0, 32, 0, 66, 16, 66, 1, 16, 3, 26, 66, 4, 66, 1, 16, 4, 32, 0, 66, 16, 16, 5, 11, 11, 11, 1, 0, 65, 0, 11, 5, 116, 116, 105, 110, 121, 0, 97, 4, 110, 97, 109, 101, 1, 82, 7, 0, 5, 105, 110, 112, 117, 116, 1, 12, 114, 101, 103, 105, 115, 116, 101, 114, 95, 108, 101, 110, 2, 13, 114, 101, 97, 100, 95, 114, 101, 103, 105, 115, 116, 101, 114, 3, 13, 115, 116, 111, 114, 97, 103, 101, 95, 119, 114, 105, 116, 101, 4, 8, 108, 111, 103, 95, 117, 116, 102, 56, 5, 12, 118, 97, 108, 117, 101, 95, 114, 101, 116, 117, 114, 110, 6, 4, 109, 97, 105, 110, 2, 6, 1, 6, 1, 0, 1, 110].map Nat.toUInt8

theorem d3tiny_len : d3tiny.length = 345 := by decide +kernel

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

/-- **Decoder faithfulness for `d3tiny`** at `pv86`, by kernel evaluation. -/
theorem decFaithful_d3tiny : PrepDec.DecFaithfulAt pv86 d3tiny := by
  unfold PrepDec.DecFaithfulAt
  decide +kernel

#print axioms ctxM2_isM2
#print axioms decFaithful_d3tiny

end PrepT1
end WasmBase
