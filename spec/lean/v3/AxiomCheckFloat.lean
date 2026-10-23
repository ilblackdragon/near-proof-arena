import NearSpecV3
import NearSpecV3.Logged.WasmStepE
/-! Transitive axiom audit for the L2 float increment (plan §5.7).

Checks every theorem added by `Wasm/Float.lean`, `ChallengeChunkV3Float.lean` and the two
`Logged/WasmStepE.lean` commutation lemmas. Allowed set is
`{propext, Classical.choice, Quot.sound}`; `sorryAx`, a new `axiom`, or a native shortcut is a
failure. Run with `lake env lean AxiomCheckFloat.lean`. -/
open NearSpecV3 NearSpecV3.Wasm

#print axioms NearSpecV3.Wasm.add_nan_canonical_f32
#print axioms NearSpecV3.Wasm.add_nan_canonical_f64
#print axioms NearSpecV3.Wasm.qnan_f32_bits
#print axioms NearSpecV3.Wasm.qnan_f64_bits
#print axioms NearSpecV3.Wasm.abs_f32_payload
#print axioms NearSpecV3.Wasm.neg_f32_payload
#print axioms NearSpecV3.Wasm.copysign_f32_body
#print axioms NearSpecV3.Wasm.copysign_f32_sign
#print axioms NearSpecV3.relD3F_iff_acceptsD3F
#print axioms NearSpecV3.checkD3F_characterization
#print axioms NearSpecV3.checkD3F_eq_checkD3_of_cfg
#print axioms NearSpecV3.floatPv86_eq_pv86_iff
#print axioms NearSpecV3.floatPv86_fields
#print axioms NearSpecV3.Logged.W.E_pushT
#print axioms NearSpecV3.Logged.W.E_execFloat
