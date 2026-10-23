import NearSpecV3.Wasm.FloatTests
import NearSpecV3.ChallengeChunkV3Float
import NearSpecV3.Logged.WasmStepE
/-!
# Axiom audit of the L2 float lane (`lake env lean NearSpecV3/Wasm/FloatAxioms.lean`)

The plan's §5 item 7 requires the transitive axioms of every new theorem to be checked, with
`propext`, `Classical.choice` and `Quot.sound` the only allowed logical axioms and no `sorryAx`.
`#print axioms` prints the closure; a theorem that needed `sorryAx` (or any new axiom) shows it in
the output. This file is not imported by anything: it is an audit script, run explicitly (see
`docs/logs/lean-chunk-L2-2026-10-23.md`).

Note the test suite is decided by the kernel (`decide`), so its theorems' closures are the
`Decidable` instances' — no axioms at all. The interesting cases are the structural theorems in
`Wasm/Float.lean` and `ChallengeChunkV3Float.lean`, and the logged-step lemmas the float arms
needed.
-/

/-! ## The semantic boundary claims -/

#print axioms NearSpecV3.Wasm.add_nan_canonical_f32
#print axioms NearSpecV3.Wasm.add_nan_canonical_f64
#print axioms NearSpecV3.Wasm.qnan_f32_bits
#print axioms NearSpecV3.Wasm.qnan_f64_bits
#print axioms NearSpecV3.Wasm.abs_f32_payload
#print axioms NearSpecV3.Wasm.neg_f32_payload
#print axioms NearSpecV3.Wasm.copysign_f32_body
#print axioms NearSpecV3.Wasm.copysign_f32_sign

/-! ## The successor relation -/

#print axioms NearSpecV3.relD3F_iff_acceptsD3F
#print axioms NearSpecV3.checkD3F_characterization
#print axioms NearSpecV3.checkD3F_eq_checkD3_of_cfg
#print axioms NearSpecV3.floatPv86_eq_pv86_iff
#print axioms NearSpecV3.floatPv86_fields

/-! ## The logged-step equivariance the new arms required -/

#print axioms NearSpecV3.Logged.W.E_pushT
#print axioms NearSpecV3.Logged.W.E_execFloat

/-! ## A sample of the directed test suite (all of it is `decide`d at build time) -/

#print axioms NearSpecV3.Wasm.FloatTests.add_zeros
#print axioms NearSpecV3.Wasm.FloatTests.min_zeros
#print axioms NearSpecV3.Wasm.FloatTests.sub_to_normal
#print axioms NearSpecV3.Wasm.FloatTests.add_payload_dropped
#print axioms NearSpecV3.Wasm.FloatTests.abs_payload_kept
#print axioms NearSpecV3.Wasm.FloatTests.nearest_2_5
#print axioms NearSpecV3.Wasm.FloatTests.trunc_s_over
#print axioms NearSpecV3.Wasm.FloatTests.sat_nan
#print axioms NearSpecV3.Wasm.FloatTests.roundPack_overflow

/-! ## The inexact-sqrt rounding tests -/

#print axioms NearSpecV3.Wasm.FloatTests.sqrt_half_f32
#print axioms NearSpecV3.Wasm.FloatTests.sqrt_half_f64
#print axioms NearSpecV3.Wasm.FloatTests.sqrt_two_f32
#print axioms NearSpecV3.Wasm.FloatTests.sqrt_two_f64
#print axioms NearSpecV3.Wasm.FloatTests.sqrt_half_f32_neighbour
