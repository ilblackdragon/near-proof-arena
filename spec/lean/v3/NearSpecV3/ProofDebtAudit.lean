import NearSpecV3.ReshardingProofs
import NearSpecV3.Wasm.FloatRange

/-! # Axiom audit of the 2026-10-29 proof-debt lane (W11 split, W04 float fuel/range)

Imported by `NearSpecV3`, so the default build fails if any headline theorem below picks up
an axiom outside `propext`, `Classical.choice`, `Quot.sound` (e.g. `sorryAx`). -/

/-- info: 'NearSpecV3.retainSplit_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.retainSplit_get

/-- info: 'NearSpecV3.retainSplitKids_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.retainSplitKids_get

/-- info: 'NearSpecV3.splitChild_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.splitChild_get

/-- info: 'NearSpecV3.splitKey_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.splitKey_partition

/-- info: 'NearSpecV3.retainSplit_refinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.retainSplit_refinedBy

/-- info: 'NearSpecV3.splitRootE_refinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.splitRootE_refinedBy

/-- info: 'NearSpecV3.Wasm.bitLenF_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Wasm.bitLenF_spec

/-- info: 'NearSpecV3.Wasm.bitLen_lt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Wasm.bitLen_lt_iff

/-- info: 'NearSpecV3.Wasm.isqrt_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Wasm.isqrt_spec

/-- info: 'NearSpecV3.Wasm.copysign_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Wasm.copysign_lt

/-- info: 'NearSpecV3.Wasm.encodeNormal_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Wasm.encodeNormal_lt

/-- info: 'NearSpecV3.Wasm.encodeSub_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Wasm.encodeSub_lt

/-- info: 'NearSpecV3.Wasm.roundPackS_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Wasm.roundPackS_lt

/-- info: 'NearSpecV3.Wasm.mul_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Wasm.mul_lt

/-- info: 'NearSpecV3.Wasm.div_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Wasm.div_lt

/-- info: 'NearSpecV3.Wasm.sqrt_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Wasm.sqrt_lt

/-- info: 'NearSpecV3.Wasm.add_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Wasm.add_lt

/-- info: 'NearSpecV3.Wasm.sub_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Wasm.sub_lt

/-- info: 'NearSpecV3.Wasm.min_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Wasm.min_lt

/-- info: 'NearSpecV3.Wasm.max_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Wasm.max_lt

/-- info: 'NearSpecV3.Wasm.roundToInt_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Wasm.roundToInt_lt

/-- info: 'NearSpecV3.Wasm.demote_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Wasm.demote_lt

/-- info: 'NearSpecV3.Wasm.promote_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Wasm.promote_lt

/-- info: 'NearSpecV3.Wasm.truncSat_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Wasm.truncSat_lt
