import NearSpecV3.Logged.API

/-! # Axiom audit of the read-logging checker (built by the default target, so CI runs it)

`Logged.API` (`checkD3Reads`, `checkD3_congr`, `reads_restrict_eq`, `reads_fixed`) and its spine
(`WasmStepE`, `WasmRun`, `D3LSpec`) were outside the default build and rotted silently: first when
`St` gained `globalActions`/`curveHosts`, then when `callHost` began dispatching the successor curve
hosts (`dispatchArm`) and `functionCall` moved to `runCallWithLimits`. This module is in
`defaultTargets` (`lakefile.toml`), so building the package builds the whole spine, and each
`#guard_msgs` fails the build if a headline theorem's transitive axioms change (e.g. a `sorryAx`).
It mirrors `oracle/wasm-d3/lean/AuditLogged.lean`, which audits the same names from the oracle
package.
-/

/-- info: 'NearSpecV3.Logged.W.E_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Logged.W.E_step

/-- info: 'NearSpecV3.Logged.W.CR_dispatchArm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Logged.W.CR_dispatchArm

/-- info: 'NearSpecV3.Logged.W.callHostL_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Logged.W.callHostL_spec

/-- info: 'NearSpecV3.Logged.W.runCallWithLimitsL_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Logged.W.runCallWithLimitsL_spec

/-- info: 'NearSpecV3.Logged.W.runUntil_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Logged.W.runUntil_spec

/-- info: 'NearSpecV3.Logged.W.runL_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Logged.W.runL_spec

/-- info: 'NearSpecV3.Logged.checkD2L_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Logged.checkD2L_eq

/-- info: 'NearSpecV3.Logged.checkD3L_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Logged.checkD3L_eq

/-- info: 'NearSpecV3.Logged.checkD3Reads_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Logged.checkD3Reads_eq

/-- info: 'NearSpecV3.Logged.checkD3_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Logged.checkD3_congr

/-- info: 'NearSpecV3.Logged.reads_restrict_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Logged.reads_restrict_eq

/-- info: 'NearSpecV3.Logged.reads_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Logged.reads_fixed
