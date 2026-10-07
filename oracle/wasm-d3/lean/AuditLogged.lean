import NearSpecV3.Logged.API

/-! Transitive axiom audit for the stack-safe read-logging checker.
Run after `lake build nearspec-v3-check-logged` with `lake env lean AuditLogged.lean`.
The guarded messages make any change to the transitive axiom sets fail this audit.
-/

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

