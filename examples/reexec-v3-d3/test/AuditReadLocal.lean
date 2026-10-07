import ReexecV3D3.Logged.API
import ReexecV3D3.ReadControl
import ReexecV3D3.ReadCanon

/-! Transitive axiom audit for the stack-safe read-logging checker.
Run from source/verifier after checking the candidate modules, with
`lake env lean ../../test/AuditReadLocal.lean`.
The guarded messages make any change to the transitive axiom sets fail this audit.
-/

/-- info: 'ReexecV3D3.Logged.W.runUntil_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Logged.W.runUntil_spec

/-- info: 'ReexecV3D3.Logged.W.runL_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Logged.W.runL_spec

/-- info: 'ReexecV3D3.Logged.checkD2L_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Logged.checkD2L_eq

/-- info: 'ReexecV3D3.Logged.checkD3L_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Logged.checkD3L_eq

/-- info: 'ReexecV3D3.Logged.checkD3Reads_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Logged.checkD3Reads_eq

/-- info: 'ReexecV3D3.Logged.checkD3_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Logged.checkD3_congr

/-- info: 'ReexecV3D3.Logged.reads_restrict_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Logged.reads_restrict_eq

/-- info: 'ReexecV3D3.Logged.reads_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Logged.reads_fixed


/-- info: 'ReexecV3D3.Read.Refines.run_reads' does not depend on any axioms -/
#guard_msgs in
#print axioms ReexecV3D3.Read.Refines.run_reads
/-- info: 'ReexecV3D3.Read.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Read.check_sound
/-- info: 'ReexecV3D3.Read.check_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Read.check_normal
