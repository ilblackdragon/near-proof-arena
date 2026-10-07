import ReexecV3D3.Logged.API
import ReexecV3D3.ReadControl
import ReexecV3D3.ReadCanon
import ReexecV3D3.ReadPools
import ReexecV3D3.ReadEncoding
import ReexecV3D3.ReadComplete

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

/-- info: 'ReexecV3D3.Read.hGet_filter_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Read.hGet_filter_hash

/-- info: 'ReexecV3D3.Read.restrictPools_idempotent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Read.restrictPools_idempotent

/-- info: 'ReexecV3D3.Read.encP_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Read.encP_decoded

/-- info: 'ReexecV3D3.Read.storesOf_encodeReads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Read.storesOf_encodeReads

/-- info: 'ReexecV3D3.Read.encodeReads_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Read.encodeReads_idempotent

/-- info: 'ReexecV3D3.Read.check_canonW_of_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Read.check_canonW_of_refines

/-- info: 'ReexecV3D3.Read.checkD2CoreL_reencode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Read.checkD2CoreL_reencode

/-- info: 'ReexecV3D3.Read.canonW_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Read.canonW_refines

/-- info: 'ReexecV3D3.Read.check_canonW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Read.check_canonW

/-- info: 'ReexecV3D3.Read.canonW_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReexecV3D3.Read.canonW_idempotent
