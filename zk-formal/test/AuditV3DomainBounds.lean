import ZkFormal.V3.Integration
import NearSpecV3.ChallengeD0a
import ZkFormal.NearV3.Rcpt.Render.Srcp.ProofComplete

/-! Axiom regression guard for the RelD0a domain bounds A9 (`e.chacha_words`, W0 = 770,000)
and A10 (`w.path_depth`, Dp0 = 32), user decisions 2026-10-09. -/

/-- info: 'NearSpecV3.Scheduler.run_eq_mid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.Scheduler.run_eq_mid

/-- info: 'NearSpecV3.prims_sched_eq_mid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.prims_sched_eq_mid

/-- info: 'NearSpecV3.relD0a_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.relD0a_iff

/-- info: 'NearSpecV3.relD0a_relD0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.relD0a_relD0

/-- info: 'NearSpecV3.relD0a_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.relD0a_mono

/-- info: 'NearSpecV3.relD0a_mono_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.relD0a_mono_all

/-- info: 'NearSpecV3.inD0a_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms NearSpecV3.inD0a_iff

/-- info: 'NearSpecV3.relD0a_iff_in' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.relD0a_iff_in

/-- info: 'NearSpecV3.WfClaim.relD0a_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.WfClaim.relD0a_rel

/-- info: 'NearSpecV3.WfClaim.domainD0a_domain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NearSpecV3.WfClaim.domainD0a_domain

/-- info: 'ZkFormal.NearV3.Sched.Complete.lane_770k_22' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Sched.Complete.lane_770k_22

/-- info: 'ZkFormal.NearV3.Sched.Complete.laneMaxes_770k' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Sched.Complete.laneMaxes_770k

/-- info: 'ZkFormal.NearV3.Sched.Complete.chachaMax_tight' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Sched.Complete.chachaMax_tight

/-- info: 'ZkFormal.NearV3.Sched.Complete.lane_prep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Sched.Complete.lane_prep

/-- info: 'ZkFormal.NearV3.Sched.Complete.lane_W0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Sched.Complete.lane_W0

/-- info: 'ZkFormal.NearV3.Sched.Complete.a9_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Sched.Complete.a9_iff

/-- info: 'ZkFormal.NearV3.Sched.Complete.chacha_cap_short' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Sched.Complete.chacha_cap_short

/-- info: 'ZkFormal.NearV3.Rcpt.SrcpDepth.srcpRows_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.SrcpDepth.srcpRows_le

/-- info: 'ZkFormal.NearV3.Rcpt.SrcpDepth.dp0_largest' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.SrcpDepth.dp0_largest

/-- info: 'ZkFormal.NearV3.Rcpt.SrcpDepth.dp0_tight' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.SrcpDepth.dp0_tight

/-- info: 'ZkFormal.NearV3.Rcpt.SrcpDepth.srcpRows_le_A10' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.SrcpDepth.srcpRows_le_A10

/-- info: 'ZkFormal.NearV3.Rcpt.SrcpDepth.proofInputs_rows_A10' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.SrcpDepth.proofInputs_rows_A10

/-- info: 'ZkFormal.NearV3.Rcpt.SrcpDepth.a10_paths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.SrcpDepth.a10_paths

/-- info: 'ZkFormal.NearV3.Rcpt.SrcpDepth.relD0a_paths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.SrcpDepth.relD0a_paths

/-- info: 'ZkFormal.NearV3.Rcpt.SrcpDepth.rcptSha_A10' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.SrcpDepth.rcptSha_A10

/-- info: 'ZkFormal.NearV3.Rcpt.SrcpDepth.sourceSha_A10' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.SrcpDepth.sourceSha_A10

/-- info: 'ZkFormal.NearV3.Rcpt.SrcpDepth.srcpSegments_A10' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.SrcpDepth.srcpSegments_A10

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.witness_bytes_do_not_bound_source_rows' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.witness_bytes_do_not_bound_source_rows

/-- info: 'ZkFormal.NearV3.Render.SrcpGen.proof_inputs_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.SrcpGen.proof_inputs_complete

/-- info: 'ZkFormal.Size.V3.rcpt_shapes_check' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.Size.V3.rcpt_shapes_check

/-- info: 'ZkFormal.Size.V3.padded_twoSha_hint_margin' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.Size.V3.padded_twoSha_hint_margin
