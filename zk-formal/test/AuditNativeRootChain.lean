import ZkFormal.NearV3.Rcpt.Candidates.NativeRootRecords
import ZkFormal.NearV3.Rcpt.Candidates.NativeRootChain
import ZkFormal.NearV3.Rcpt.Candidates.NativeRootHeader
import ZkFormal.NearV3.Rcpt.Candidates.NativeRootWidths
import ZkFormal.NearV3.Rcpt.Candidates.NativeMidrootBalance

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.nativeRootRecords_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.nativeRootRecords_length

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.nativeRootRecords_get' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.nativeRootRecords_get

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.allocated_root_records' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.allocated_root_records

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.implicit_root_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.implicit_root_chain

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.main_implicit_root_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.main_implicit_root_chain

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.implicit_last_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.implicit_last_unique

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.accepted_last_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.accepted_last_root

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.accepted_root_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.accepted_root_chain

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.allocated_post_widths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.allocated_post_widths
