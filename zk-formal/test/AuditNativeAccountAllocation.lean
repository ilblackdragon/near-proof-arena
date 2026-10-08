import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountAllocation
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountAllocationWf

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.closingKeyVersion_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.closingKeyVersion_bound

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.closingAccountView_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.closingAccountView_success

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.closingAccountViews_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.closingAccountViews_success

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.nativeAccountViews_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.nativeAccountViews_success

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.closingAccountView_wf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.closingAccountView_wf

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.closingAccountViews_member' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.closingAccountViews_member

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.nativeAccountViews_wf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.nativeAccountViews_wf
