import ZkFormal.NearV3.Rcpt.Candidates.PreparedRootChain
import ZkFormal.NearV3.Rcpt.Candidates.NativeHeadRootRecords
import ZkFormal.NearV3.Rcpt.Candidates.NativeRootBalance
import ZkFormal.NearV3.Rcpt.Candidates.PreparedRootEndpoints

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.forest_head_root_records' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.forest_head_root_records

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.replay_head_root_records' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.replay_head_root_records

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.native_root_balance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.native_root_balance

/-- info: 'ZkFormal.NearV3.Assembly.prepClaim_root_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.prepClaim_root_endpoints

/-- info: 'ZkFormal.NearV3.Assembly.prepD0_root_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.prepD0_root_endpoints

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.prepared_trace_root_endpoints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.prepared_trace_root_endpoints

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.prepared_root_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.prepared_root_chain
