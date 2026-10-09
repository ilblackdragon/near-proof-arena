import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestMetadata
import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestPhysical

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.initialize_node_views' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.initialize_node_views

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.chain_node_views' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.chain_node_views

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.usage_node_views' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.usage_node_views

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.records_node_views' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.records_node_views

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pipeline_child_digests' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pipeline_child_digests

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.node_digest_records' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.node_digest_records

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.physical_node_digest_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.physical_node_digest_split
