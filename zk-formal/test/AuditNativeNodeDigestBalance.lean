import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestOrder
import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestJobs
import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestBoundJobs
import ZkFormal.NearV3.Rcpt.Candidates.NativeNodeDigestBalance

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.indexedOwners_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.indexedOwners_append

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.occurrenceOwners_indexed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.occurrenceOwners_indexed

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.kidOccurrenceOwners_indexed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.kidOccurrenceOwners_indexed

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.forestOccurrenceOwners_indexed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.forestOccurrenceOwners_indexed

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.node_jobs_digests' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.node_jobs_digests

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.post_bindings_of_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.post_bindings_of_map

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.replay_node_job_digests' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.replay_node_job_digests

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pipeline_node_job_digests' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pipeline_node_job_digests

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.native_node_digest_balance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.native_node_digest_balance
