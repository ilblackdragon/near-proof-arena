import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestHeads
import ZkFormal.NearV3.Rcpt.Candidates.NativeReplayDigestPartition

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.childPayload_root' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.childPayload_root

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.payload_root_digest' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.payload_root_digest

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.forest_head_digest_records' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.forest_head_digest_records

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.replay_digest_partition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.replay_digest_partition

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.native_replay_digest_partition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.native_replay_digest_partition
