import ZkFormal.NearV3.Rcpt.Candidates.UniqWeightedTraffic
import ZkFormal.NearV3.Rcpt.Candidates.UniqWeightedNondup
import ZkFormal.NearV3.Rcpt.Candidates.UniqPayload
import ZkFormal.NearV3.Rcpt.Candidates.RetainedStorePayload
import ZkFormal.NearV3.Rcpt.Candidates.NativePayloadOwnership
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountNativePaid

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.eidMass_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.eidMass_perm

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.eidMass_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.eidMass_append

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.eidMass_flat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.eidMass_flat

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.cast_msgId' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.cast_msgId

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.digest_mass' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.digest_mass

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.digs_node_mass' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.digs_node_mass

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.digs_all_mass' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.digs_all_mass

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.uniq_weight_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.uniq_weight_exact

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.duplicate_weight_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.duplicate_weight_exact

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.nonduplicate_weight_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.nonduplicate_weight_exact

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.nondup_payload_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.nondup_payload_exact

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.nodup_weight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.nodup_weight_le

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.retained_payload_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.retained_payload_le

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.ext_retained_payload_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.ext_retained_payload_le

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.witness_payload_instances' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.witness_payload_instances

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.native_witness_payload_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.native_witness_payload_le

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.native_payload_from_uniqueness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.native_payload_from_uniqueness

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.SizeCount.prepared_native_witness_paid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.SizeCount.prepared_native_witness_paid
