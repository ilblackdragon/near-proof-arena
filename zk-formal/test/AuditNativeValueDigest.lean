import ZkFormal.NearV3.Rcpt.Candidates.NativeValueDigestSlots
import ZkFormal.NearV3.Rcpt.Candidates.NativeValueDigestForest
import ZkFormal.NearV3.Rcpt.Candidates.NativeValueDigestPipeline
import ZkFormal.NearV3.Rcpt.Candidates.NativeValueDigestBalance

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.slot_digest_split' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.slot_digest_split

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.update_preSlot' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.update_preSlot

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.valueDigestFrom_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.valueDigestFrom_append

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.seed_preSlot' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.seed_preSlot

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.seed_value_digests' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.seed_value_digests

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.seed_kid_value_digests' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.seed_kid_value_digests

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.forest_value_digests' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.forest_value_digests

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.seeded_value_digests' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.seeded_value_digests

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.updated_value_digests' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.updated_value_digests

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pipeline_preSlot' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pipeline_preSlot

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.metadata_value_digests' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.metadata_value_digests

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.native_preSlot_inventory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.native_preSlot_inventory

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.physical_value_balance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.physical_value_balance
