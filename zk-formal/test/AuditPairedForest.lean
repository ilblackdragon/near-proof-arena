import ZkFormal.NearV3.Rcpt.Candidates.NodePairedForest
import ZkFormal.NearV3.Rcpt.Candidates.NodePairedIds
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountLengths
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountWriteRun

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pairedNodes_pre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pairedNodes_pre

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pairedChildNodes_pre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pairedChildNodes_pre

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pairedForest_pre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pairedForest_pre

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pairedRecord_valueId' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pairedRecord_valueId

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pairedNodes_valueIds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pairedNodes_valueIds

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pairedChildNodes_valueIds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pairedChildNodes_valueIds

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pairedForest_valueIds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.pairedForest_valueIds

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.decoded_account_write_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.decoded_account_write_length

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.native_receipt_write_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.native_receipt_write_length

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.native_system_write_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.native_system_write_length

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.native_get_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.native_get_find

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.native_kids_get_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.native_kids_get_find

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.SizedAccountRun.forget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.SizedAccountRun.forget

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.native_sized_account_writes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.native_sized_account_writes

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.SizedAccountRun.slot_lengths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.SizedAccountRun.slot_lengths

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.SizedAccountRun.value_lengths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.SizedAccountRun.value_lengths
