import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountStep
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountSignature

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.receipt_account_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.receipt_account_write

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.system_account_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.system_account_write

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.native_step_account_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.native_step_account_write

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.ledger_account_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.ledger_account_write

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.ledger_account_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.ledger_account_view

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.account_update_signature' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.account_update_signature

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.account_write_signatures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.account_write_signatures

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.native_receipt_signatures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.native_receipt_signatures
