import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountRebasedAllocation
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountNativeAllocation
import ZkFormal.NearV3.Rcpt.Candidates.AcceptedNativeAccounts

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.closingAccountViews_of_each' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.closingAccountViews_of_each

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.native_rebased_accounts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.native_rebased_accounts

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.newchunk_account_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.newchunk_account_context

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.newchunk_rebased_accounts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.newchunk_rebased_accounts

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.accepted_native_accounts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.accepted_native_accounts
