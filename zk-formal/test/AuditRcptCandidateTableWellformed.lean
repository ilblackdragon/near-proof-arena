import ZkFormal.NearV3.Assembly.RcptCandidateTableWellformed

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.flat_views_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.flat_views_length

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.flat_views_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.flat_views_body

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.view_wf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.view_wf

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.extract_wellformed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.extract_wellformed
