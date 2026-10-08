import ZkFormal.NearV3.Assembly.RcptCandidateSignerTraffic

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.signerMsgs_view' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.signerMsgs_view

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.Layout.signer_traffic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.Layout.signer_traffic

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.signer_traffic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.signer_traffic
