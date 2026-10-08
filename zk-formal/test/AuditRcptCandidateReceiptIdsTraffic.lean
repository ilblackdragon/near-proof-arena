import ZkFormal.NearV3.Assembly.RcptCandidateReceiptIdsTraffic

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.receiptIdMsgs_view' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.receiptIdMsgs_view

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.rids_receive_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.rids_receive_empty

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.rids_view_receive_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.rids_view_receive_empty

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListBlockWf.header_rids' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListBlockWf.header_rids

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.rids_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.rids_view

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.rids_view_traffic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.rids_view_traffic
