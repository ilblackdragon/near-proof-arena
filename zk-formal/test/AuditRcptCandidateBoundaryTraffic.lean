import ZkFormal.NearV3.Assembly.RcptCandidateBoundaryTraffic

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.filterMap_messages' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.filterMap_messages

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.boundaryMsgs_view' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.boundaryMsgs_view

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.Layout.boundary_traffic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.Layout.boundary_traffic

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.boundary_traffic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.boundary_traffic
