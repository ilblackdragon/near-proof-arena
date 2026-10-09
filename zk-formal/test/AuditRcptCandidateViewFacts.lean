import ZkFormal.NearV3.Assembly.RcptCandidateViewFacts

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListBlock.view_header_canon' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListBlock.view_header_canon

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListBlockWf.view_nj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListBlockWf.view_nj

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.view_header_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.view_header_facts
