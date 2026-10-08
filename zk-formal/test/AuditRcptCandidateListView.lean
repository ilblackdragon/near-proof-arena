import ZkFormal.NearV3.Assembly.RcptCandidateListView

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListBlock.view_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListBlock.view_length

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListBlock.receipts_le_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListBlock.receipts_le_rows

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListBlockWf.receipts_lt_P' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListBlockWf.receipts_lt_P

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListBlockWf.count_registers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListBlockWf.count_registers

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListBlockWf.view_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListBlockWf.view_count
