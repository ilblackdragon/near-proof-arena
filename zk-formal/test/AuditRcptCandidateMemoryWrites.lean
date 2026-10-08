import ZkFormal.NearV3.Assembly.RcptCandidateMemoryWrites

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.memoryWriteMsgs_view' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.memoryWriteMsgs_view

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.memory_write_silent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.memory_write_silent

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.memory_writes_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.memory_writes_view
