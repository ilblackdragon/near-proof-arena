import ZkFormal.NearV3.Assembly.RcptCandidateTokenSequence

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.TokenRun.append' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.TokenRun.append

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.receipt_token_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.receipt_token_run

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListBlockWf.token_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListBlockWf.token_run

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.token_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.token_run

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.zero_token_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.zero_token_run
