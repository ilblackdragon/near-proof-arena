import ZkFormal.NearV3.Assembly.RcptTokenLedger

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.applySystemReceipt_tokens' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.applySystemReceipt_tokens

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.applyReceipts_token_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.applyReceipts_token_ledger

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.tokenLedger_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.tokenLedger_length

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.tokenLedger_boundary' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.tokenLedger_boundary

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.tokenLedger_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.tokenLedger_append

