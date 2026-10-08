import ZkFormal.NearV3.Rcpt.Candidates.ReceiptShaJobs

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.receiptJobsAt_payloads' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.receiptJobsAt_payloads

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.receiptShaJobs_weights' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.receiptShaJobs_weights

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.receiptShaJobs_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.receiptShaJobs_capacity

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.allocate_receipt_batch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.allocate_receipt_batch
