import ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeyOwner

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeyOwner.flat_lookup' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeyOwner.flat_lookup

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeyOwner.message_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeyOwner.message_id

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeyOwner.account_owner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeyOwner.account_owner

/-- info: 'ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeyOwner.walk_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeyOwner.walk_messages
