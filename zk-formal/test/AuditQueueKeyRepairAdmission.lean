import ZkFormal.NearV3.Candidates.QueueKeyRepairAdmission

/-- info: 'ZkFormal.NearV3.Candidates.QueueKeyRepair.existing_table' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.QueueKeyRepair.existing_table

/-- info: 'ZkFormal.NearV3.Candidates.QueueKeyRepair.certified_slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.QueueKeyRepair.certified_slot

/-- info: 'ZkFormal.NearV3.Candidates.QueueKeyRepair.retained_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.QueueKeyRepair.retained_certificate
