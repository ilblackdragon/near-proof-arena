import ZkFormal.NearV3.Candidates.NativeAccountSlotBalance

/-- info: 'ZkFormal.NearV3.Candidates.NativeAccountSlotBalance.account_slots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.NativeAccountSlotBalance.account_slots

/-- info: 'ZkFormal.NearV3.Candidates.NativeAccountSlotBalance.node_slots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.NativeAccountSlotBalance.node_slots

/-- info: 'ZkFormal.NearV3.Candidates.NativeAccountSlotBalance.physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.NativeAccountSlotBalance.physical
