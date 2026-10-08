import ZkFormal.NearV3.Candidates.NativeAccountPreBytes

/-- info: 'ZkFormal.NearV3.Candidates.NativeAccountPreBytes.closing_pre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.NativeAccountPreBytes.closing_pre

/-- info: 'ZkFormal.NearV3.Candidates.NativeAccountPreBytes.account_pre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.NativeAccountPreBytes.account_pre

/-- info: 'ZkFormal.NearV3.Candidates.NativeAccountPreBytes.bytes_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.NativeAccountPreBytes.bytes_perm

/-- info: 'ZkFormal.NearV3.Candidates.NativeAccountPreBytes.physical_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.NativeAccountPreBytes.physical_partition
