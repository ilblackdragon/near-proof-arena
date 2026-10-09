import ZkFormal.NearV3.Candidates.ProcPushSortContract

/-- info: 'ZkFormal.NearV3.Candidates.ProcPushSortContract.comparator_ties' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPushSortContract.comparator_ties

/-- info: 'ZkFormal.NearV3.Candidates.ProcPushSortContract.stamp_strict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPushSortContract.stamp_strict

/-- info: 'ZkFormal.NearV3.Candidates.ProcPushSortContract.stamp_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPushSortContract.stamp_injective

/-- info: 'ZkFormal.NearV3.Candidates.ProcPushSortContract.stamped_order' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPushSortContract.stamped_order

/-- info: 'ZkFormal.NearV3.Candidates.ProcPushSortContract.sorted_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPushSortContract.sorted_unique
