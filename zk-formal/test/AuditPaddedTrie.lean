import ZkFormal.V3.Integration

/-! Assumption guards for aligned trie generators and the widened walk view. -/

/-- info: 'ZkFormal.NearV3.walk3_view_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.walk3_view_at

/-- info: 'ZkFormal.NearV3.Render.node_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.node_aligned_complete

/-- info: 'ZkFormal.NearV3.Render.uniq_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.uniq_aligned_complete

/-- info: 'ZkFormal.NearV3.Render.walk_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.walk_aligned_complete
