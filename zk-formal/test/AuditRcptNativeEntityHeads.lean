import ZkFormal.NearV3.Assembly.RcptNativeEntityHeads

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.nativeEntity_start' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.nativeEntity_start

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.nativeEntity_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.nativeEntity_rows

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.native_entity_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.native_entity_head

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.entity_head_lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.entity_head_lookup
