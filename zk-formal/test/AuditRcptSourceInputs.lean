import ZkFormal.NearV3.Assembly.RcptSourceInputs

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.sourceInputLists_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.sourceInputLists_length

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.sourceInputLists_receipts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.sourceInputLists_receipts

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.sourceInputLists_applied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.sourceInputLists_applied

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.sourceInputLists_toShard' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.sourceInputLists_toShard
