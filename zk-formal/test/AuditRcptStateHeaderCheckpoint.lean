import ZkFormal.NearV3.Assembly.RcptStateHeaderCheckpoint

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.headerCheckpointConstraints_count' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.headerCheckpointConstraints_count

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_native_checkpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_native_checkpoint
