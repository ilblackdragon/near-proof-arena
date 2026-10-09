import ZkFormal.NearV3.Assembly.RcptStateCheckpoint

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.stateCheckpointConstraints_count' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.stateCheckpointConstraints_count

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_state_checkpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_state_checkpoint
