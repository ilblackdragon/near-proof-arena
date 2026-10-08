import ZkFormal.NearV3.Assembly.RcptStateCoverage

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.nativeStateCheckpointConstraints_count' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.nativeStateCheckpointConstraints_count

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.cStates_checkpoint_coverage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.cStates_checkpoint_coverage

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_native_state_checkpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_native_state_checkpoint
