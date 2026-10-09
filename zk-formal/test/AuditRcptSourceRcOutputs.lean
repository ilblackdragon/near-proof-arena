import ZkFormal.NearV3.Assembly.RcptSourceRcOutputs

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.source_rc_bytes_unchanged' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.source_rc_bytes_unchanged

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.source_rc_digest_outputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.source_rc_digest_outputs
