import ZkFormal.NearV3.Assembly.RcptStateHeaderCount

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.planned_header_inputs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.planned_header_inputs

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.headerStream_count_bytes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.headerStream_count_bytes

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.headerStream_count_small' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.headerStream_count_small

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.headerCountConstraints_in_states' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.headerCountConstraints_in_states
