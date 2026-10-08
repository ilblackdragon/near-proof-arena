import ZkFormal.NearV3.Assembly.RcptGasEffectiveLocal

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.gasEffectiveConstraints_footprint' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.gasEffectiveConstraints_footprint

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.gasEffectiveConstraints_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.gasEffectiveConstraints_mem

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.receipt_gasEffective_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.receipt_gasEffective_local
