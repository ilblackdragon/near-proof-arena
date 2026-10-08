import ZkFormal.NearV3.Assembly.RcptGasProductPrices

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.nativeBurn_price' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.nativeBurn_price

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.nativeRefundAmount_price' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.nativeRefundAmount_price

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.gasEffectiveByte_price' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.gasEffectiveByte_price

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.gasRawSurplusByte_price' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.gasRawSurplusByte_price

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.gasNativeSurplusByte_price' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.gasNativeSurplusByte_price
