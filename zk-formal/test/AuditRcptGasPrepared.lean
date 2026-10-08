import ZkFormal.NearV3.Assembly.RcptGasPrepared

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.prepClaim_gasPrice' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.prepClaim_gasPrice

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.prepBody_gasPrice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.prepBody_gasPrice

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.prepD0_native_gasPrice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.prepD0_native_gasPrice

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.prepared_gasPrice_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.prepared_gasPrice_byte

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.prepared_GasPublicBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.prepared_GasPublicBytes

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.prepD0_native_GasPublicBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.prepD0_native_GasPublicBytes
