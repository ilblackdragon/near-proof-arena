import ZkFormal.NearV3.Assembly.RcptNativeEncoding

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.native_borsh_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.native_borsh_bytes

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.native_publickey_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.native_publickey_bytes

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.native_receipt_encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.native_receipt_encoding
