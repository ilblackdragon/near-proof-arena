import ZkFormal.NearV3.Rcpt.Link.PreparedOwner
import ZkFormal.NearV3.Assembly.RcptNativeEncoding

/-- info: 'ZkFormal.NearV3.RcptLink.receipt_toBytes_enc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.RcptLink.receipt_toBytes_enc

/-- info: 'ZkFormal.NearV3.RcptLink.view_receipt_encoding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.RcptLink.view_receipt_encoding

/-- info: 'ZkFormal.NearV3.RcptLink.view_receipts_encoding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.RcptLink.view_receipts_encoding

/-- info: 'ZkFormal.NearV3.RcptLink.list_count_encoding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.RcptLink.list_count_encoding

/-- info: 'ZkFormal.NearV3.RcptLink.list_toBytes_encoding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.RcptLink.list_toBytes_encoding

/-- info: 'ZkFormal.NearV3.RcptLink.physical_list_toBytes_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.RcptLink.physical_list_toBytes_encoding

/-- info: 'ZkFormal.NearV3.RcptLink.header_owner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.RcptLink.header_owner

/-- info: 'ZkFormal.NearV3.RcptLink.public_bytes_native' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.RcptLink.public_bytes_native

/-- info: 'ZkFormal.NearV3.RcptLink.prepared_owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.RcptLink.prepared_owner


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
