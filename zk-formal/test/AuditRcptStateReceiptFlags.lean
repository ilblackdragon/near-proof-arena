import ZkFormal.NearV3.Assembly.RcptStateReceiptFlags

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.receiptFirstConstraints_footprint' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.receiptFirstConstraints_footprint

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.receiptFirstConstraints_in_states' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.receiptFirstConstraints_in_states

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.receipt_firstFlags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.receipt_firstFlags

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.header_firstFlags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.header_firstFlags
