import ZkFormal.NearV3.Assembly.RcptStateSizes

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.receiptSizeConstraints_footprint' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.receiptSizeConstraints_footprint

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.receiptSizeConstraints_in_states' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.receiptSizeConstraints_in_states

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.receipt_size_offsets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.receipt_size_offsets

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.header_size_offsets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.header_size_offsets

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_sizes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_sizes
