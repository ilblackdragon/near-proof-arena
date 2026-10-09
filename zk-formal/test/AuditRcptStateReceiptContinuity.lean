import ZkFormal.NearV3.Assembly.RcptStateReceiptContinuity

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.ReceiptSegmentEnd.continues' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.ReceiptSegmentEnd.continues

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.receiptSegments_continues' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.receiptSegments_continues

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.receiptSegments_end' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.receiptSegments_end

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.listSegments_continues' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.listSegments_continues

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.listSegments_end' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.listSegments_end

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.plannedSegments_continues' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.plannedSegments_continues

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.terminal_receiptEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.terminal_receiptEnd
