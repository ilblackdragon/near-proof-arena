import ZkFormal.NearV3.Assembly.RcptStateHeaderFacts

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.planned_receipt_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.planned_receipt_fields

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.fields_not_header' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.fields_not_header

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_receipt_not_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_receipt_not_header

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_header_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_header_values

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_headerCurrent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_headerCurrent

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.headerCurrentConstraints_in_states' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.headerCurrentConstraints_in_states
