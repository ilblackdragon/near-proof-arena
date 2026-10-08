import ZkFormal.NearV3.Assembly.RcptEntityInterior

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.fields_end_final' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.fields_end_final

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.fields_next_not_final' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.fields_next_not_final

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.receiptEnd_final' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.receiptEnd_final

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.EntityPlan.header_inside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.EntityPlan.header_inside

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.EntityPlan.receipt_inside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.EntityPlan.receipt_inside
