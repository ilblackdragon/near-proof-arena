import ZkFormal.NearV3.Assembly.RcptEntityRows

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.EntityPlan.rows_first' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.EntityPlan.rows_first

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.EntityPlan.rows_nonempty' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.EntityPlan.rows_nonempty

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.EntityPlan.head' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.EntityPlan.head

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.entityPlans_receipt_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.entityPlans_receipt_wf

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.EntityPlan.header_last' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.EntityPlan.header_last

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.EntityPlan.receipt_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.EntityPlan.receipt_last

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.entityPlans_final_flags' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.entityPlans_final_flags

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.planReceipts_lastInList_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.planReceipts_lastInList_count

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.entityPlans_listEnd_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.entityPlans_listEnd_count
