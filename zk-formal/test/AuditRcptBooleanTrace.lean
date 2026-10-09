import ZkFormal.NearV3.Assembly.RcptBooleanTrace

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.planned_receipt_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.planned_receipt_wf

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.boolCols_noEmission' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.boolCols_noEmission

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_cells' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_cells
