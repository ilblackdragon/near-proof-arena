import ZkFormal.NearV3.Assembly.RcptBooleanLocal

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.booleanConstraints_count' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.booleanConstraints_count

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.booleanConstraints_in_states' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.booleanConstraints_in_states

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.bool_eval_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.bool_eval_zero

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_cBool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_cBool

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_regs_emit_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.booleanReceiptTrace_regs_emit_bool
