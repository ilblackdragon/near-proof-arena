import ZkFormal.NearV3.Assembly.RcptPlanLedger

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.planLists_prefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.planLists_prefix

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.global_plan_receipt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.global_plan_receipt

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.receiptPlanToken_native' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.receiptPlanToken_native

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.applyNewChunk_plan_tokens' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.applyNewChunk_plan_tokens

