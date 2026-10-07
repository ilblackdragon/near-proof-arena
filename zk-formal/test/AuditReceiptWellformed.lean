import ZkFormal.NearV3.Assembly.ReceiptWellformed

/-- info: 'ZkFormal.NearV3.Assembly.pEntry_receipts_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.pEntry_receipts_wf

/-- info: 'ZkFormal.NearV3.Assembly.decodeStateWitness_receipts_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.decodeStateWitness_receipts_wf

/-- info: 'ZkFormal.NearV3.Assembly.appliedReceipts_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.appliedReceipts_wf

/-- info: 'ZkFormal.NearV3.Assembly.MainExecutionV3.NativeValid.body_decodes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.MainExecutionV3.NativeValid.body_decodes
