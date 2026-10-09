import ZkFormal.NearV3.Assembly.SchedulerPriorSanity

/-- info: 'ZkFormal.NearV3.Assembly.CodecDigest.native_sanity_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.CodecDigest.native_sanity_byte

/-- info: 'ZkFormal.NearV3.Assembly.CodecDigest.PriorCore.sanity_balance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.CodecDigest.PriorCore.sanity_balance

/-- info: 'ZkFormal.NearV3.Assembly.CodecDigest.routed_sanity_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.CodecDigest.routed_sanity_balance
