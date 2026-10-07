import ZkFormal.NearV3.Rcpt.Extract.Srcp.Bytes

/-! Guard the recovered source-proof extraction and digest-byte reconstruction. -/

/-- info: 'ZkFormal.NearV3.SrcpProof.segFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.segFacts

/-- info: 'ZkFormal.NearV3.SrcpProof.segShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.segShape

/-- info: 'ZkFormal.NearV3.SrcpProof.rootTraffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.rootTraffic

/-- info: 'ZkFormal.NearV3.SrcpProof.segRowT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.segRowT

/-- info: 'ZkFormal.NearV3.SrcpProof.leaf_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.leaf_bytes
