import ZkFormal.NearV3.Rcpt.Extract.Srcp.PathItem
import ZkFormal.NearV3.Rcpt.Link.SourceNonempty

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

/-- info: 'ZkFormal.NearV3.SrcpProof.path_accumulator_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.path_accumulator_bytes

/-- info: 'ZkFormal.NearV3.sourceBlocks_has_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.sourceBlocks_has_new

/-- info: 'ZkFormal.NearV3.new_slot_filter_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.new_slot_filter_nonempty

/-- info: 'ZkFormal.NearV3.source_shuffle_nonempty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.source_shuffle_nonempty

/-- info: 'ZkFormal.NearV3.SrcpProof.leaf_bytes_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.leaf_bytes_traffic

/-- info: 'ZkFormal.NearV3.SrcpProof.leaf_digest_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.leaf_digest_traffic

/-- info: 'ZkFormal.NearV3.SrcpProof.path_digest_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.path_digest_traffic

/-- info: 'ZkFormal.NearV3.SrcpProof.pathItem_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.pathItem_bytes

/-- info: 'ZkFormal.NearV3.SrcpProof.pathItem_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.SrcpProof.pathItem_traffic
