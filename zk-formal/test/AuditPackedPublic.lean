import ZkFormal.NearV3.Public.Records
import ZkFormal.NearV3.Public.Fits
import ZkFormal.NearV3.Public.Body
import ZkFormal.NearV3.Public.Source
import ZkFormal.NearV3.Public.Header
import ZkFormal.NearV3.Public.Boundary
import ZkFormal.NearV3.Public.NatRecords

open ZkFormal.NearV3.Public ZkFormal.V2 ZkFormal.Algebra

private def blocks : List Payload := [[], [[11,22],[11,22]], [[255]]]
private def plan : PubSeg :=
  { bus := 14, send := true, width := 2, countAt := 0, start := 0,
    msgPrefix := [7], indexBase := some 300 }
private def packed := ZkFormal.Udr.pubOf Fp (encode [99,98] blocks)
#guard packed.length = 31
#guard (descriptor plan 2 0).count packed = 0
#guard (descriptor plan 2 1).count packed = 2
#guard (descriptor plan 2 1).startOffset packed = 26
#guard (descriptor plan 2 2).startOffset packed = 30
#guard ((descriptor plan 2 1).msgs packed).map (·.map Fp.toNat) =
  [[7,300,11,22],[7,301,11,22]]
#guard (descriptor plan 2 0).msgs packed = []
#guard (descriptor plan 2 1).fits 31 packed = true
#guard (descriptor plan 2 1).fits 29 packed = false

/-- info: 'ZkFormal.NearV3.Public.descriptor_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Public.descriptor_count
/-- info: 'ZkFormal.NearV3.Public.descriptor_offset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Public.descriptor_offset
/-- info: 'ZkFormal.NearV3.Public.descriptor_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Public.descriptor_record
/-- info: 'ZkFormal.NearV3.Public.descriptor_msgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Public.descriptor_msgs
/-- info: 'ZkFormal.NearV3.Public.descriptor_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Public.descriptor_fits

#guard (bodyPayload [0,0,0,0,1,0,0,0,255]) = [[255]]
#guard (bodyPayload [0,0]) = []
#guard (recordValues bodyPlan 300 [255]).map Fp.toNat = [2,308,255]
private def sources : List NearSpecV3.SrcList :=
  [⟨[1],0,List.replicate 32 7⟩,⟨[2],0,List.replicate 32 8⟩,⟨[1],0,List.replicate 32 7⟩]
#guard sourceDup sources 0 = false
#guard sourceDup sources 1 = false
#guard sourceDup sources 2 = true
#guard (sourcePayload sources).length = 3
/-- info: 'ZkFormal.NearV3.Public.descriptor_body_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Public.descriptor_body_record
/-- info: 'ZkFormal.NearV3.Public.descriptor_source_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Public.descriptor_source_record

#guard boundaryRow [(some [97],some [122]),(none,none)] 0 = [97,122,0]
#guard boundaryRow [(some [97],some [122]),(none,none)] 64 = [0,0,0]
#guard boundaryRow [(some [97],some [122]),(none,none)] 65 = [0,0,1]
#guard (boundaryPayload [(none,none)]).length = 65
#guard natPayload [[0,255]] = [[0,255]]
/-- info: 'ZkFormal.NearV3.Public.headerBytes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Public.headerBytes_length
/-- info: 'ZkFormal.NearV3.Public.header_body_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Public.header_body_length
/-- info: 'ZkFormal.NearV3.Public.header_witness_overhead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Public.header_witness_overhead
/-- info: 'ZkFormal.NearV3.Public.descriptor_boundary_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Public.descriptor_boundary_record
/-- info: 'ZkFormal.NearV3.Public.descriptor_nat_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Public.descriptor_nat_record
