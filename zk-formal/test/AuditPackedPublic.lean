import ZkFormal.NearV3.Public.Records
import ZkFormal.NearV3.Public.Fits

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
