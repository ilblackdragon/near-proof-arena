import ZkFormal.V2.IndexedPublic
import ZkFormal.V2.Toy

open ZkFormal.V2 ZkFormal.Algebra

private def indexedSample : PubSeg :=
  { bus := 14, send := true, width := 2, countAt := 0, start := 4,
    msgPrefix := [7], indexBase := some 300 }
private def indexedBytes : List Fp := [2,0,0,0,11,22,33,44].map Fp.ofNat

-- An index above one byte is synthesized without truncation to UInt8.
#guard ((indexedSample.record indexedBytes 1).map Fp.toNat) = [7,301,33,44]
#guard indexedSample.messageWidth = 4
#guard indexedSample.count indexedBytes = 2
#guard indexedSample.fits 8 indexedBytes = true
#guard indexedSample.fits 7 indexedBytes = false
#guard (({ indexedSample with indexBase := none }.record indexedBytes 0).map Fp.toNat) = [7,11,22]
#guard (({ indexedSample with msgPrefix := [], indexBase := none }.record indexedBytes 0).map Fp.toNat) = [11,22]
-- Equal payloads at distinct positions still yield distinct messages.
private def repeatedBytes : List Fp := [2,0,0,0,11,22,11,22].map Fp.ofNat
#guard indexedSample.record repeatedBytes 0 ≠ indexedSample.record repeatedBytes 1
#guard ((indexedSample.msgs repeatedBytes).map (·.map Fp.toNat)) =
  [[7,300,11,22],[7,301,11,22]]

/-- info: 'ZkFormal.V2.PubSeg.record_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.V2.PubSeg.record_length
/-- info: 'ZkFormal.V2.PubSeg.record_plain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.V2.PubSeg.record_plain
/-- info: 'ZkFormal.V2.PubSeg.record_indexed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.V2.PubSeg.record_indexed
/-- info: 'ZkFormal.V2.pubIdx_of_segments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.V2.pubIdx_of_segments
/-- info: 'ZkFormal.V2.Toy.toyP_admission' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.V2.Toy.toyP_admission

private def dynamicSample : PubSeg :=
  { indexedSample with start := 999, countAt := 4, startAt := some 0 }
private def dynamicBytes : List Fp := [8,0,0,0,1,0,0,0,55,66].map Fp.ofNat
#guard ((dynamicSample.record dynamicBytes 0).map Fp.toNat) = [7,300,55,66]
#guard dynamicSample.startOffset dynamicBytes = 8
#guard dynamicSample.fits 10 dynamicBytes = true
#guard dynamicSample.fits 9 dynamicBytes = false
#guard dynamicSample.fits 100 ([99,0,0,0,1,0,0,0,55,66].map Fp.ofNat) = false
