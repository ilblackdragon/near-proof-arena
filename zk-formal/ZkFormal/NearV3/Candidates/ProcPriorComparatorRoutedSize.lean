import ZkFormal.NearV3.Candidates.ProcPriorComparatorRoutedDegree
namespace ZkFormal.NearV3.Candidates.ProcPriorComparatorRoutedFamily
open ZkFormal.Air ZkFormal.Size
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem rest_shapes : (HorizontalAccounts.rest.map InteractionTriples.table).map (shapeOf 3)=
  [⟨73,4,7,4,11⟩,⟨56,2,7,2,21⟩,⟨272,2,7,2,21⟩,⟨137,2,3,2,20⟩,
   ⟨77,4,7,4,20⟩,⟨16,5,7,5,17⟩,⟨7,2,5,2,16⟩,⟨6,2,5,2,13⟩,
   ⟨33,1,3,1,2⟩,⟨60,3,7,3,19⟩,⟨49,1,3,1,18⟩] := by decide +kernel

theorem shapes : tables.map (shapeOf 3)=
  [⟨3402,90,7,90,22⟩,⟨73,4,7,4,11⟩,⟨56,2,7,2,21⟩,⟨272,2,7,2,21⟩,
   ⟨137,2,3,2,20⟩,⟨77,4,7,4,20⟩,⟨16,5,7,5,17⟩,⟨7,2,5,2,16⟩,
   ⟨6,2,5,2,13⟩,⟨33,1,3,1,2⟩,⟨60,3,7,3,19⟩,⟨49,1,3,1,18⟩] := by
  change shapeOf 3 fused::(HorizontalAccounts.rest.map InteractionTriples.table).map (shapeOf 3)=_
  rw [fused_shape,rest_shapes]

theorem bytes_exact : bytes=8238324 := by
  unfold bytes
  rw [shapes]
  decide +kernel

theorem model_exact : sizeMaxDedup air (ZkFormal.V2.G.pg 3)=8238324 := by
  rw [sizeMaxDedup_eq_model]
  exact bytes_exact

theorem proof_bound : sizeMaxDedup air (ZkFormal.V2.G.pg 3)<8388608 := by
  rw [model_exact]
  decide +kernel

theorem headroom : 8388608-bytes=150284 := by rw [bytes_exact]
end ZkFormal.NearV3.Candidates.ProcPriorComparatorRoutedFamily
