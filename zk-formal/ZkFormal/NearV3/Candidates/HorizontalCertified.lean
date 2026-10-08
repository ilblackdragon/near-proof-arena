import ZkFormal.NearV3.Candidates.HorizontalAccounts
import ZkFormal.NearV3.Candidates.HorizontalAuxCheck
import ZkFormal.NearV3.Candidates.HorizontalWf
namespace ZkFormal.NearV3.Candidates.HorizontalCertified
open ZkFormal.Air ZkFormal.Size HorizontalAccounts HorizontalAuxCheck HorizontalProfile
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem shapes : tables.map (shapeOf 2)=
  [⟨3372,106,7,106,22⟩,⟨73,4,5,4,11⟩,⟨56,4,5,4,21⟩,⟨272,2,5,2,21⟩,
   ⟨137,2,3,2,20⟩,⟨77,4,6,4,20⟩,⟨16,7,5,7,17⟩,⟨7,2,5,2,16⟩,
   ⟨6,2,5,2,13⟩,⟨33,1,3,1,2⟩,⟨60,3,7,3,19⟩,⟨49,1,3,1,18⟩] := by
  simp only [tables,List.map_cons,fused_shape,rest_shapes]

theorem bytes_exact : bytes=8288148 := by
  unfold bytes
  rw [shapes]
  decide +kernel

theorem proof_bound : sizeMaxDedup air (ZkFormal.V2.G.pg 2)<8388608 := by
  rw [actual_model,bytes_exact]
  decide

theorem rest_wf : rest.all (fun T=>T.wf air 16)=true := by decide +kernel

theorem table_wf : air.tables.all (fun T=>T.wf air 16)=true := by
  change (HorizontalTables.fuse HorizontalTables.selected :: rest).all _=true
  rw [List.all_cons,rest_wf,Bool.and_true]
  apply HorizontalWf.fuse_wf
  intro T hT
  have hT' := (List.mem_filter.mp hT).1
  have ht := List.all_eq_true.mp PackedMerkleFamily.four_wf T hT'
  simp only [Table.wf,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at ht ⊢
  exact ⟨⟨⟨⟨ht.1.1.1.1,ht.1.1.1.2⟩,by intro e he; have h:=ht.1.1.2 e he; omega⟩,
    ht.1.2⟩,ht.2⟩

theorem mult_bound : air.multBound=921280516 := by
  unfold Air.multBound
  simp only [air,tables,List.map_cons,List.sum_cons,mult_weights,fuse_profiles]
  decide +kernel

theorem fp_bound : air.fpBound=53434269928 := by
  unfold Air.fpBound
  simp only [air,tables,List.map_cons,List.sum_cons,List.flatMap_cons,
    interaction_count,msg_lengths,fuse_profiles]
  decide +kernel

theorem air_wf : air.wf 16=true := by
  simp only [Air.wf,table_wf,mult_bound,fp_bound,busBudget]
  decide +kernel

theorem grouped_degree : air.tables.all (fun T=>decide (T.degree 2≤16))=true := by
  change (HorizontalTables.fuse HorizontalTables.selected :: rest).all _=true
  rw [List.all_cons,fused_degree]
  decide +kernel

theorem header_max : ZkFormal.Stark.headerOk air (ZkFormal.V2.G.pg 2)
    (tables.map (·.maxLog))=true := by
  unfold ZkFormal.Stark.headerOk
  have hbl : 2^(ZkFormal.V2.G.pg 2).logBlowup=16 := rfl
  have hgr : (ZkFormal.V2.G.pg 2).auxGroup=2 := rfl
  simp only [hbl,hgr]
  rw [air_wf,grouped_degree]
  decide +kernel
end ZkFormal.NearV3.Candidates.HorizontalCertified
