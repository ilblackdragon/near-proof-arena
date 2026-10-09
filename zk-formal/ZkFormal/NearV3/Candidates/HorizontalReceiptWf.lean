import ZkFormal.NearV3.Candidates.HorizontalReceipt

namespace ZkFormal.NearV3.Candidates.HorizontalReceiptWf
open ZkFormal.Air ZkFormal.Size HorizontalReceipt HorizontalProfile
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem table_wf : air.tables.all (fun T=>T.wf air 16)=true := by
  change (HorizontalTables.fuse selected :: HorizontalAccounts.rest).all _=true
  rw [List.all_cons]
  rw [Bool.and_eq_true]
  constructor
  · apply HorizontalWf.fuse_wf
    intro T hT
    rcases List.mem_or_eq_of_mem_set hT with ho|rfl
    · have hT' := (List.mem_filter.mp ho).1
      have ht := List.all_eq_true.mp PackedMerkleFamily.four_wf T hT'
      simp only [Table.wf,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at ht ⊢
      exact ⟨⟨⟨⟨ht.1.1.1.1,ht.1.1.1.2⟩,by intro e he;have h:=ht.1.1.2 e he;omega⟩,ht.1.2⟩,ht.2⟩
    · decide +kernel
  · exact HorizontalCertified.rest_wf

theorem mult_bound : air.multBound=921280516 := by
  unfold Air.multBound
  simp only [air,tables,List.map_cons,List.sum_cons,mult_weights,fuse_profiles,profiles_equal]
  decide +kernel

theorem fp_bound : air.fpBound=53434269928 := by
  unfold Air.fpBound
  simp only [air,tables,List.map_cons,List.sum_cons,List.flatMap_cons,
    interaction_count,msg_lengths,fuse_profiles,profiles_equal]
  decide +kernel

theorem air_wf : air.wf 16=true := by
  simp only [Air.wf,table_wf,mult_bound,fp_bound,busBudget]
  decide +kernel

theorem grouped_degree : air.tables.all (fun T=>decide (T.degree 2≤16))=true := by
  change (HorizontalTables.fuse selected :: HorizontalAccounts.rest).all _=true
  rw [List.all_cons,fused_degree]
  decide +kernel

/-- Structural verifier header admission for the actual repaired receipt family.
This does not assert a complete execution witness or global bus conservation. -/
theorem header_max : ZkFormal.Stark.headerOk air (ZkFormal.V2.G.pg 2)
    (tables.map (·.maxLog))=true := by
  unfold ZkFormal.Stark.headerOk
  have hbl : 2^(ZkFormal.V2.G.pg 2).logBlowup=16 := rfl
  have hgr : (ZkFormal.V2.G.pg 2).auxGroup=2 := rfl
  simp only [hbl,hgr]
  rw [air_wf,grouped_degree]
  decide +kernel
end ZkFormal.NearV3.Candidates.HorizontalReceiptWf
