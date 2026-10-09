import ZkFormal.NearV3.Candidates.ProcPriorComparatorRoutedSize
import ZkFormal.NearV3.Candidates.ProcPriorComparatorRoutedWf
namespace ZkFormal.NearV3.Candidates.ProcPriorComparatorRoutedFamily
open ZkFormal.Air HorizontalProfile
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

/-- Structural/proof-size certificate only. Native renderer installation,
new bus ownership and global honest balance are independent obligations. -/
theorem mult_bound : air.multBound=1038721028 := by
  unfold Air.multBound
  change ((fused::HorizontalAccounts.rest.map InteractionTriples.table).map _).sum=_
  simp only [List.map_cons,List.sum_cons,mult_weights,fused_profiles]
  decide +kernel

theorem fp_bound : air.fpBound=68697539256 := by
  unfold Air.fpBound
  change ((fused::HorizontalAccounts.rest.map InteractionTriples.table).map _).sum *
    (((fused::HorizontalAccounts.rest.map InteractionTriples.table).flatMap _).foldr max 0+1)=_
  simp only [List.map_cons,List.sum_cons,List.flatMap_cons,interaction_count,msg_lengths,fused_profiles]
  decide +kernel

theorem air_wf : air.wf 16=true := by
  simp only [Air.wf,tables_wf,mult_bound,fp_bound,busBudget]
  decide +kernel

theorem grouped_degree : air.tables.all (fun T=>decide (T.degree 3≤16))=true := by
  change (fused::HorizontalAccounts.rest.map InteractionTriples.table).all _=true
  rw [List.all_cons,fused_degree]
  decide +kernel

theorem header_max : ZkFormal.Stark.headerOk air (ZkFormal.V2.G.pg 3)
    (tables.map (·.maxLog))=true := by
  unfold ZkFormal.Stark.headerOk
  have hbl : 2^(ZkFormal.V2.G.pg 3).logBlowup=16 := rfl
  have hgr : (ZkFormal.V2.G.pg 3).auxGroup=3 := rfl
  simp only [hbl,hgr]
  rw [air_wf,grouped_degree]
  decide +kernel
/-- Remaining fingerprint budget for this exact family and its 57-word maximum
message. Any later interaction changes require recertification. -/
theorem fingerprint_headroom : 2^36-air.fpBound=21937480 := by
  rw [fp_bound]

theorem extra_padded_group_exceeds : 2^36<air.fpBound+3*2^22*58 := by
  rw [fp_bound]
  decide +kernel

end ZkFormal.NearV3.Candidates.ProcPriorComparatorRoutedFamily
