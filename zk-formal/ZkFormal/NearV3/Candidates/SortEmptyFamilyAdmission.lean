import ZkFormal.NearV3.Candidates.SortEmptyFamilyBounds
namespace ZkFormal.NearV3.Candidates.SortEmptyFamily
open ZkFormal.Air ZkFormal.Size HorizontalProfile
open ProcPriorCodecActualFamily (fused)
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem air_wf : air.wf 16=true := by
  change (tables.all (fun T=>T.wf air 16) && decide (air.multBound≤busBudget) && decide (air.fpBound≤busBudget))=true
  rw [tables_wf,mult_bound,fp_bound]
  decide +kernel

theorem grouped_degree : air.tables.all (fun T=>decide (T.degree 3≤16))=true := by
  change (fused::rest.map InteractionTriples.table).all _=true
  rw [List.all_cons,ProcPriorCodecActualFamily.fused_degree]
  apply List.all_eq_true.mpr
  intro T hT
  obtain ⟨U,hU,rfl⟩:=List.mem_map.mp hT
  rcases List.mem_or_eq_of_mem_set hU with hU|rfl
  · have hh:=List.all_eq_true.mp ProcPriorCodecActualFamily.grouped_degree
      (InteractionTriples.table U) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨U,hU,rfl⟩))
    exact hh
  · decide +kernel

theorem header_max : ZkFormal.Stark.headerOk air (ZkFormal.V2.G.pg 3)
    (tables.map (·.maxLog))=true := by
  unfold ZkFormal.Stark.headerOk
  have hbl : 2^(ZkFormal.V2.G.pg 3).logBlowup=16 := rfl
  have hgr : (ZkFormal.V2.G.pg 3).auxGroup=3 := rfl
  simp only [hbl,hgr]
  rw [air_wf,grouped_degree]
  decide +kernel


end ZkFormal.NearV3.Candidates.SortEmptyFamily
