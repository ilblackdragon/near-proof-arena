import ZkFormal.NearV3.Rcpt.Candidates.CompactWalkInventory

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
set_option maxRecDepth 16384
set_option maxHeartbeats 800000
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen Render.UpsRelay UpsRows

/-- Full fixed-log22 compact walk-bus traffic, including all part and padding
rows. Unlike the old UPS bridge, this uses the actual compact table/renderer. -/
theorem compact_physical_walk_count_at_log (Is : List UpsInst) (L : Nat) (hR : compactR Is≤2^L)
    (t : Nat) (pub : List Fp) (bus : Nat) (hb : bus=B_EDGE ∨ bus=B_BMAP)
    (sd : Bool) (msg : List Fp) :
    tableBusCount compactTable.interactions (Candidates.CompactPhysicalShaBytes.trace Is L) t pub bus sd msg=
      ((upsWalkMessages Is bus sd).map Msg.toFp).count msg := by
  rw [tableBusCount_eq]
  have he : (List.range ((Candidates.CompactPhysicalShaBytes.trace Is L).height t)).flatMap
      (fun r=>rowTraffic compactTable.interactions (Candidates.CompactPhysicalShaBytes.trace Is L) t r pub bus sd)=
      (upsWalkMessages Is bus sd).map Msg.toFp := by
    simp only [show compactTable.interactions=compactInteractions from rfl,
      Extract.rowTraffic_compact,←List.map_flatMap]
    congr 1
    change (List.range (2^L)).flatMap _=_
    rw [show 2^L=compactR Is+(2^L-compactR Is) by omega,List.range_add,List.flatMap_append]
    have hz : (List.range (2^L-compactR Is)).flatMap (fun r=>
        compactMsgs (rowC (Candidates.CompactPhysicalShaBytes.trace Is L) t (compactR Is+r))
          (rowC (Candidates.CompactPhysicalShaBytes.trace Is L) t
            ((compactR Is+r+1)%(Candidates.CompactPhysicalShaBytes.trace Is L).height t)) bus sd)=[] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro r hr
      have hC : rowC (Candidates.CompactPhysicalShaBytes.trace Is L) t (compactR Is+r)=(fun _=>0) := by
        funext x
        simp [rowC,cv,Candidates.CompactPhysicalShaBytes.trace,compactCell,show ¬compactR Is+r<compactR Is by omega]
        rfl
      rw [hC,compact_padding_silent _ bus hb sd]
    simp only [List.flatMap_map]
    rw [hz,List.append_nil]
    have hc : (List.range (compactR Is)).flatMap (fun r=>
        compactMsgs (rowC (Candidates.CompactPhysicalShaBytes.trace Is L) t r)
          (rowC (Candidates.CompactPhysicalShaBytes.trace Is L) t
            ((r+1)%(Candidates.CompactPhysicalShaBytes.trace Is L).height t)) bus sd)=
        (List.range (compactR Is)).flatMap (fun r=>compactMsgs
          (compactGeneratedRow Is 0 ((compactRecs Is).getD r default)) (fun _=>0) bus sd) := by
      apply UpsRows.flatMap_congr'
      intro r hr
      have hlt:=List.mem_range.mp hr
      have hC : rowC (Candidates.CompactPhysicalShaBytes.trace Is L) t r=
          compactGeneratedRow Is r ((compactRecs Is).getD r default) := by
        funext x
        simp only [rowC,cv,Candidates.CompactPhysicalShaBytes.trace,compactCell,hlt,ite_true,compactGeneratedRow]
      rw [hC]
      exact compact_row_independent Is _ (compact_get_mem hlt) r _ bus hb sd
    rw [hc]
    have hm : (List.range (compactR Is)).map (fun r=>(compactRecs Is).getD r default)=compactRecs Is := by
      rw [←compactRecs_length]
      apply List.ext_getElem (by simp)
      intro i hi hj
      simp only [List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj,Option.getD_some]
    have hh:=congrArg (fun xs=>xs.flatMap (fun rr=>compactMsgs (compactGeneratedRow Is 0 rr) (fun _=>0) bus sd)) hm
    simp only [List.flatMap_map] at hh
    exact hh.trans (compact_walk_inventory Is bus hb sd)
  rw [he]

theorem compact_physical_walk_count (Is : List UpsInst) (hR : compactR Is≤2^22)
    (t : Nat) (pub : List Fp) (bus : Nat) (hb : bus=B_EDGE ∨ bus=B_BMAP)
    (sd : Bool) (msg : List Fp) :
    tableBusCount compactTable.interactions (Candidates.CompactHeight.trace Is) t pub bus sd msg=
      ((upsWalkMessages Is bus sd).map Msg.toFp).count msg :=
  compact_physical_walk_count_at_log Is 22 hR t pub bus hb sd msg

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
