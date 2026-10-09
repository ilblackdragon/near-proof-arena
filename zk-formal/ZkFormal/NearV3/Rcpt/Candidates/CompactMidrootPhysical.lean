import ZkFormal.NearV3.Rcpt.Candidates.UpsPhysicalPrefix
import ZkFormal.NearV3.Rcpt.Candidates.CompactMidrootInventory
import ZkFormal.NearV3.Rcpt.Candidates.CompactWalkPhysical

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
set_option maxRecDepth 16384
set_option maxHeartbeats 800000
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen Render.UpsRelay UpsRows

/-- Full fixed-log22 compact walk-bus traffic, including all part and padding
rows. Unlike the old UPS bridge, this uses the actual compact table/renderer. -/
theorem compact_physical_midroot_count_at_log (Is : List UpsInst) (L : Nat) (hR : compactR Is≤2^L)
    (hl : ∀I∈Is,I.mid.length=32) (t : Nat) (pub : List Fp) (msg : List Fp) :
    tableBusCount compactTable.interactions (Candidates.CompactPhysicalShaBytes.trace Is L) t pub B_MIDROOT false msg=
      (((Is.map (fun I=>[I.tau,I.rid]++I.mid)).map reduceMessage).map Msg.toFp).count msg := by
  rw [tableBusCount_eq]
  have he : (List.range ((Candidates.CompactPhysicalShaBytes.trace Is L).height t)).flatMap
      (fun r=>rowTraffic compactTable.interactions (Candidates.CompactPhysicalShaBytes.trace Is L) t r pub B_MIDROOT false)=
      ((Is.map (fun I=>[I.tau,I.rid]++I.mid)).map reduceMessage).map Msg.toFp := by
    simp only [show compactTable.interactions=compactInteractions from rfl,
      Extract.rowTraffic_compact,←List.map_flatMap]
    congr 1
    change (List.range (2^L)).flatMap _=_
    rw [show 2^L=compactR Is+(2^L-compactR Is) by omega,List.range_add,List.flatMap_append]
    have hz : (List.range (2^L-compactR Is)).flatMap (fun r=>
        compactMsgs (rowC (Candidates.CompactPhysicalShaBytes.trace Is L) t (compactR Is+r))
          (rowC (Candidates.CompactPhysicalShaBytes.trace Is L) t
            ((compactR Is+r+1)%(Candidates.CompactPhysicalShaBytes.trace Is L).height t)) B_MIDROOT false)=[] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro r hr
      have hC : rowC (Candidates.CompactPhysicalShaBytes.trace Is L) t (compactR Is+r)=(fun _=>0) := by
        funext x
        simp [rowC,cv,Candidates.CompactPhysicalShaBytes.trace,compactCell,show ¬compactR Is+r<compactR Is by omega]
        rfl
      rw [hC,compact_midroot_silent _ _ rfl]
    simp only [List.flatMap_map]
    rw [hz,List.append_nil]
    have hc : (List.range (compactR Is)).flatMap (fun r=>
        compactMsgs (rowC (Candidates.CompactPhysicalShaBytes.trace Is L) t r)
          (rowC (Candidates.CompactPhysicalShaBytes.trace Is L) t
            ((r+1)%(Candidates.CompactPhysicalShaBytes.trace Is L).height t)) B_MIDROOT false)=
        (List.range (compactR Is)).flatMap (fun r=>compactMsgs
          (compactGeneratedRow Is 0 ((compactRecs Is).getD r default)) (fun _=>0) B_MIDROOT false) := by
      apply UpsRows.flatMap_congr'
      intro r hr
      have hlt:=List.mem_range.mp hr
      have hC : rowC (Candidates.CompactPhysicalShaBytes.trace Is L) t r=
          compactGeneratedRow Is r ((compactRecs Is).getD r default) := by
        funext x
        simp only [rowC,cv,Candidates.CompactPhysicalShaBytes.trace,compactCell,hlt,ite_true,compactGeneratedRow]
      rw [hC]
      have hi:=(compact_mem.mp (compact_get_mem hlt)).1
      have hh : (inst Is ((compactRecs Is).getD r default).1).mid.length=32 := by
        apply hl
        change Is[((compactRecs Is).getD r default).1]?.getD default∈Is
        rw [List.getElem?_eq_getElem hi]
        exact List.getElem_mem hi
      rw [compact_midroot_row _ _ _ _ _ hh,compact_midroot_row _ _ _ _ _ hh]
    rw [hc]
    have hm : (List.range (compactR Is)).map (fun r=>(compactRecs Is).getD r default)=compactRecs Is := by
      rw [←compactRecs_length]
      apply List.ext_getElem (by simp)
      intro i hi hj
      simp only [List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj,Option.getD_some]
    have hh:=congrArg (fun xs=>xs.flatMap (fun rr=>compactMsgs (compactGeneratedRow Is 0 rr) (fun _=>0) B_MIDROOT false)) hm
    simp only [List.flatMap_map] at hh
    exact hh.trans (compact_midroot_inventory Is (fun _=>0) (fun _ _=>0) hl)
  rw [he]

theorem compact_physical_midroot_recv (Is : List UpsInst) (hR : compactR Is≤2^22)
    (hl : ∀I∈Is,I.mid.length=32) (t : Nat) (pub : List Fp) (msg : List Fp) :
    tableBusCount compactTable.interactions (Candidates.CompactHeight.trace Is) t pub B_MIDROOT false msg=
      ((Is.map (fun I=>[I.tau,I.rid]++I.mid)).map Msg.toFp).count msg := by
  have hh:=compact_physical_midroot_count_at_log Is 22 hR hl t pub msg
  simpa only [Candidates.CompactHeight.trace,Candidates.CompactPhysicalShaBytes.trace,reduceMessages_toFp] using hh

theorem compact_physical_midroot_send (tr : Trace Fp) (t : Nat) (pub : List Fp) (msg : List Fp) :
    tableBusCount compactTable.interactions tr t pub B_MIDROOT true msg=0 := by
  rw [tableBusCount_eq]
  have hz : (List.range (tr.height t)).flatMap
      (fun r=>rowTraffic compactTable.interactions tr t r pub B_MIDROOT true)=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    rw [show compactTable.interactions=compactInteractions from rfl,Extract.rowTraffic_compact,
      compact_midroot_send]
    rfl
  rw [hz]
  rfl

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
