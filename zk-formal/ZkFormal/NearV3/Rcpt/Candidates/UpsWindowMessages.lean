import ZkFormal.NearV3.Rcpt.Candidates.UpsWindowRanks

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Render.UpsRelay

def physicalWindowMessages (tr : Trace Fp) (t : Nat) (sd : Bool) : List Msg :=
  (List.range (tr.height t)).flatMap (fun r=>if tr.cell t r UpsV3.rd=1 then
    [physicalWindowKey tr t r++[if sd then physicalWindowRank tr t r+1 else physicalWindowRank tr t r]] else [])

def physicalWindowRows (tr : Trace Fp) (t : Nat) : List Nat :=
  (List.range (tr.height t)).filter (fun r=>decide (tr.cell t r UpsV3.rd=1))

theorem physicalWindowKey_toFp (tr : Trace Fp) (t r : Nat) :
    Msg.toFp (physicalWindowKey tr t r)=windowFieldKey tr t r := by
  simp [Msg.toFp,physicalWindowKey,List.map_map,Function.comp_def,Fp.ofNat_toNat]

/-- Exact whole-table UPB traffic after assigning actual prefix ranks. -/
theorem patched_window_count (tr : Trace Fp) (t : Nat) (pub : List Fp) (sd : Bool) (msg : List Fp) :
    tableBusCount compactTable.interactions
      (patchWindowCounters tr t (physicalWindowRank tr t)) t pub B_UPB sd msg=
      ((physicalWindowMessages tr t sd).map Msg.toFp).count msg := by
  rw [tableBusCount_eq]
  congr 1
  rw [physicalWindowMessages,List.map_flatMap]
  apply UpsRows.flatMap_congr'
  intro r hr
  change rowTraffic compactInteractions _ _ _ _ _ _=_
  rw [patched_window_row]
  by_cases h : tr.cell t r UpsV3.rd=1
  · simp only [h,ite_true,List.map_cons,List.map_nil]
    congr 1
    simp only [Msg.toFp,List.map_append,List.map_cons,List.map_nil]
    rw [show List.map Fp.ofNat (physicalWindowKey tr t r)=windowFieldKey tr t r from physicalWindowKey_toFp tr t r]
    cases sd <;> simp
  · simp [h]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
