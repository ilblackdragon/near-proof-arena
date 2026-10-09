import ZkFormal.NearV3.Candidates.ProcPriorRoutedKeySound
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedKeyBalance
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open Sched
open RcptV3Proof Assembly.ReceiptCandidateProof
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem global_recv {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) (msg:List Fp) :
    busCount AP.toAir tr pub B_KEYNIB false msg=tableBusCount WalkV3.interactions tr 2 pub B_KEYNIB false msg := by
  have hz (tr':Trace Fp) (t:Nat):tableBusCount [] tr' t pub B_KEYNIB false msg=0:=by
    apply tableBusCount_zero
    intro i hi
    simp at hi
  have hf:tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_KEYNIB false msg=0:=by
    rw [ProcPriorRoutedKeyCounts.fused_count]
    rw [ProcPriorRoutedVParent.filter_count RcptV3.interactions,
      ProcPriorRoutedVParent.filter_count Qv.Candidates.KeyTrafficRepair.interactions]
    change tableBusCount [] _ _ _ _ _ _+tableBusCount [] _ _ _ _ _ _=0
    rw [hz,hz]
  have hhead:tableBusCount (InteractionTriples.table HeadV3.table).interactions tr 1 pub B_KEYNIB false msg=0:=by
    change tableBusCount (InteractionTriples.reorder HeadV3.interactions) tr 1 pub B_KEYNIB false msg=0
    rw [InteractionTriples.count,ProcPriorRoutedVParent.filter_count]
    change tableBusCount [] _ _ _ _ _ _=0
    exact hz _ _
  have hall:((ProcPriorComparatorRoutedFamily.tables.drop 3).all
    (fun T=>T.interactions.all (fun i=>i.bus != B_KEYNIB)))=true:=by decide +kernel
  have ht:busCount.go tr pub B_KEYNIB false msg (ProcPriorComparatorRoutedFamily.tables.drop 3) 3=0:=by
    apply busCount_go_zero
    intro t ht
    apply tableBusCount_zero
    intro i hi hb
    have hm:(ProcPriorComparatorRoutedFamily.tables.drop 3)[t]!∈ProcPriorComparatorRoutedFamily.tables.drop 3:=by
      rw [getElem!_pos _ t ht];exact List.getElem_mem ht
    have hh:=List.all_eq_true.mp (List.all_eq_true.mp hall _ hm) i hi
    simpa [hb] using hh
  unfold busCount
  change busCount.go tr pub B_KEYNIB false msg AP.tables 0=_
  rw [htables]
  change tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_KEYNIB false msg+
    (tableBusCount (InteractionTriples.table HeadV3.table).interactions tr 1 pub B_KEYNIB false msg+
      (tableBusCount (InteractionTriples.table WalkV3.table).interactions tr 2 pub B_KEYNIB false msg+
        busCount.go tr pub B_KEYNIB false msg (ProcPriorComparatorRoutedFamily.tables.drop 3) 3))=_
  rw [hf,hhead,ht,Nat.zero_add,Nat.zero_add,Nat.add_zero]
  exact InteractionTriples.count _ tr 2 pub B_KEYNIB false msg

theorem balance {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_KEYNIB)
    {bs:List ListBlock} {e:Nat} (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e)
    {ws:List WalkR} (hW:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws)) :
    ((List.range (tr.height 0)).flatMap (fun r=>ZkFormal.Near.rowTraffic Qv.Candidates.KeyTrafficRepair.interactions
      (ProcPriorRoutedKeyView.key tr) 0 r pub B_KEYNIB true) ++
      (rcptSends3 pub (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)) B_KEYNIB).map Msg.toFp).Perm
      ((walkRecvs3 ws B_KEYNIB).map Msg.toFp) := by
  apply List.perm_iff_count.mpr
  intro msg
  have hp (dir:Bool):pubCount AP pub B_KEYNIB dir msg=0:=
    pubCount_zero (fun seg hs hb=>absurd hb (hpub seg hs)) msg
  have hh:=hH.balance B_KEYNIB msg
  rw [hp true,hp false,Nat.add_zero,Nat.add_zero,ProcPriorRoutedKeyCounts.global_count htables,
    global_recv htables,(hW B_KEYNIB msg).2] at hh
  have hL:=repaired_local_base (ProcPriorRoutedReceiptView.local_receipt hH htables)
  rw [(Assembly.ReceiptCandidateProof.ListChain.key_view_traffic hL hc msg).1,ZkFormal.Near.tableBusCount_eq] at hh
  simp only [List.count_append]
  change _=_ at hh
  simpa only [walkTraffic3,Nat.add_comm,ProcPriorRoutedKeyView.key,HorizontalTrace.project,Trace.height] using hh
end ZkFormal.NearV3.Candidates.ProcPriorRoutedKeyBalance
