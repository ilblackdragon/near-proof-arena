import ZkFormal.NearV3.Candidates.ProcPriorRoutedHeadView
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedParent
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.Near
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem node_count (tr:Trace Fp) (pub msg:List Fp) (dir:Bool) :
    tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_PARENT dir msg=
      tableBusCount NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub B_PARENT dir msg := by
  change tableBusCount (InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions) _ _ _ _ _ _=_
  rw [InteractionTriples.count]
  change tableBusCount (InteractionPairing.reorder ProcPriorComparatorRoutedFamily.raw.interactions) _ _ _ _ _ _=_
  rw [InteractionPairing.count,ProcPriorRoutedVParent.filter_count]
  have hraw:ProcPriorComparatorRoutedFamily.raw.interactions.filter
      (fun i=>i.bus==B_PARENT && i.send==dir)=
      [HorizontalTables.interaction ProcPriorRoutedNodeView.offset (NodeV3.interactions[if dir then 4 else 5]!)] := by cases dir <;> rfl
  have hbase:NodeV3.interactions.filter (fun i=>i.bus==B_PARENT && i.send==dir)=
      [NodeV3.interactions[if dir then 4 else 5]!] := by cases dir <;> rfl
  rw [hraw,ProcPriorRoutedVParent.filter_count NodeV3.interactions,hbase]
  exact HorizontalTraffic.count_map (HorizontalTables.expression ProcPriorRoutedNodeView.offset)
    [NodeV3.interactions[if dir then 4 else 5]!] tr (ProcPriorRoutedNodeView.node tr) 0 pub B_PARENT dir msg rfl
    (by intro r i hi e he;exact HorizontalTrace.expression_eval tr 0 r ProcPriorRoutedNodeView.offset pub e)

theorem tail_absent :((ProcPriorComparatorRoutedFamily.tables.drop 2).all
    (fun T=>T.interactions.all (fun i=>i.bus != B_PARENT)))=true := by decide +kernel

theorem global_count {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) (dir:Bool) (msg:List Fp) :
    busCount AP.toAir tr pub B_PARENT dir msg=
      tableBusCount NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub B_PARENT dir msg+
      tableBusCount HeadV3.interactions tr 1 pub B_PARENT dir msg := by
  have htail:busCount.go tr pub B_PARENT dir msg (ProcPriorComparatorRoutedFamily.tables.drop 2) 2=0 := by
    apply busCount_go_zero
    intro t ht
    apply tableBusCount_zero
    intro i hi hb
    have hmem:(ProcPriorComparatorRoutedFamily.tables.drop 2)[t]!∈ProcPriorComparatorRoutedFamily.tables.drop 2 := by
      rw [getElem!_pos (ProcPriorComparatorRoutedFamily.tables.drop 2) t ht]
      exact List.getElem_mem ht
    have hh:=List.all_eq_true.mp (List.all_eq_true.mp tail_absent _ hmem) i hi
    have hn:i.bus≠B_PARENT := by simpa using hh
    exact (hn hb).elim
  unfold busCount
  change busCount.go tr pub B_PARENT dir msg AP.tables 0=_
  rw [htables]
  change tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_PARENT dir msg+
    (tableBusCount (InteractionTriples.table HeadV3.table).interactions tr 1 pub B_PARENT dir msg+
      busCount.go tr pub B_PARENT dir msg (ProcPriorComparatorRoutedFamily.tables.drop 2) 2)=_
  rw [htail,Nat.add_zero,node_count]
  change _+tableBusCount (InteractionTriples.reorder HeadV3.interactions) tr 1 pub B_PARENT dir msg=_
  rw [InteractionTriples.count]

/-- Actual PARENT conservation includes exactly Node children plus Head
roots, and the actual Node receivers. -/
theorem balance {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_PARENT)
    {vs:List NodeS3} {hs:List HeadE}
    (hN:ZkFormal.Near.TableTraffic NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub (nodeTraffic3 vs))
    (hHead:ZkFormal.Near.TableTraffic HeadV3.interactions tr 1 pub (headTraffic hs)) :
    Link3.ParentBal vs hs := by
  intro msg
  have hp (dir:Bool):pubCount AP pub B_PARENT dir msg=0 :=
    pubCount_zero (fun seg hseg hb=>absurd hb (hpub seg hseg)) msg
  have hh:=hH.balance B_PARENT msg
  rw [global_count htables true,global_count htables false,hp true,hp false,Nat.add_zero,Nat.add_zero] at hh
  rw [(hN _ _).1,(hHead _ _).1,(hN _ _).2,(hHead _ _).2] at hh
  have he:headRecvs hs B_PARENT=[] := by simp [headRecvs,B_PARENT,B_DIGEST,B_ROOT,B_EDGE]
  change _+_= _+(headRecvs hs B_PARENT |>.map ZkFormal.Near.Msg.toFp).count msg at hh
  rw [he,List.map_nil,List.count_nil,Nat.add_zero] at hh
  change ((nodeSends3 vs B_PARENT++headSends hs B_PARENT).map ZkFormal.Near.Msg.toFp).count msg=_
  rw [List.map_append,List.count_append]
  exact hh
end ZkFormal.NearV3.Candidates.ProcPriorRoutedParent
