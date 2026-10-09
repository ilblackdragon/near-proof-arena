import ZkFormal.NearV3.Candidates.ProcessRepairForestDigest
namespace ZkFormal.NearV3.Candidates.ProcessRepairForestRequests
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
set_option maxRecDepth 32768

theorem head {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr) {hs:List HeadE}
    (hT:TableTraffic HeadV3.interactions tr 1 pub (headTraffic hs))
    {m:Msg} (hm:m∈headRecvs hs B_DIGEST) :
    ∃r,r<tr.height 1 ∧ ∃i∈AP.tables[1]!.interactions,
      i.bus=B_DIGEST ∧ i.send=false ∧ i.msgVal tr 1 r pub=m.toFp ∧ i.multNat tr 1 r pub≠0 := by
  have hc:0<(headRecvs hs B_DIGEST |>.map Msg.toFp).count m.toFp:=
    List.count_pos_iff.mpr (List.mem_map.mpr ⟨m,hm,rfl⟩)
  have he:(AP.tables[1]!).interactions=InteractionTriples.reorder HeadV3.interactions:=by rw [view.wires];rfl
  have hp:tableBusCount (AP.tables[1]!).interactions tr 1 pub B_DIGEST false m.toFp≠0:=by
    rw [he,InteractionTriples.count,(hT _ _).2]
    exact Nat.ne_of_gt hc
  exact exists_of_tableBusCount hp

theorem node_routed {i:Interaction} (hb:i.bus=B_DIGEST):ProcPriorRoutedNodeView.routed i=i := by
  simp [ProcPriorRoutedNodeView.routed,Rcpt.Candidates.SizeCount.withCount,
    ProcPriorComparatorRoutedFamily.route,hb,B_DIGEST,B_SIZE]

theorem node {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr) {vs:List NodeS3}
    (hT:TableTraffic NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub (nodeTraffic3 vs))
    {m:Msg} (hm:m∈nodeRecvs3 vs B_DIGEST) :
    ∃r,r<tr.height 0 ∧ ∃i∈AP.tables[0]!.interactions,
      i.bus=B_DIGEST ∧ i.send=false ∧ i.msgVal tr 0 r pub=m.toFp ∧ i.multNat tr 0 r pub≠0 := by
  have hc:0<(nodeRecvs3 vs B_DIGEST |>.map Msg.toFp).count m.toFp:=
    List.count_pos_iff.mpr (List.mem_map.mpr ⟨m,hm,rfl⟩)
  have hp:tableBusCount NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub B_DIGEST false m.toFp≠0:=by
    rw [(hT _ _).2];exact Nat.ne_of_gt hc
  obtain ⟨r,hr,i,hi,hb,hs,he,hm⟩:=exists_of_tableBusCount hp
  have him:ProcPriorRoutedNodeView.interaction i∈AP.tables[0]!.interactions:=by
    rw [view.wires];exact ProcPriorRoutedNodeView.member hi
  have hir:ProcPriorRoutedNodeView.interaction i=HorizontalTables.interaction ProcPriorRoutedNodeView.offset i:=by
    unfold ProcPriorRoutedNodeView.interaction;rw [node_routed hb]
  refine ⟨r,hr,_,him,?_,?_,?_,?_⟩
  · rw [hir];exact hb
  · rw [hir];exact hs
  · rw [hir]
    change (i.msg.map (HorizontalTables.expression ProcPriorRoutedNodeView.offset)).map
      (fun e=>e.eval tr 0 r pub)=_
    rw [List.map_map]
    simpa only [Function.comp_def,HorizontalTrace.expression_eval,Interaction.msgVal,ProcPriorRoutedNodeView.node] using he
  · rw [hir]
    change Interaction.multNat.go tr 0 r pub (i.mult.map (HorizontalTables.expression ProcPriorRoutedNodeView.offset)) 0≠0
    rw [HorizontalTraffic.mult_map _ _ tr (ProcPriorRoutedNodeView.node tr) 0 r 0 pub
      (by intro e he;exact HorizontalTrace.expression_eval tr 0 r _ pub e)]
    exact hm
end ZkFormal.NearV3.Candidates.ProcessRepairForestRequests
