import ZkFormal.NearV3.Candidates.ProcessRepairKeyBalance
import ZkFormal.NearV3.Candidates.ProcPriorRoutedQueueFinal
namespace ZkFormal.NearV3.Candidates.ProcessRepairQueueFinal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
theorem query_walk {AP:AirP} {pub msg:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:pubCount AP pub B_FINAL true msg=0)
    {ws:List WalkR} (hW:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws))
    (hc:0<tableBusCount Qv.Candidates.KeyTrafficRepair.interactions (ProcPriorRoutedKeyView.key tr) 0 pub B_FINAL false msg) :
    ∃w∈ws,Msg.toFp [w.w,w.tau,w.fk,w.k]=msg := by
  obtain ⟨r,hr,i,hi,hb,hs,he,hm⟩:=exists_of_tableBusCount (Nat.ne_of_gt hc)
  have hir:ProcPriorRoutedKeyView.routed i=i:=by
    unfold ProcPriorRoutedKeyView.routed ProcPriorComparatorRoutedFamily.route
    rw [if_neg (by rw [hb];decide)]
  have hmem:ProcPriorRoutedKeyView.interaction i∈AP.tables[0]!.interactions:=by
    rw [view.wires];exact ProcPriorRoutedKeyView.member hi
  have hmult:(ProcPriorRoutedKeyView.interaction i).multNat tr 0 r pub=i.multNat (ProcPriorRoutedKeyView.key tr) 0 r pub:=by
    unfold ProcPriorRoutedKeyView.interaction
    rw [hir]
    exact HorizontalTraffic.mult_map _ _ tr (ProcPriorRoutedKeyView.key tr) 0 r 0 pub
      (by intro e he;exact HorizontalTrace.expression_eval tr 0 r _ pub e)
  have hmsg:(ProcPriorRoutedKeyView.interaction i).msgVal tr 0 r pub=msg:=by
    unfold ProcPriorRoutedKeyView.interaction
    rw [hir]
    change (i.msg.map (HorizontalTables.expression ProcPriorRoutedKeyView.offset)).map
      (fun e=>e.eval tr 0 r pub)=_
    rw [List.map_map]
    simpa only [Function.comp_def,HorizontalTrace.expression_eval,Interaction.msgVal,ProcPriorRoutedKeyView.key] using he
  have hbus:(ProcPriorRoutedKeyView.interaction i).bus=B_FINAL:=by
    unfold ProcPriorRoutedKeyView.interaction;rw [hir];exact hb
  have hsend:(ProcPriorRoutedKeyView.interaction i).send=false:=by
    unfold ProcPriorRoutedKeyView.interaction;rw [hir];exact hs
  have hr0:r<tr.height 0:=hr
  have hp:=ZkFormal.Chacha.tableBusCount_pos (tr:=tr) (pub:=pub) hr0 hmem (by rw [hmult];exact hm)
  rw [hbus,hsend,hmsg] at hp
  have ht:0<AP.tables.length:=by rw [view.length];decide +kernel
  have hle:=busCount_go_ge tr pub B_FINAL false msg AP.tables 0 0 ht
  simp only [Nat.zero_add] at hle
  change _≤busCount AP.toAir tr pub B_FINAL false msg at hle
  have hh:=view.valid.balance B_FINAL msg
  rw [hpub,Nat.add_zero] at hh
  have hpos:busCount AP.toAir tr pub B_FINAL true msg≠0:=by omega
  obtain ⟨t,ht,hc⟩:=busCount_go_pos tr pub B_FINAL true msg AP.tables 0 hpos
  simp only [Nat.zero_add] at hc
  obtain ⟨rr,hrr,j,hj,hbj,hsj,hej,hmj⟩:=exists_of_tableBusCount hc
  have ht2:=ProcPriorRoutedQueueFinal.sender_table (AP:=ProcessRepairBalance.reference AP) rfl (by simpa only [ProcessRepairBalance.reference,view.length] using ht) (by simpa only [view.wires,ProcessRepairBalance.reference] using hj) hbj hsj
  subst t
  have hp:=ZkFormal.Chacha.tableBusCount_pos hrr hj hmj
  rw [hbj,hsj,hej,view.wires] at hp
  have hp:=Nat.pos_of_ne_zero hp
  change 0<tableBusCount (InteractionTriples.reorder WalkV3.interactions) tr 2 pub B_FINAL true msg at hp
  rw [InteractionTriples.count,(hW B_FINAL msg).1,List.count_pos_iff,List.mem_map] at hp
  obtain ⟨m,hm,he⟩:=hp
  change m∈walkSends3 ws B_FINAL at hm
  simp only [walkSends3,show B_FINAL≠B_EDGE by decide,show B_FINAL≠B_BMAP by decide,ite_false,ite_true,List.mem_map] at hm
  obtain ⟨w,hw,rfl⟩:=hm
  exact ⟨w,hw,he⟩
theorem requested_walk {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub B_FINAL true msg=0)
    {ws:List WalkR} (hW:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws))
    (q:Qv.Extract.WalkChain (ProcPriorRoutedKeyView.key tr) 0) (i:Nat) (hi:i<q.segs.length) :
    ∃w∈ws,Msg.toFp [w.w,w.tau,w.fk,w.k]=Qv.Extract.finalMessage (ProcPriorRoutedKeyView.key tr) 0 q.segs[i].1 pub := by
  apply query_walk view (hpub _) hW
  rw [ZkFormal.Near.tableBusCount_eq,List.count_pos_iff,
    Qv.Extract.repaired_final_physical (ProcessRepairKeyView.local_key view) q]
  exact List.mem_map.mpr ⟨q.segs[i],List.getElem_mem hi,rfl⟩
end ZkFormal.NearV3.Candidates.ProcessRepairQueueFinal
