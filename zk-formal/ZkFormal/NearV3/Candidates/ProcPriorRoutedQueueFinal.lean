import ZkFormal.NearV3.Candidates.ProcPriorRoutedKeyBalance
import ZkFormal.NearV3.Qv.Extract.BalancedFinal
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedQueueFinal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem sender_table {AP:AirP} (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    {t:Nat} (ht:t<AP.tables.length) {i:Interaction} (hi:i∈AP.tables[t]!.interactions)
    (hb:i.bus=B_FINAL) (hs:i.send=true) : t=2 := by
  have hall:((ProcPriorComparatorRoutedFamily.tables.zipIdx).all (fun p=>p.1.interactions.all
    (fun j=> !(j.bus==B_FINAL && j.send) || p.2==2)))=true:=by decide +kernel
  rw [htables] at ht hi
  have hm:(ProcPriorComparatorRoutedFamily.tables[t],t)∈ProcPriorComparatorRoutedFamily.tables.zipIdx:=by
    apply List.mem_iff_getElem?.mpr
    exact ⟨t,by simp [List.getElem?_zipIdx,List.getElem?_eq_getElem ht]⟩
  have hh:=List.all_eq_true.mp (List.all_eq_true.mp hall _ hm) i (by simpa only [getElem!_pos ProcPriorComparatorRoutedFamily.tables t ht] using hi)
  simpa [hb,hs] using hh

theorem query_walk {AP:AirP} {pub msg:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:pubCount AP pub B_FINAL true msg=0)
    {ws:List WalkR} (hW:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws))
    (hc:0<tableBusCount Qv.Candidates.KeyTrafficRepair.interactions (ProcPriorRoutedKeyView.key tr) 0 pub B_FINAL false msg) :
    ∃w∈ws,Msg.toFp [w.w,w.tau,w.fk,w.k]=msg := by
  obtain ⟨r,hr,i,hi,hb,hs,he,hm⟩:=exists_of_tableBusCount (Nat.ne_of_gt hc)
  have hir:ProcPriorRoutedKeyView.routed i=i:=by
    unfold ProcPriorRoutedKeyView.routed ProcPriorComparatorRoutedFamily.route
    rw [if_neg (by rw [hb];decide)]
  have hmem:ProcPriorRoutedKeyView.interaction i∈AP.tables[0]!.interactions:=by
    rw [htables];exact ProcPriorRoutedKeyView.member hi
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
  have ht:0<AP.tables.length:=by rw [htables];decide +kernel
  have hle:=busCount_go_ge tr pub B_FINAL false msg AP.tables 0 0 ht
  simp only [Nat.zero_add] at hle
  change _≤busCount AP.toAir tr pub B_FINAL false msg at hle
  have hh:=hH.balance B_FINAL msg
  rw [hpub,Nat.add_zero] at hh
  have hpos:busCount AP.toAir tr pub B_FINAL true msg≠0:=by omega
  obtain ⟨t,ht,hc⟩:=busCount_go_pos tr pub B_FINAL true msg AP.tables 0 hpos
  simp only [Nat.zero_add] at hc
  obtain ⟨rr,hrr,j,hj,hbj,hsj,hej,hmj⟩:=exists_of_tableBusCount hc
  have ht2:=sender_table htables ht hj hbj hsj
  subst t
  have hp:=ZkFormal.Chacha.tableBusCount_pos hrr hj hmj
  rw [hbj,hsj,hej,htables] at hp
  have hp:=Nat.pos_of_ne_zero hp
  change 0<tableBusCount (InteractionTriples.reorder WalkV3.interactions) tr 2 pub B_FINAL true msg at hp
  rw [InteractionTriples.count,(hW B_FINAL msg).1,List.count_pos_iff,List.mem_map] at hp
  obtain ⟨m,hm,he⟩:=hp
  change m∈walkSends3 ws B_FINAL at hm
  simp only [walkSends3,show B_FINAL≠B_EDGE by decide,show B_FINAL≠B_BMAP by decide,ite_false,ite_true,List.mem_map] at hm
  obtain ⟨w,hw,rfl⟩:=hm
  exact ⟨w,hw,he⟩
theorem requested_walk {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀msg,pubCount AP pub B_FINAL true msg=0)
    {ws:List WalkR} (hW:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws))
    (q:Qv.Extract.WalkChain (ProcPriorRoutedKeyView.key tr) 0) (i:Nat) (hi:i<q.segs.length) :
    ∃w∈ws,Msg.toFp [w.w,w.tau,w.fk,w.k]=Qv.Extract.finalMessage (ProcPriorRoutedKeyView.key tr) 0 q.segs[i].1 pub := by
  apply query_walk hH htables (hpub _) hW
  rw [ZkFormal.Near.tableBusCount_eq,List.count_pos_iff,
    Qv.Extract.repaired_final_physical (ProcPriorRoutedKeyView.local_key hH htables) q]
  exact List.mem_map.mpr ⟨q.segs[i],List.getElem_mem hi,rfl⟩
end ZkFormal.NearV3.Candidates.ProcPriorRoutedQueueFinal
