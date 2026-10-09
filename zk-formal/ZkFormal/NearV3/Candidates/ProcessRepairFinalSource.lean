import ZkFormal.NearV3.Candidates.ProcessRepairQueueFinal
namespace ZkFormal.NearV3.Candidates.ProcessRepairFinalSource
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha

theorem received {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub B_FINAL true msg=0)
    {ws:List WalkR} (hW:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws))
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=B_FINAL) (hs:i.send=false)
    (hm:i.multNat tr t r pub≠0):
    ∃w∈ws,Msg.toFp [w.w,w.tau,w.fk,w.k]=i.msgVal tr t r pub:=by
  let msg:=i.msgVal tr t r pub
  have hp:=ZkFormal.Chacha.tableBusCount_pos (tr:=tr) (pub:=pub) hr hi hm
  rw [hb,hs] at hp
  change tableBusCount AP.tables[t]!.interactions tr t pub B_FINAL false msg≠0 at hp
  have hpub:=hpub msg
  have hle:=busCount_go_ge tr pub B_FINAL false msg AP.tables 0 t ht
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
end ZkFormal.NearV3.Candidates.ProcessRepairFinalSource
