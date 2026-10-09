import ZkFormal.NearV3.Candidates.ProcessRepairAccountComplete
namespace ZkFormal.NearV3.Candidates.ProcessRepairAccountUnique
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open Qv.Extract
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem keys {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hv:ValWf es)
    (hT:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    {as:List AcctV} (ha:TableTraffic AcctV3.interactions tr 6 pub (acctV3Traffic as)):
    (((acctV3Sends as B_VBYTES).map Msg.toFp).map byteKey).Nodup:=by
  have hl:=Qv.Candidates.KeyTrafficRepair.local_to_base (ProcessRepairKeyView.local_key view)
  obtain ⟨q⟩:=walk_chain_exists hl
  obtain ⟨v⟩:=parser_chain_exists hl q
  obtain ⟨aks,_,hak⟩:=ProcessRepairQueueSuppliers.access_keys view
  let extra:List (List Fp):=(List.range (tr.height 0)).flatMap
    (fun r=>rowTraffic [ProcPriorRoutedRawBytes.bytes] tr 0 r pub B_VBYTES true)
  let qbytes:=v.segs.flatMap (fun p=>physicalRecordBytes (ProcPriorRoutedKeyView.key tr) 0 p.1 p.2 pub)
  let others:=qbytes++(akeySends aks B_VBYTES).map Msg.toFp++extra
  have hp:((acctV3Sends as B_VBYTES).map Msg.toFp++others).Perm ((valRecvs es B_VBYTES).map Msg.toFp):=by
    apply List.perm_iff_count.mpr
    intro msg
    have h:=ProcessRepairVbytesCounts.balance view hpub msg
    rw [(ha _ _).1,(hak _ _).1,(hT _ _).2] at h
    rw [tableBusCount_eq,tableBusCount_eq] at h
    have he:∀r,rowTraffic Qv.Candidates.KeyTrafficRepair.interactions (ProcPriorRoutedKeyView.key tr) 0 r pub B_VBYTES true=
        rowTraffic Qv.Candidates.CombinedTable.interactions (ProcPriorRoutedKeyView.key tr) 0 r pub B_VBYTES true:=by
      intro r;exact Qv.Candidates.KeyTrafficRepair.other_bus _ _ _ _ _ (by decide) _
    simp only [he] at h
    rw [byte_all_physical hl q v] at h
    simpa only [others,qbytes,extra,List.count_append,acctV3Traffic,akeyTraffic,valTraffic,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  have hn:=(hp.map byteKey).nodup_iff.mpr (value_byte_keys_unique hv)
  rw [List.map_append,List.nodup_append] at hn
  exact hn.1

theorem slots {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hv:ValWf es)
    (hT:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    {as:List AcctV} (hw:as=[] ∨ AcctV3Wf as)
    (ha:TableTraffic AcctV3.interactions tr 6 pub (acctV3Traffic as)):(as.map (·.k)).Nodup:=by
  rcases hw with rfl|hw
  · simp
  have hn:=keys view hpub hv hT ha
  have he:((acctV3Sends as B_VBYTES).map Msg.toFp).map byteKey=
      as.flatMap (fun a=>(ProcessRepairAccountStream.stream a).map byteKey):=by
    simp only [acctV3Sends,ite_true,List.map_flatMap,ProcessRepairAccountStream.stream]
  rw [he] at hn
  unfold List.Nodup
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  simp only [List.length_map] at hi hj
  simp only [List.getElem_map] at heq
  have hli:0<as[i].pre.length:=by rw [(hw.v1.len _ (List.getElem_mem hi)).1];decide
  have hlj:0<as[j].pre.length:=by rw [(hw.v1.len _ (List.getElem_mem hj)).1];decide
  obtain ⟨mi,hmi,hki⟩:=ProcessRepairAccountStream.start as[i] hli
  obtain ⟨mj,hmj,hkj⟩:=ProcessRepairAccountStream.start as[j] hlj
  have hmi':(Fp.ofNat as[i].k,0)∈(ProcessRepairAccountStream.stream as[i]).map byteKey:=
    List.mem_map.mpr ⟨mi,hmi,hki⟩
  have hmj':(Fp.ofNat as[i].k,0)∈(ProcessRepairAccountStream.stream as[j]).map byteKey:=by
    rw [heq]
    exact List.mem_map.mpr ⟨mj,hmj,hkj⟩
  exact Sound.flatMap_disj (fun a=>(ProcessRepairAccountStream.stream a).map byteKey)
    as i j as[i] as[j] (Fp.ofNat as[i].k,0) hn (by omega)
    (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hmi' hmj'
end ZkFormal.NearV3.Candidates.ProcessRepairAccountUnique
