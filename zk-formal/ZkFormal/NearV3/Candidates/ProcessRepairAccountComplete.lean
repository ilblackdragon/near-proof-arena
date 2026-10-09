import ZkFormal.NearV3.Candidates.ProcessRepairAccountStream
namespace ZkFormal.NearV3.Candidates.ProcessRepairAccountComplete
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open Qv.Extract ProcessRepairAccountStream
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem value {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hv:ValWf es)
    (hT:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    {as:List AcctV} (hw:as=[] ∨ AcctV3Wf as)
    (ha:TableTraffic AcctV3.interactions tr 6 pub (acctV3Traffic as))
    {a:AcctV} (ham:a∈as):∃e∈es,e.vz=false ∧ e.vid=a.k ∧ e.bytes=a.pre:=by
  have hw:AcctV3Wf as:=by
    rcases hw with rfl|hw
    · simp at ham
    · exact hw
  have hlen:=(hw.v1.len a ham).1
  have hk:=(hw.v1.len a ham).2.2.1
  have hc:∀x∈a.pre,x<P:=fun x hx=>hw.v1.canon a ham x (List.mem_append_left _ hx)
  have hl:=Qv.Candidates.KeyTrafficRepair.local_to_base (ProcessRepairKeyView.local_key view)
  obtain ⟨q⟩:=walk_chain_exists hl
  obtain ⟨v⟩:=parser_chain_exists hl q
  obtain ⟨aks,_,hak⟩:=ProcessRepairQueueSuppliers.access_keys view
  obtain ⟨left,right,heq⟩:=List.mem_iff_append.mp ham
  let extra:List (List Fp):=(List.range (tr.height 0)).flatMap
    (fun r=>rowTraffic [ProcPriorRoutedRawBytes.bytes] tr 0 r pub B_VBYTES true)
  let qbytes:=v.segs.flatMap (fun p=>physicalRecordBytes (ProcPriorRoutedKeyView.key tr) 0 p.1 p.2 pub)
  let rest:List (List Fp):=((acctV3Sends (left++right) B_VBYTES).map Msg.toFp ++ qbytes ++
    (akeySends aks B_VBYTES).map Msg.toFp) ++ extra
  have hclosed:StartClosed rest:=startClosed_append
    (startClosed_append (startClosed_append (account_streams_closed (left++right))
      (physical_records_closed hl q v v.segs (fun _ h=>h))) (access_key_streams_closed aks))
    (ProcessRepairRawStartClosed.start_closed view)
  have hbalance:(stream a++rest).Perm ((valRecvs es B_VBYTES).map Msg.toFp):=by
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
    rw [heq] at h
    simp only [acctV3Traffic,acctV3Sends,ite_true,List.flatMap_append,List.flatMap_cons,
      List.map_append,List.count_append] at h
    simpa only [stream,rest,qbytes,extra,acctV3Sends,ite_true,List.flatMap_append,List.map_append,
      List.count_append,akeyTraffic,valTraffic,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  exact exact_value hv a (by omega) hk (by unfold P;omega) hc
    (isolate hv a (by omega) rest hclosed hbalance)
end ZkFormal.NearV3.Candidates.ProcessRepairAccountComplete
