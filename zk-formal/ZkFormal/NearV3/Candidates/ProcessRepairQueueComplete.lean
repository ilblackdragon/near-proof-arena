import ZkFormal.NearV3.Candidates.ProcessRepairVbytesCounts
import ZkFormal.NearV3.Candidates.ProcessRepairQueueSuppliers
import ZkFormal.NearV3.Candidates.ProcessRepairQueueRecordComplete
namespace ZkFormal.NearV3.Candidates.ProcessRepairQueueComplete
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open Qv.Extract
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem record {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hv:ValWf es)
    (hT:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    (q:WalkChain (ProcPriorRoutedKeyView.key tr) 0)
    (v:ParserChain (ProcPriorRoutedKeyView.key tr) 0 (segEnd 0 q.segs))
    (p:Nat×Nat) (hp:p∈v.segs) (hn:cv (ProcPriorRoutedKeyView.key tr) 0 p.1 Qv.Candidates.ValueTable.len≠0) :
    (physicalRecordBytes (ProcPriorRoutedKeyView.key tr) 0 p.1 p.2 pub).Perm
      (((valRecvs es B_VBYTES).map Msg.toFp).filter
        (fun m=>decide ((byteKey m).1=(ProcPriorRoutedKeyView.key tr).cell 0 p.1 Qv.Candidates.ValueTable.vid))) := by
  classical
  have hl:=Qv.Candidates.KeyTrafficRepair.local_to_base (ProcessRepairKeyView.local_key view)
  obtain ⟨as,ha⟩:=ProcessRepairQueueSuppliers.accounts view
  obtain ⟨aks,_,hk⟩:=ProcessRepairQueueSuppliers.access_keys view
  let extra:List (List Fp):=(List.range (tr.height 0)).flatMap
    (fun r=>rowTraffic [ProcPriorRoutedRawBytes.bytes] tr 0 r pub B_VBYTES true)
  have hclosed:StartClosed extra:=ProcessRepairRawStartClosed.start_closed view
  have hglobal:((v.segs.flatMap (fun p=>physicalRecordBytes (ProcPriorRoutedKeyView.key tr) 0 p.1 p.2 pub) ++
    (acctV3Sends as B_VBYTES).map Msg.toFp ++ (akeySends aks B_VBYTES).map Msg.toFp) ++extra).Perm
      ((valRecvs es B_VBYTES).map Msg.toFp):=by
    apply List.perm_iff_count.mpr
    intro msg
    have h:=ProcessRepairVbytesCounts.balance view hpub msg
    rw [(ha _ _).1,(hk _ _).1,(hT _ _).2] at h
    rw [tableBusCount_eq,tableBusCount_eq] at h
    have he:∀r,rowTraffic Qv.Candidates.KeyTrafficRepair.interactions (ProcPriorRoutedKeyView.key tr) 0 r pub B_VBYTES true=
        rowTraffic Qv.Candidates.CombinedTable.interactions (ProcPriorRoutedKeyView.key tr) 0 r pub B_VBYTES true:=by
      intro r;exact Qv.Candidates.KeyTrafficRepair.other_bus _ _ _ _ _ (by decide) _
    simp only [he] at h
    rw [byte_all_physical hl q v] at h
    simp only [List.count_append]
    change _+_+_+_= _ at h
    change _= _
    simpa only [extra,acctV3Traffic,akeyTraffic,valTraffic,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  have hmove:=(List.perm_cons_erase hp).flatMap_right
    (fun z=>physicalRecordBytes (ProcPriorRoutedKeyView.key tr) 0 z.1 z.2 pub)
  have hselected:=((hmove.append_right ((acctV3Sends as B_VBYTES).map Msg.toFp)).append_right
    ((akeySends aks B_VBYTES).map Msg.toFp)).append_right extra
  apply ProcessRepairQueueRecordComplete.selected hl q v p hp hn (v.segs.erase p)
    (fun z hz=>List.mem_of_mem_erase hz) as aks es hv extra hclosed
  simpa only [List.flatMap_cons,List.append_assoc] using hselected.symm.trans hglobal
end ZkFormal.NearV3.Candidates.ProcessRepairQueueComplete
