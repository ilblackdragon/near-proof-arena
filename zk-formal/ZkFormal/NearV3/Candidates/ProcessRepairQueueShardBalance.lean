import ZkFormal.NearV3.Candidates.ProcessRepairQueueShardStream
namespace ZkFormal.NearV3.Candidates.ProcessRepairQueueShardBalance
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open Qv Qv.Extract Qv.Candidates.ValueTable
theorem balance {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    (hpubQ:∀seg∈AP.pubSegs,seg.bus≠B_QSH)
    {es:List ValE} (hv:ValWf es)
    (hT:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    (hvb:∀e∈es,Bytes8 e.bytes)
    (q:WalkChain (ProcPriorRoutedKeyView.key tr) 0)
    (v:ParserChain (ProcPriorRoutedKeyView.key tr) 0 (segEnd 0 q.segs))
 :
    ∃shards:Nat×Nat→List Nat,
      (∀p∈v.segs,(ProcPriorRoutedKeyView.key tr).cell 0 p.1 mBuffer=1→
        ∃e∈es,e.vz=false ∧ e.vid=cv (ProcPriorRoutedKeyView.key tr) 0 p.1 vid ∧ e.len=p.2 ∧
          BufferedValue (some (toBytes e.bytes)) (shards p)) ∧
      ((List.range (segEnd 0 q.segs)).flatMap
        (fun r=>rowTraffic Qv.Candidates.CombinedTable.interactions (ProcPriorRoutedKeyView.key tr) 0 r pub B_QSH false)).Perm (
        v.segs.flatMap (fun p=>if (ProcPriorRoutedKeyView.key tr).cell 0 p.1 mBuffer=1 then
          Parser.nativeShardMessages ((ProcPriorRoutedKeyView.key tr).cell 0 p.1 tau) (shards p) else [])) := by
  obtain ⟨ss,he,htotal⟩:=ProcessRepairQueueShardStream.streams view hpub hv hT hvb q v
  refine ⟨ss,he,List.perm_iff_count.mpr ?_⟩
  intro msg
  have h:=ProcessRepairQshBalance.balance view hpubQ msg
  rw [tableBusCount_eq,tableBusCount_eq] at h
  have heq (dir:Bool):∀r,rowTraffic Qv.Candidates.KeyTrafficRepair.interactions (ProcPriorRoutedKeyView.key tr) 0 r pub B_QSH dir=
      rowTraffic Qv.Candidates.CombinedTable.interactions (ProcPriorRoutedKeyView.key tr) 0 r pub B_QSH dir:=by
    intro r;exact Qv.Candidates.KeyTrafficRepair.other_bus _ _ _ _ _ (by decide) _
  simp only [heq] at h
  have hL:=Qv.Candidates.KeyTrafficRepair.local_to_base (ProcessRepairKeyView.local_key view)
  rw [htotal,shard_receives_prefix hL q] at h
  exact h.symm
end ZkFormal.NearV3.Candidates.ProcessRepairQueueShardBalance
