import ZkFormal.NearV3.Candidates.ProcessRepairQueueBuffered
import ZkFormal.NearV3.Qv.Extract.NativeShardAggregate
import ZkFormal.NearV3.Qv.Extract.WalkShardTraffic
namespace ZkFormal.NearV3.Candidates.ProcessRepairQueueShardStream
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open Qv Qv.Extract Qv.Candidates.ValueTable
theorem streams {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
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
      (List.range ((ProcPriorRoutedKeyView.key tr).height 0)).flatMap
        (fun r=>rowTraffic Qv.Candidates.CombinedTable.interactions (ProcPriorRoutedKeyView.key tr) 0 r pub B_QSH true)=
        v.segs.flatMap (fun p=>if (ProcPriorRoutedKeyView.key tr).cell 0 p.1 mBuffer=1 then
          Parser.nativeShardMessages ((ProcPriorRoutedKeyView.key tr).cell 0 p.1 tau) (shards p) else []) := by
  classical
  have hL:=Qv.Candidates.KeyTrafficRepair.local_to_base (ProcessRepairKeyView.local_key view)
  have hx:∀p:Nat×Nat,∃shards:List Nat,p∈v.segs→(ProcPriorRoutedKeyView.key tr).cell 0 p.1 mBuffer=1→
      (∃e∈es,e.vz=false ∧ e.vid=cv (ProcPriorRoutedKeyView.key tr) 0 p.1 vid ∧ e.len=p.2 ∧
        BufferedValue (some (toBytes e.bytes)) shards) ∧
      (List.range' p.1 p.2).flatMap (fun r=>rowTraffic Qv.Candidates.CombinedTable.interactions
        (ProcPriorRoutedKeyView.key tr) 0 r pub B_QSH true)=
        Parser.nativeShardMessages ((ProcPriorRoutedKeyView.key tr).cell 0 p.1 tau) shards:=by
    intro p
    by_cases hp:p∈v.segs
    · by_cases hm:(ProcPriorRoutedKeyView.key tr).cell 0 p.1 mBuffer=1
      · obtain ⟨e,he,hz,hid,hlen,ss,hbuf,hstream⟩:=ProcessRepairQueueBuffered.buffered view hpub hv hT hvb q v p hp hm
        exact ⟨ss,fun _ _=>⟨⟨e,he,hz,hid,hlen,hbuf⟩,hstream⟩⟩
      · exact ⟨[],fun _ hm'=>False.elim (hm hm')⟩
    · exact ⟨[],fun hp' _=>False.elim (hp hp')⟩
  let shards:=fun p=>Classical.choose (hx p)
  have hshards:=fun p=>Classical.choose_spec (hx p)
  refine ⟨shards,fun p hp hm=>(hshards p hp hm).1,?_⟩
  rw [shard_sends_suffix hL q,parser_shard_suffix hL q v true]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro p hp
  by_cases hm:(ProcPriorRoutedKeyView.key tr).cell 0 p.1 mBuffer=1
  · simpa only [hm,ite_true,List.flatMap_def,shards] using (hshards p hp hm).2
  · simpa only [hm,ite_false,List.flatMap_def] using nonbuffer_record_silent hL q v p hp hm true
end ZkFormal.NearV3.Candidates.ProcessRepairQueueShardStream
