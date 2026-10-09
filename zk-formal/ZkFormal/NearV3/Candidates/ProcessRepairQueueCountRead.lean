import ZkFormal.NearV3.Candidates.ProcessRepairQueueGroupRead
import ZkFormal.NearV3.Qv.Extract.CountReadMode
namespace ZkFormal.NearV3.Candidates.ProcessRepairQueueCountRead
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open Qv Qv.Extract Qv.Candidates.ValueTable

theorem read {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    (hpubQ:∀seg∈AP.pubSegs,seg.bus≠B_QSH) (hpubC:∀seg∈AP.pubSegs,seg.bus≠B_QVC)
    {es:List ValE} (hv:ValWf es)
    (hT:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    (hvb:∀e∈es,Bytes8 e.bytes)
    (q:WalkChain (ProcPriorRoutedKeyView.key tr) 0)
    (v:ParserChain (ProcPriorRoutedKeyView.key tr) 0 (segEnd 0 q.segs))
    (w:Nat×Nat) (hw:w∈q.segs)
    (hcount:(ProcPriorRoutedKeyView.key tr).cell 0 w.1 Qv.Candidates.CombinedTable.countRead=1) :
    ∃e∈es,e.vz=false ∧ e.vid=cv (ProcPriorRoutedKeyView.key tr) 0 w.1 vid ∧
      ∃shards,BufferedValue (some (toBytes e.bytes)) shards ∧ shards.length<P ∧
        cv (ProcPriorRoutedKeyView.key tr) 0 w.1 count=shards.length ∧
        ∀m∈(List.range (segEnd 0 q.segs)).flatMap (fun r=>rowTraffic Qv.Candidates.CombinedTable.interactions
          (ProcPriorRoutedKeyView.key tr) 0 r pub B_QSH false),
          m∈Parser.nativeShardMessages ((ProcPriorRoutedKeyView.key tr).cell 0 w.1 tau) shards := by
  have hL:=Qv.Candidates.KeyTrafficRepair.local_to_base (ProcessRepairKeyView.local_key view)
  have hend:=seg_le_end q.segs 0 q.consecutive w hw
  have hn:=(q.valid w hw).1
  have hrow:w.1<(ProcPriorRoutedKeyView.key tr).height 0:=by have:=q.fits;omega
  have hprefix:w.1<segEnd 0 q.segs:=by omega
  obtain ⟨ha,hm⟩:=count_request_read_mode hL hrow hcount
  obtain ⟨p,hp,hbuf,hvid,htau⟩:=physical_buffered_provider_exists hL q v
    (ProcessRepairQvcBalance.base_balance view hpubC) w hw ha hm
  obtain ⟨ss,hrecords,hperm⟩:=ProcessRepairQueueShardBalance.balance view hpub hpubQ hv hT hvb q v
  obtain ⟨e,he,hz,hid,hlen,hbuf⟩:=hrecords p hp hbuf
  have hb:=bufferedValue_length hbuf
  have hs:=(hv.shape e he).2 hz
  have hc:=hv.canon e he
  have hss:(ss p).length<P:=by simp only [toBytes,List.length_map] at hb;omega
  have htfield:(ProcPriorRoutedKeyView.key tr).cell 0 p.1 tau=(ProcPriorRoutedKeyView.key tr).cell 0 w.1 tau:=by
    have h:=congrArg Fp.ofNat htau
    simpa only [cv,Fp.ofNat_toNat] using h
  have hrequests:∀m∈(List.range (segEnd 0 q.segs)).flatMap (fun r=>rowTraffic Qv.Candidates.CombinedTable.interactions
      (ProcPriorRoutedKeyView.key tr) 0 r pub B_QSH false),
      m∈Parser.nativeShardMessages ((ProcPriorRoutedKeyView.key tr).cell 0 w.1 tau) (ss p):=by
    intro m hm
    rw [←htfield]
    exact unique_shard_member hL q v.segs ss hperm hp (by assumption) hm
  have hreq:=shard_count_request_mem (ProcPriorRoutedKeyView.key tr) 0 w.1 (segEnd 0 q.segs) pub hprefix hcount
  have hcnt:=Parser.native_shard_count_nat hss (hrequests _ hreq)
  exact ⟨e,he,hz,hid.trans hvid,ss p,hbuf,hss,hcnt.2,hrequests⟩
end ZkFormal.NearV3.Candidates.ProcessRepairQueueCountRead
