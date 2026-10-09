import ZkFormal.NearV3.Candidates.ProcessRepairQueueComplete
import ZkFormal.NearV3.Candidates.ProcessRepairValueRange
namespace ZkFormal.NearV3.Candidates.ProcessRepairQueueBuffered
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open NearSpecV3 Qv Qv.Extract Qv.Candidates.ValueTable

theorem buffered {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hv:ValWf es)
    (hT:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    (hvb:∀e∈es,Bytes8 e.bytes)
    (q:WalkChain (ProcPriorRoutedKeyView.key tr) 0)
    (v:ParserChain (ProcPriorRoutedKeyView.key tr) 0 (segEnd 0 q.segs))
    (p:Nat×Nat) (hp:p∈v.segs) (hm:(ProcPriorRoutedKeyView.key tr).cell 0 p.1 mBuffer=1) :
    ∃e∈es,e.vz=false ∧ e.vid=cv (ProcPriorRoutedKeyView.key tr) 0 p.1 vid ∧ e.len=p.2 ∧
      ∃shards,BufferedValue (some (toBytes e.bytes)) shards ∧
        (List.range' p.1 p.2).flatMap (fun r=>rowTraffic Qv.Candidates.CombinedTable.interactions
          (ProcPriorRoutedKeyView.key tr) 0 r pub B_QSH true)=
          Parser.nativeShardMessages ((ProcPriorRoutedKeyView.key tr).cell 0 p.1 tau) shards := by
  have hL:=Qv.Candidates.KeyTrafficRepair.local_to_base (ProcessRepairKeyView.local_key view)
  have hb:=seg_le_end v.segs (segEnd 0 q.segs) v.consecutive p hp
  have hfit:p.1+p.2≤(ProcPriorRoutedKeyView.key tr).height 0:=Nat.le_trans hb.2 v.fits
  have hw:∀r,p.1≤r→r<p.1+p.2→(ProcPriorRoutedKeyView.key tr).cell 0 r Qv.Candidates.CombinedTable.walk=0:=by
    intro r hr hn
    exact zero_of_false hL (by omega) (x:=Qv.Candidates.CombinedTable.walk) (by simp [walkBools])
      (q.suffix r (by omega) (by omega))
  have hs:=v.valid p hp
  have hmin:=(Parser.buffered_header_rows hL hfit hw hs hm 3 (by omega)).1
  have hn:cv (ProcPriorRoutedKeyView.key tr) 0 p.1 len≠0:=by
    rcases Parser.length_cases hL hfit hw hs with h|h <;> omega
  exact buffered_native_record hL hfit hw hs hv hvb
    (ProcessRepairQueueComplete.record view hpub hv hT q v p hp hn) hm
end ZkFormal.NearV3.Candidates.ProcessRepairQueueBuffered
