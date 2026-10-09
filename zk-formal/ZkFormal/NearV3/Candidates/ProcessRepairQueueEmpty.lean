import ZkFormal.NearV3.Candidates.ProcessRepairQueueComplete
import ZkFormal.NearV3.Candidates.ProcessRepairQvcBalance
import ZkFormal.NearV3.Qv.Extract.EmptyProvider
namespace ZkFormal.NearV3.Candidates.ProcessRepairQueueEmpty
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open NearSpecV3 Qv Qv.Extract Qv.Candidates.ValueTable

theorem record {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hv:ValWf es)
    (hT:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    (hvb:∀e∈es,Bytes8 e.bytes)
    (q:WalkChain (ProcPriorRoutedKeyView.key tr) 0)
    (v:ParserChain (ProcPriorRoutedKeyView.key tr) 0 (segEnd 0 q.segs))
    (p:Nat×Nat) (hp:p∈v.segs) (hm:(ProcPriorRoutedKeyView.key tr).cell 0 p.1 mEmpty=1) :
    ∃e∈es,e.vz=false ∧ e.vid=cv (ProcPriorRoutedKeyView.key tr) 0 p.1 vid ∧ e.len=16 ∧
      EmptyQueue (some (toBytes e.bytes)) := by
  have hL:=Qv.Candidates.KeyTrafficRepair.local_to_base (ProcessRepairKeyView.local_key view)
  have hb:=seg_le_end v.segs (segEnd 0 q.segs) v.consecutive p hp
  have hfit:p.1+p.2≤(ProcPriorRoutedKeyView.key tr).height 0:=Nat.le_trans hb.2 v.fits
  have hw:∀r,p.1≤r→r<p.1+p.2→(ProcPriorRoutedKeyView.key tr).cell 0 r Qv.Candidates.CombinedTable.walk=0:=by
    intro r hr hn
    exact zero_of_false hL (by omega) (x:=Qv.Candidates.CombinedTable.walk) (by simp [walkBools])
      (q.suffix r (by omega) (by omega))
  have hs:=v.valid p hp
  have hmin:=Parser.empty_row_count hL hfit hw hs hm
  have hn:cv (ProcPriorRoutedKeyView.key tr) 0 p.1 len≠0:=by
    rcases Parser.length_cases hL hfit hw hs with h|h <;> omega
  exact empty_native_record hL hfit hw hs hv hvb
    (ProcessRepairQueueComplete.record view hpub hv hT q v p hp hn) hm
theorem read {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    (hpubC:∀seg∈AP.pubSegs,seg.bus≠B_QVC)
    {es:List ValE} (hv:ValWf es)
    (hT:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    (hvb:∀e∈es,Bytes8 e.bytes)
    (q:WalkChain (ProcPriorRoutedKeyView.key tr) 0)
    (v:ParserChain (ProcPriorRoutedKeyView.key tr) 0 (segEnd 0 q.segs))
    (w:Nat×Nat) (hw:w∈q.segs)
    (ha:(ProcPriorRoutedKeyView.key tr).cell 0 w.1 Qv.Candidates.CombinedTable.absent=0)
    (hm:cv (ProcPriorRoutedKeyView.key tr) 0 w.1 len=0) :
    ∃e∈es,e.vid=cv (ProcPriorRoutedKeyView.key tr) 0 w.1 vid ∧ EmptyQueue (some (toBytes e.bytes)) := by
  have hL:=Qv.Candidates.KeyTrafficRepair.local_to_base (ProcessRepairKeyView.local_key view)
  obtain ⟨p,hp,hbuf,hvid,htau⟩:=physical_empty_provider_exists hL q v
    (ProcessRepairQvcBalance.base_balance view hpubC) w hw ha hm
  obtain ⟨e,he,hz,hid,_,hempty⟩:=record view hpub hv hT hvb q v p hp hbuf
  exact ⟨e,he,hid.trans hvid,hempty⟩
end ZkFormal.NearV3.Candidates.ProcessRepairQueueEmpty
