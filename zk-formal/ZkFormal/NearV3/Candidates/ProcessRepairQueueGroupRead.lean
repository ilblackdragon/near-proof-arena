import ZkFormal.NearV3.Candidates.ProcessRepairQvcBalance
import ZkFormal.NearV3.Candidates.ProcessRepairQueueGroupKey
import ZkFormal.NearV3.Qv.Extract.BufferedProvider
namespace ZkFormal.NearV3.Candidates.ProcessRepairQueueGroupRead
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open Qv Qv.Extract Qv.Candidates.ValueTable

theorem native_key {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    (hpubQ:∀seg∈AP.pubSegs,seg.bus≠B_QSH) (hpubC:∀seg∈AP.pubSegs,seg.bus≠B_QVC)
    {es:List ValE} (hv:ValWf es)
    (hT:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    (hvb:∀e∈es,Bytes8 e.bytes)
    (q:WalkChain (ProcPriorRoutedKeyView.key tr) 0)
    (v:ParserChain (ProcPriorRoutedKeyView.key tr) 0 (segEnd 0 q.segs))
    (w:Nat×Nat) (hw:w∈q.segs)
    (ha:(ProcPriorRoutedKeyView.key tr).cell 0 w.1 Qv.Candidates.CombinedTable.absent=0)
    (hm:cv (ProcPriorRoutedKeyView.key tr) 0 w.1 len=1) :
    ∃e∈es,e.vz=false ∧ e.vid=cv (ProcPriorRoutedKeyView.key tr) 0 w.1 vid ∧
      ∃shards,BufferedValue (some (toBytes e.bytes)) shards ∧
        ∀j (hj:j<q.segs.length),
          (ProcPriorRoutedKeyView.key tr).cell 0 q.segs[j].1 Qv.Candidates.CombinedTable.main=1→3≤j→
          NearSpec.nibbles (physicalWalkBytes (ProcPriorRoutedKeyView.key tr) 0 q.segs[j])=
            NearSpecV3.keyGroupsData (shards.getD (j-3) 0) := by
  have hL:=Qv.Candidates.KeyTrafficRepair.local_to_base (ProcessRepairKeyView.local_key view)
  obtain ⟨p,hp,hbuf,hvid,htau⟩:=physical_buffered_provider_exists hL q v
    (ProcessRepairQvcBalance.base_balance view hpubC) w hw ha hm
  obtain ⟨e,he,hz,hid,_,ss,hss,hkeys⟩:=ProcessRepairQueueGroupKey.native_key view hpub hpubQ hv hT hvb q v p hp hbuf
  exact ⟨e,he,hz,hid.trans hvid,ss,hss,hkeys⟩
end ZkFormal.NearV3.Candidates.ProcessRepairQueueGroupRead
