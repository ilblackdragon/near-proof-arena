import ZkFormal.NearV3.Candidates.ProcessRepairQueueShardBalance
import ZkFormal.NearV3.Qv.Extract.UniqueShardLookup
import ZkFormal.NearV3.Qv.Extract.NativeGroupKey
namespace ZkFormal.NearV3.Candidates.ProcessRepairQueueGroupKey
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open Qv Qv.Extract Qv.Candidates.ValueTable

theorem native_key {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    (hpubQ:∀seg∈AP.pubSegs,seg.bus≠B_QSH)
    {es:List ValE} (hv:ValWf es)
    (hT:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    (hvb:∀e∈es,Bytes8 e.bytes)
    (q:WalkChain (ProcPriorRoutedKeyView.key tr) 0)
    (v:ParserChain (ProcPriorRoutedKeyView.key tr) 0 (segEnd 0 q.segs))
    (p:Nat×Nat) (hp:p∈v.segs) (hm:(ProcPriorRoutedKeyView.key tr).cell 0 p.1 mBuffer=1) :
    ∃e∈es,e.vz=false ∧ e.vid=cv (ProcPriorRoutedKeyView.key tr) 0 p.1 vid ∧ e.len=p.2 ∧
      ∃shards,BufferedValue (some (toBytes e.bytes)) shards ∧
        ∀j (hj:j<q.segs.length),
          (ProcPriorRoutedKeyView.key tr).cell 0 q.segs[j].1 Qv.Candidates.CombinedTable.main=1→3≤j→
          NearSpec.nibbles (physicalWalkBytes (ProcPriorRoutedKeyView.key tr) 0 q.segs[j])=
            NearSpecV3.keyGroupsData (shards.getD (j-3) 0) := by
  obtain ⟨ss,hrecords,hperm⟩:=ProcessRepairQueueShardBalance.balance view hpub hpubQ hv hT hvb q v
  obtain ⟨e,he,hz,hid,hlen,hbuf⟩:=hrecords p hp hm
  refine ⟨e,he,hz,hid,hlen,ss p,hbuf,?_⟩
  have hL:=Qv.Candidates.KeyTrafficRepair.local_to_base (ProcessRepairKeyView.local_key view)
  have hb:=bufferedValue_length hbuf
  have hs:=(hv.shape e he).2 hz
  have hc:=hv.canon e he
  have hss:(ss p).length<P:=by
    simp only [toBytes,List.length_map] at hb
    omega
  intro j hj hmain hj3
  exact native_group_key hL q (ss p) ((ProcPriorRoutedKeyView.key tr).cell 0 p.1 tau) hss
    (fun m hreq=>unique_shard_member hL q v.segs ss hperm hp hm hreq) j hj hmain hj3
end ZkFormal.NearV3.Candidates.ProcessRepairQueueGroupKey
