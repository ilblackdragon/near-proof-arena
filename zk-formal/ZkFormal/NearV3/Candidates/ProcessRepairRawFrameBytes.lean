import ZkFormal.NearV3.Candidates.ProcPriorRawRecordPosition
import ZkFormal.NearV3.Candidates.ProcessRepairValueBytes
namespace ZkFormal.NearV3.Candidates.ProcessRepairRawFrameBytes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame
open ProcPriorRoutedRawSource (raw)
open ProcPriorRoutedRawBytes (value)

/-- All declared bytes of a present frame belong to one actual extracted
Value entry, at their exact serialized natural positions. -/
theorem byte_at {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es))
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv (raw tr) 0 r first=1) (hp:cv (raw tr) 0 r present=1)
    (j:Nat) (hj:j<37+24*cv (raw tr) 0 r count) :
    let id:=cv (raw tr) 0 r vid
    id<es.length ∧ es[id]!.vid=id ∧ j<es[id]!.bytes.length ∧
      cv (raw tr) 0 (r+j) byte=es[id]!.bytes.getD j 0 := by
  have hh:tr.height 0≤2^22:=Nat.pow_le_pow_right (by decide) (ProcessRepairTrieViews.value_local view).log_le
  have hv:=ProcessRepairRawBytes.overlay_local view
  have hhraw:(raw tr).height 0≤2013265921:=by change tr.height 0≤2013265921;omega
  obtain ⟨hrj,hsj,haj,hpos,hfields⟩:=ProcPriorRawRecordPosition.frame hv hr hs hf hhraw j hj
  have hpj:(cv (raw tr) 0 (r+j) present)=1:=(hfields present (by simp)).trans hp
  have hid:=hfields vid (by simp)
  have hb:=ProcessRepairValueBytes.raw_byte_index view hpub hw hT hrj hsj haj hpj
  dsimp only at hb ⊢
  change cv (raw tr) 0 (r+j) vid=cv (raw tr) 0 r vid at hid
  change cv (raw tr) 0 (r+j) pos=j at hpos
  rw [hid,hpos] at hb
  exact hb
end ZkFormal.NearV3.Candidates.ProcessRepairRawFrameBytes
