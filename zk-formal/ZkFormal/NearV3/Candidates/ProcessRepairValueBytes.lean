import ZkFormal.NearV3.Candidates.ProcessRepairRawBytes
import ZkFormal.NearV3.Candidates.ProcessRepairTrieViews
import ZkFormal.NearV3.Candidates.ProcPriorRoutedValueBytes
namespace ZkFormal.NearV3.Candidates.ProcessRepairValueBytes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRoutedRawBytes
open ProcPriorRoutedValueBytes (byte_entry value_id_at)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
theorem raw_byte {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es))
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (ProcPriorRoutedRawSource.raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.act=1)
    (hpres:cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.present=1) :
    ∃e,e∈es ∧ e.vid=cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.vid ∧
      cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.pos<e.bytes.length ∧
      cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.byte=
        e.bytes.getD (cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.pos) 0 := by
  obtain ⟨q,hq,hg,hid,hpos,hbyte⟩:=ProcessRepairRawBytes.byte_source v hpub hr hs ha hpres
  obtain ⟨e,he,heid,hep,heb⟩:=byte_entry hw hT hq hg
  exact ⟨e,he,heid.trans hid,by rwa [hpos] at hep,by rw [←hbyte,heb,hpos]⟩
theorem raw_byte_index {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es))
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (ProcPriorRoutedRawSource.raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.act=1)
    (hpres:cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.present=1) :
    let id:=cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.vid
    let pos:=cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.pos
    id<es.length ∧ es[id]!.vid=id ∧ pos<es[id]!.bytes.length ∧
      cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.byte=es[id]!.bytes.getD pos 0 := by
  obtain ⟨e,he,heid,hep,heb⟩:=raw_byte v hpub hw hT hr hs ha hpres
  obtain ⟨k,hk,rfl⟩:=List.getElem_of_mem he
  have hkid:k=cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.vid :=
    (value_id_at hw k hk).symm.trans heid
  dsimp only
  rw [←hkid,getElem!_pos es k hk]
  rw [←hkid] at heid
  exact ⟨hk,heid,hep,heb⟩

/-- A single extracted view serves all present RawFrame bytes. -/
theorem raw_view {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES) :
    ∃es:List ValE,ValWf es ∧ ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es) ∧
    ∀r,r<tr.height 0→cv (ProcPriorRoutedRawSource.raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1→
      cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.act=1→
      cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.present=1→
      let id:=cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.vid
      let pos:=cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.pos
      id<es.length ∧ es[id]!.vid=id ∧ pos<es[id]!.bytes.length ∧
        cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.byte=es[id]!.bytes.getD pos 0 := by
  obtain ⟨es,hw,hT⟩:=val_view _ pub 0 (ProcessRepairTrieViews.value_local v)
  exact ⟨es,hw,hT,fun _ hr hs ha hp=>raw_byte_index v hpub hw hT hr hs ha hp⟩
end ZkFormal.NearV3.Candidates.ProcessRepairValueBytes
