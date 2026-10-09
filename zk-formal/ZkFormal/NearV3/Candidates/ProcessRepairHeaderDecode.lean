import ZkFormal.NearV3.Candidates.ProcessRepairRawFrameBytes
namespace ZkFormal.NearV3.Candidates.ProcessRepairHeaderDecode
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame
open ProcPriorRoutedRawSource (raw)
open ProcPriorRoutedRawBytes (value)

/-- Decoder bridge: the range premise belongs to the SAME extracted Value
list, so authenticated SHA preimages can discharge it without changing witness. -/
theorem count_bytes {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es))
    (hbytes:∀e∈es,∀b∈e.bytes,b<256)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv (raw tr) 0 r first=1) (hp:cv (raw tr) 0 r present=1) :
    let bs:=(es[cv (raw tr) 0 r vid]!).bytes
    cv (raw tr) 0 r count=bs.getD 1 0+256*bs.getD 2 0+65536*bs.getD 3 0 ∧
      cv (raw tr) 0 r count<16777216 := by
  have hv:=ProcessRepairRawBytes.overlay_local view
  have hbound (j:Nat) (hj:1≤j) (hj3:j≤3):cv (raw tr) 0 (r+j) byte<256:=by
    obtain ⟨hid,_,hpos,hbyte⟩:=ProcessRepairRawFrameBytes.byte_at view hpub hw hT hr hs hf hp j (by omega)
    rw [hbyte,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hpos,Option.getD_some]
    have hem:es[cv (raw tr) 0 r vid]!∈es:=by rw [getElem!_pos es _ hid];exact List.getElem_mem hid
    exact hbytes _ hem _ (List.getElem_mem hpos)
  have hc:=ProcPriorRawHeaderCount.count_bytes hv hr hs hf hbound
  have hb1:=(ProcessRepairRawFrameBytes.byte_at view hpub hw hT hr hs hf hp 1 (by omega)).2.2.2
  have hb2:=(ProcessRepairRawFrameBytes.byte_at view hpub hw hT hr hs hf hp 2 (by omega)).2.2.2
  have hb3:=(ProcessRepairRawFrameBytes.byte_at view hpub hw hT hr hs hf hp 3 (by omega)).2.2.2
  change cv (raw tr) 0 r count=cv (raw tr) 0 (r+1) byte+256*cv (raw tr) 0 (r+2) byte+65536*cv (raw tr) 0 (r+3) byte ∧ _ at hc
  rw [hb1,hb2,hb3] at hc
  exact hc
end ZkFormal.NearV3.Candidates.ProcessRepairHeaderDecode
