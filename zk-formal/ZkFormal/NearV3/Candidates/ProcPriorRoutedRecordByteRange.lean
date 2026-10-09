import ZkFormal.NearV3.Candidates.ProcPriorRoutedValueBytes
import ZkFormal.NearV3.Candidates.ProcPriorRoutedValueRange
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedRecordByteRange
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched
open ProcPriorRoutedRawSource (raw)
open ProcPriorRoutedRawBytes (value)

theorem raw_byte {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es))
    (hbytes:∀e∈es,∀b∈e.bytes,b<256)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv (raw tr) 0 r ProcPriorRawFrame.act=1) :
    cv (raw tr) 0 r ProcPriorRawFrame.byte<256 := by
  have ht:0<AP.tables.length:=by rw [htables];decide +kernel
  have hL:=local_of_holdsP hH ht
  rw [htables] at hL
  have hv:=ProcPriorRoutedFamilyWrite.projected_local hL
  change ProcPriorVerticalMemorySound.LocalV (raw tr) 0 pub at hv
  have hp:=ProcPriorRawSound.flag hv hr hs ProcPriorRawFrame.present (by simp)
  by_cases hpres:cv (raw tr) 0 r ProcPriorRawFrame.present=1
  · obtain ⟨e,he,_,hpos,hbyte⟩:=ProcPriorRoutedValueBytes.raw_byte hH htables hpub hw hT hr hs ha hpres
    rw [hbyte,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hpos,Option.getD_some]
    exact hbytes e he _ (List.getElem_mem hpos)
  · have hz:cv (raw tr) 0 r ProcPriorRawFrame.present=0:=by omega
    have hb:=(ProcPriorRawSound.absent_zero hv hr hs hz).1
    omega

theorem received {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpubV:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    (hpubR:∀msg,pubCount AP pub 75 true msg=0)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es))
    (hbytes:∀e∈es,∀b∈e.bytes,b<256)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=75) (hs:i.send=false)
    (hm:i.multNat tr t r pub≠0) :
    (i.msgVal tr t r pub)[3]!.toNat<256 := by
  obtain ⟨q,hq,hstage,_,hact,hmsg⟩:=ProcPriorRoutedRawSource.record_source hH htables hpubR ht hr hi hb hs hm
  have hbyte:=raw_byte hH htables hpubV hw hT hbytes hq hstage hact
  have he:=congrArg (fun xs:List Fp=>xs[3]!.toNat) hmsg
  change cv (raw tr) 0 q ProcPriorRawFrame.byte=(i.msgVal tr t r pub)[3]!.toNat at he
  omega
end ZkFormal.NearV3.Candidates.ProcPriorRoutedRecordByteRange
