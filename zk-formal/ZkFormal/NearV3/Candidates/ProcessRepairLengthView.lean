import ZkFormal.NearV3.Candidates.ProcessRepairLengthSource
import ZkFormal.NearV3.Candidates.ProcPriorRoutedLengthView
namespace ZkFormal.NearV3.Candidates.ProcessRepairLengthView
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRoutedRawBytes
open ProcPriorRoutedLengthView (indexed)
theorem source {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub 73 true msg=0)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es))
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=73) (hs:i.send=false)
    (hm:i.multNat tr t r pub≠0) :
    ∃id,id<es.length ∧ es[id]!.vid=id ∧
      i.msgVal tr t r pub=[Fp.ofNat id,Fp.ofNat es[id]!.bytes.length] := by
  obtain ⟨q,hq,hg,hmsg⟩:=ProcessRepairLengthSource.source view hpub ht hr hi hb hs hm
  have hhead:=ProcessRepairLengthSource.header view hq hg
  obtain ⟨hid,hvid,hlen⟩:=indexed hw hT hq hhead
  refine ⟨cv (value tr) 0 q ValV3.vid,hid,hvid,?_⟩
  rw [←hmsg,hlen]
  change [(value tr).cell 0 q ValV3.vid,(value tr).cell 0 q ValV3.len]=_
  simp only [cv,Fp.ofNat_toNat]
end ZkFormal.NearV3.Candidates.ProcessRepairLengthView
