import ZkFormal.NearV3.Candidates.ProcPriorRoutedRawFrameBytes
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedHeaderZeros
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound
open ProcPriorRoutedRawSource (raw)
open ProcPriorRoutedRawBytes (value)
theorem zeros {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es))
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv (raw tr) 0 r first=1) (hp:cv (raw tr) 0 r present=1) :
    let bs:=(es[cv (raw tr) 0 r vid]!).bytes
    bs.getD 0 0=0 ∧ bs.getD 4 0=0 := by
  have ht0:0<AP.tables.length:=by rw [htables];decide +kernel
  have hL:=local_of_holdsP hH ht0
  rw [htables] at hL
  have hv:=ProcPriorRoutedFamilyWrite.projected_local hL
  change ProcPriorVerticalMemorySound.LocalV (raw tr) 0 pub at hv
  have hz:=(ProcPriorRawEndpoints.first_fields hv hr hs hf).2.1
  obtain ⟨hh,ha,ho⟩:=ProcPriorRawPhase.first_header hv hr hs hf
  have hk:=kinds hv hr hs
  have he:4=4*cv (raw tr) 0 r hdr+23*cv (raw tr) 0 r rec+31*cv (raw tr) 0 r hash:=by omega
  obtain ⟨hr4,hs4,_,_,hf4⟩:=ProcPriorRawPhase.traverse hv hr hs ha ho 4 he 4 (by decide)
  have hend:=ProcPriorRawPhase.boundary_flag hv hr hs ha ho 4 he 4 (by decide)
  simp only [ite_true] at hend
  have hh4:cv (raw tr) 0 (r+4) hdr=1:=(hf4 hdr (by simp)).trans hh
  have hz4:=(ProcPriorRawHeaderCount.end_zero hv hr4 hs4 hh4 hend).2
  have hb0:=(ProcPriorRoutedRawFrameBytes.byte_at hH htables hpub hw hT hr hs hf hp 0 (by omega)).2.2.2
  have hb4:=(ProcPriorRoutedRawFrameBytes.byte_at hH htables hpub hw hT hr hs hf hp 4 (by omega)).2.2.2
  dsimp only
  exact ⟨hb0.symm.trans hz,hb4.symm.trans hz4⟩
end ZkFormal.NearV3.Candidates.ProcPriorRoutedHeaderZeros
