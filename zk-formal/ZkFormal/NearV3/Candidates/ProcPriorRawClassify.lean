import ZkFormal.NearV3.Candidates.ProcPriorRawInterval
namespace ZkFormal.NearV3.Candidates.ProcPriorRawClassify
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem frame (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hheight:tr.height t≤2013265921)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) :
    ∃f,f≤r ∧ f<tr.height t ∧ cv tr t f (ProcPriorVertical4Linear.stage 2)=1 ∧
      cv tr t f first=1 ∧ r=f+cv tr t r pos ∧
      cv tr t r pos<37+24*cv tr t f count ∧
      (∀x∈[tau,vid,present,count],cv tr t r x=cv tr t f x) := by
  obtain ⟨f,hfr,hfh,hfs,hff,_,_,he,hfields,hactive,hnotfirst⟩:=ProcPriorRawInterval.interval hL hheight hr hs ha
  refine ⟨f,hfr,hfh,hfs,hff,he,?_,hfields⟩
  apply Classical.byContradiction
  intro hn
  let z:=f+5+24*cv tr t f count+31
  obtain ⟨hz,hsz,haz,hhz,hoz,_⟩:=ProcPriorRawFrameExtent.sanity_rows hL hfh hfs hff 31 (by decide)
  have hzr:z+1≤r:=by dsimp [z];omega
  have hzn:z+1<tr.height t:=by omega
  have hact:= (hactive (z+1) (by dsimp [z];omega) hzr).2
  have hfirst:=hnotfirst (z+1) (by dsimp [z];omega) hzr
  have hk:=kinds hL hz hsz
  have heq:cv tr t z offset=4*cv tr t z hdr+23*cv tr t z rec+31*cv tr t z hash:=by
    change cv tr t z act=cv tr t z hdr+cv tr t z rec+cv tr t z hash at hk
    change cv tr t z act=1 at haz
    change cv tr t z hash=1 at hhz
    change cv tr t z offset=31 at hoz
    omega
  have hend:=ProcPriorRawPhase.endpoint hL hz hsz haz heq
  have hnd:=ProcPriorRawOrigin.not_done hL hzn hsz hact hfirst
  change cv tr t z hash=0 ∨ cv tr t z phaseEnd=0 at hnd
  change cv tr t z hash=1 at hhz
  change cv tr t z phaseEnd=1 at hend
  omega

theorem record_row (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hheight:tr.height t≤2013265921)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hrec:cv tr t r rec=1) :
    ∃f,f≤r ∧ f<tr.height t ∧ cv tr t f (ProcPriorVertical4Linear.stage 2)=1 ∧
      cv tr t f first=1 ∧ r=f+5+24*cv tr t r record+cv tr t r offset ∧
      cv tr t r record<cv tr t f count ∧ cv tr t r offset<24 ∧
      (∀x∈[tau,vid,present,count],cv tr t r x=cv tr t f x) := by
  have hk:=kinds hL hr hs
  have hab:=flag hL hr hs act (by simp)
  have ha:cv tr t r act=1:=by omega
  obtain ⟨f,hfr,hfh,hfs,hff,he,hbound,hfields⟩:=frame hL hheight hr hs ha
  have hlow:5≤cv tr t r pos:=by
    apply Classical.byContradiction
    intro hn
    obtain ⟨hh,haa,ho⟩:=ProcPriorRawPhase.first_header hL hfh hfs hff
    have hkind:=kinds hL hfh hfs
    have hlast:4=4*cv tr t f hdr+23*cv tr t f rec+31*cv tr t f hash:=by omega
    obtain ⟨_,_,_,_,hphase⟩:=ProcPriorRawPhase.traverse hL hfh hfs haa ho 4 hlast (cv tr t r pos) (by omega)
    have hheader:cv tr t r hdr=1:=by
      rw [he];exact (hphase hdr (by simp)).trans hh
    omega
  have hu:cv tr t r pos<5+24*cv tr t f count:=by
    apply Classical.byContradiction
    intro hn
    have hj:cv tr t r pos-(5+24*cv tr t f count)<32:=by omega
    obtain ⟨_,_,_,hh,_,_⟩:=ProcPriorRawFrameExtent.sanity_rows hL hfh hfs hff _ hj
    have hrow:f+5+24*cv tr t f count+(cv tr t r pos-(5+24*cv tr t f count))=r:=by omega
    rw [hrow] at hh
    omega
  let k:=(cv tr t r pos-5)/24
  let j:=(cv tr t r pos-5)%24
  have hklt:k<cv tr t f count:=by dsimp [k];omega
  have hjlt:j<24:=by dsimp [j];omega
  have hrow:f+5+24*k+j=r:=by dsimp [k,j];omega
  obtain ⟨_,_,_,_,hj,hk',_,_⟩:=ProcPriorRawRecordPosition.bytes hL hfh hfs hff hheight k j hklt hjlt
  try dsimp only at hj hk'
  rw [hrow] at hj hk'
  refine ⟨f,hfr,hfh,hfs,hff,?_,?_,?_,hfields⟩ <;> omega
end ZkFormal.NearV3.Candidates.ProcPriorRawClassify
