import ZkFormal.NearV3.Candidates.ProcessRepairRawNativeRecordFull
import ZkFormal.NearV3.Candidates.ProcPriorRawTauUnique
import ZkFormal.NearV3.Candidates.ProcessRepairRecordWordSources
import ZkFormal.NearV3.Candidates.ProcPriorRecordNativeField
import ZkFormal.NearV3.Candidates.ProcPriorDecodedIdentity
namespace ZkFormal.NearV3.Candidates.ProcessRepairNativeWord
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame
open ProcPriorRoutedRawSource (raw)
theorem word {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpubS:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (hpubL:∀msg,pubCount AP pub 73 true msg=0)
    (hpubV:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    (hpubD:∀msg,pubCount AP pub B_DIGEST true msg=0)
    (hpubB:∀msg,pubCount AP pub B_BYTES true msg=0)
    (hpubC:∀seg∈AP.pubSegs,seg.bus≠64 ∧ seg.bus≠65 ∧ seg.bus≠66)
    (I:PubIdx AP pub Fp.ofNat) {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hprep:NearSpecV3.prepD0 cb hint=.ok p) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    {vs:List NodeS3} {es:List ValE}
    (hNW:NodeWf3 vs) (hVW:ValWf es)
    (hN:TableTraffic NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub (nodeTraffic3 vs))
    (hV:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    {v:List UpsSeg} (hw:Render.UpsRelay.Extract.Wf v) {hs:List HeadE} {K:Nat} {r0 rK:List Nat}
    (hchain:RootChain hs (v.map UpsRows.upsE) K r0 rK) (hK:K<33)
    (hU:TableTraffic Render.UpsRelay.compactInteractions (ProcPriorRoutedUpsView.ups tr) 0 pub (upsTraffic v))
    (hpubR:∀msg,pubCount AP pub 75 true msg=0)
    (hpubVP:∀seg∈AP.pubSegs,seg.bus≠B_VPARENT)
    {r:Nat} (hr:r<tr.height 0)
    (hs:ZkFormal.Chacha.cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (hf:ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.firstLimb=1) :
    ∃f,∃bs:NearSpec.Bytes,∃st:NearSpec.Bandwidth.State,∃link:NearSpec.Bandwidth.LinkAllowance,
      f<tr.height 0 ∧ ZkFormal.Chacha.cv (raw tr) 0 f first=1 ∧
      ZkFormal.Chacha.cv (raw tr) 0 f tau=ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.tau ∧
      bs.map UInt8.toNat=(es[ZkFormal.Chacha.cv (raw tr) 0 f vid]!).bytes ∧
      NearSpec.Bandwidth.State.decode bs=some st ∧
      st.links[ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.record]?=some link ∧
      ProcPriorRecordSummarySound.word (raw tr) 0 r=ProcPriorRecordNativeField.selected (raw tr) 0 r link ∧
      ProcPriorSummary.low (ProcPriorRecordNativeField.selected (raw tr) 0 r link)=ZkFormal.Chacha.cv (raw tr) 0 (r+2) ProcPriorRecordTable.lo ∧
      ProcPriorSummary.big (ProcPriorRecordNativeField.selected (raw tr) 0 r link)=decide (ZkFormal.Chacha.cv (raw tr) 0 (r+2) ProcPriorRecordTable.big=1) ∧
      ∀fair:Nat,(if ZkFormal.Chacha.cv (raw tr) 0 (r+2) ProcPriorRecordTable.big=1 then 4500000 else min (ZkFormal.Chacha.cv (raw tr) 0 (r+2) ProcPriorRecordTable.lo+fair) 4500000)=
        min (min (ProcPriorRecordNativeField.selected (raw tr) 0 r link+fair) NearSpecV3.Scheduler.u64Max) 4500000 := by
  have hv:=ProcessRepairRawBytes.overlay_local view
  have hh:(raw tr).height 0≤2013265921:=by
    have h:tr.height 0≤2^22:=Nat.pow_le_pow_right (by decide) (ProcessRepairTrieViews.value_local view).log_le
    exact Nat.le_trans h (by decide)
  have sources:=ProcessRepairRecordWordSources.bytes view hpubR hr hs hf
  obtain ⟨q,hq,hqs,hqr,_,hqt,hqk,_,_⟩:=sources 0 (by decide)
  obtain ⟨f,bs,st,link,_,hfh,hfs,hff,hqv,hqtf,hbs,hd,hlink,_,_⟩:=
    ProcessRepairRawNativeRecordFull.record_byte view hpubS hpubL hpubV hpubD hpubB hpubC
      I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubVP hq hqs hqr
  have hlink0:st.links[ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.record]?=some link:=by
    rw [←hqk];exact hlink
  have bytes:∀j,j<8→ZkFormal.Chacha.cv (raw tr) 0 (r+j/3) (ProcPriorRecordTable.byte0+j%3)=
      (link.encode.getD (ProcPriorRecordWordLayout.base (raw tr) 0 r+j) 0).toNat:=by
    intro j hj
    obtain ⟨qj,hqj,hsj,hrj,_,htj,hkj,hoj,hbj⟩:=sources j hj
    obtain ⟨fj,bsj,stj,linkj,_,hfj,hfsj,hffj,hvj,htfj,hbsj,hdj,hlinkj,_,hbytej⟩:=
      ProcessRepairRawNativeRecordFull.record_byte view hpubS hpubL hpubV hpubD hpubB hpubC
        I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubVP hqj hsj hrj
    have hfe:fj=f:=ProcPriorRawTauUnique.first_unique hv hh hfj hfh hfsj hfs hffj hff
      (htfj.symm.trans (htj.trans (hqt.symm.trans hqtf)))
    have hve:ZkFormal.Chacha.cv (raw tr) 0 qj vid=ZkFormal.Chacha.cv (raw tr) 0 q vid:=by rw [hvj,hqv,hfe]
    have hsame:bsj.map UInt8.toNat=bs.map UInt8.toNat:=by rw [hbsj,hbs,hve]
    have hlj:stj.links[ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.record]?=some linkj:=by rw [←hkj];exact hlinkj
    have he:=ProcPriorDecodedIdentity.record bsj bs stj st linkj link _ hsame hdj hd hlj hlink0
    rw [he,hoj] at hbytej
    exact hbj.symm.trans hbytej
  have hm:link∈st.links:=List.mem_of_getElem? hlink0
  have hsem:=ProcPriorRecordNativeField.decoded hv hr hs hf bs st hd link hm bytes
  refine ⟨f,bs,st,link,hfh,hff,hqtf.symm.trans hqt,?_,hd,hlink0,hsem⟩
  rw [←hqv];exact hbs
end ZkFormal.NearV3.Candidates.ProcessRepairNativeWord
