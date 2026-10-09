import ZkFormal.NearV3.Candidates.ProcessRepairNativeRecords
import ZkFormal.NearV3.Candidates.ProcPriorRawClassify
namespace ZkFormal.NearV3.Candidates.ProcessRepairRawNativeRecordFull
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame
open ProcPriorRoutedRawSource (raw)
theorem record_byte {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    (hpubVP:∀seg∈AP.pubSegs,seg.bus≠B_VPARENT)
    {r:Nat} (hr:r<tr.height 0)
    (hs:ZkFormal.Chacha.cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (hrecord:ZkFormal.Chacha.cv (raw tr) 0 r rec=1) :
    ∃f,∃bs:NearSpec.Bytes,∃st:NearSpec.Bandwidth.State,∃link:NearSpec.Bandwidth.LinkAllowance,
      f≤r ∧ f<tr.height 0 ∧ ZkFormal.Chacha.cv (raw tr) 0 f (ProcPriorVertical4Linear.stage 2)=1 ∧
      ZkFormal.Chacha.cv (raw tr) 0 f first=1 ∧
      ZkFormal.Chacha.cv (raw tr) 0 r vid=ZkFormal.Chacha.cv (raw tr) 0 f vid ∧
      ZkFormal.Chacha.cv (raw tr) 0 r tau=ZkFormal.Chacha.cv (raw tr) 0 f tau ∧
      bs.map UInt8.toNat=(es[ZkFormal.Chacha.cv (raw tr) 0 r vid]!).bytes ∧
      NearSpec.Bandwidth.State.decode bs=some st ∧
      st.links[ZkFormal.Chacha.cv (raw tr) 0 r record]?=some link ∧
      ZkFormal.Chacha.cv (raw tr) 0 r offset<24 ∧
      ZkFormal.Chacha.cv (raw tr) 0 r byte=(link.encode.getD (ZkFormal.Chacha.cv (raw tr) 0 r offset) 0).toNat := by
  have hv:=ProcessRepairRawBytes.overlay_local view
  have hh:(raw tr).height 0≤2013265921:=by
    have h:tr.height 0≤2^22:=Nat.pow_le_pow_right (by decide) (ProcessRepairTrieViews.value_local view).log_le
    exact Nat.le_trans h (by decide)
  obtain ⟨f,hfr,hfh,hfs,hff,hrow,hk,hj,hfields⟩:=ProcPriorRawClassify.record_row hv hh hr hs hrecord
  have hpres:ZkFormal.Chacha.cv (raw tr) 0 f present=1:=by
    have hb:=ProcPriorRawSound.flag hv hfh hfs present (by simp)
    by_cases hz:ZkFormal.Chacha.cv (raw tr) 0 f present=0
    · have hc:=(ProcPriorRawSound.absent_zero hv hfh hfs hz).2
      omega
    · omega
  obtain ⟨bs,st,hbytes,hd,hcount,_,hrecords,_⟩:=ProcessRepairNativeRecords.records view hpubS hpubL hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubVP hfh hfs hff hpres
  have hk':ZkFormal.Chacha.cv (raw tr) 0 r record<st.links.length:=by omega
  let link:=st.links[ZkFormal.Chacha.cv (raw tr) 0 r record]
  have hlink:st.links[ZkFormal.Chacha.cv (raw tr) 0 r record]?=some link:=List.getElem?_eq_getElem hk'
  have hbyte:=hrecords _ _ link hlink hj
  rw [←hrow] at hbyte
  refine ⟨f,bs,st,link,hfr,hfh,hfs,hff,hfields vid (by simp),hfields tau (by simp),?_,hd,hlink,hj,hbyte⟩
  rw [hfields vid (by simp)]
  exact hbytes
end ZkFormal.NearV3.Candidates.ProcessRepairRawNativeRecordFull
