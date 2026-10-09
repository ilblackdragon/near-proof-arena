import ZkFormal.NearV3.Candidates.ProcessRepairNativePriorRead
namespace ZkFormal.NearV3.Candidates.ProcessRepairNativeFrameRead
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame
open ProcPriorRoutedRawSource (raw)
open ProcPriorCodecFamilyLastWrite (memory)
open ProcPriorVerticalLastWrite (Live Result)
theorem consumer {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    (hpubW:∀msg,pubCount AP pub 67 true msg=0)
    (hpub68:∀msg,pubCount AP pub 68 true msg=0)
    (hpub40:∀seg∈AP.pubSegs,seg.bus≠40)
    (h68:∀seg∈AP.pubSegs,seg.bus≠68)
    (hpub70:∀msg,pubCount AP pub 70 true msg=0)
    (hpub72:∀msg,pubCount AP pub 72 true msg=0)
    (hpub76:∀msg,pubCount AP pub 76 true msg=0)
    {f:Nat} (hf:f<tr.height 0)
    (hfs:ZkFormal.Chacha.cv (raw tr) 0 f (ProcPriorVertical4Linear.stage 2)=1)
    (hff:ZkFormal.Chacha.cv (raw tr) 0 f first=1)
    (hfp:ZkFormal.Chacha.cv (raw tr) 0 f present=1)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=68) (hsend:i.send=false)
    (hm:i.multNat tr t r pub≠0):
    ∃bs:NearSpec.Bytes,∃st:NearSpec.Bandwidth.State,
      bs.map UInt8.toNat=(es[ZkFormal.Chacha.cv (raw tr) 0 f vid]!).bytes ∧
      NearSpec.Bandwidth.State.decode bs=some st ∧
      ∃q,q<tr.height 0 ∧ Live (memory tr) 0 q ∧
      ProcPriorVerticalReadSound.read.msgVal (memory tr) 0 q pub=i.msgVal tr t r pub ∧ Result (memory tr) 0 q ∧
      (ZkFormal.Chacha.cv (memory tr) 0 q ProcPriorMemoryTable.tau=ZkFormal.Chacha.cv (raw tr) 0 f tau→
       (ZkFormal.Chacha.cv (memory tr) 0 q ProcPriorMemoryTable.lo=0 ∧ ZkFormal.Chacha.cv (memory tr) 0 q ProcPriorMemoryTable.hi=0) ∨
       ∃k,∃link:NearSpec.Bandwidth.LinkAllowance,
        st.links[k]?=some link ∧
        ProcPriorSummary.low link.allowance=ZkFormal.Chacha.cv (memory tr) 0 q ProcPriorMemoryTable.lo ∧
        ProcPriorSummary.big link.allowance=decide (ZkFormal.Chacha.cv (memory tr) 0 q ProcPriorMemoryTable.hi=1) ∧
        (∀fair:Nat,(if ZkFormal.Chacha.cv (memory tr) 0 q ProcPriorMemoryTable.hi=1 then 4500000 else min (ZkFormal.Chacha.cv (memory tr) 0 q ProcPriorMemoryTable.lo+fair) 4500000)=
          min (min (link.allowance+fair) NearSpecV3.Scheduler.u64Max) 4500000) ∧
        ∀u,u<tr.height 0→Live (memory tr) 0 u→ZkFormal.Chacha.cv (memory tr) 0 u ProcPriorMemoryTable.query=0→
          ProcPriorAddressOrder.address (memory tr) 0 u=ProcPriorAddressOrder.address (memory tr) 0 q→
          ZkFormal.Chacha.cv (memory tr) 0 u ProcPriorMemoryTable.stamp≤k) := by
  obtain ⟨bs,st,hbs,hd,_⟩:=ProcessRepairNativeRecords.records view hpubS hpubL hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubVP hf hfs hff hfp
  obtain ⟨q,hq,hqa,hmsg,hresult,hvalue⟩:=ProcessRepairNativePriorRead.consumer view
    hpubS hpubL hpubV hpubD hpubB hpubC I hprep fwd hrec hNW hVW hN hV hw hchain hK hU
    hpubR hpubVP hpubW hpub68 hpub40 h68 hpub70 hpub72 hpub76 ht hr hi hb hsend hm
  refine ⟨bs,st,hbs,hd,q,hq,hqa,hmsg,hresult,?_⟩
  intro hqt
  rcases hvalue with hz|⟨w,g,cs,su,link,_,hg,hgs,hgf,hgt,hcs,hdu,hlink,hlo,hbig,hfair,hmax,_⟩
  · exact Or.inl hz
  · have hh:(raw tr).height 0≤2013265921:=by
      have h:tr.height 0≤2^22:=Nat.pow_le_pow_right (by decide) (ProcessRepairTrieViews.value_local view).log_le
      exact Nat.le_trans h (by decide)
    have he:g=f:=ProcPriorRawTauUnique.first_unique (ProcessRepairRawBytes.overlay_local view) hh hg hf hgs hfs hgf hff (hgt.trans hqt)
    have hbytes:cs.map UInt8.toNat=bs.map UInt8.toNat:=by rw [hcs,hbs,he]
    have hstate:su=st:=ProcPriorDecodedIdentity.state cs bs su st hbytes hdu hd
    rw [hstate] at hlink
    exact Or.inr ⟨_,link,hlink,hlo,hbig,hfair,hmax⟩
end ZkFormal.NearV3.Candidates.ProcessRepairNativeFrameRead
