import ZkFormal.NearV3.Candidates.ProcessRepairNativeMemoryWrite
namespace ZkFormal.NearV3.Candidates.ProcessRepairNativeWriteState
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame
open ProcPriorRoutedRawSource (raw)
open ProcPriorCodecFamilyLastWrite (memory)
theorem coherent {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    {r:Nat} (hr:r<tr.height 0)
    (ha:ProcPriorVerticalLastWrite.Live (memory tr) 0 r)
    (hq:ZkFormal.Chacha.cv (memory tr) 0 r ProcPriorMemoryTable.query=0):
    ∃f,∃bs:NearSpec.Bytes,∃st:NearSpec.Bandwidth.State,
      f<tr.height 0 ∧ ZkFormal.Chacha.cv (raw tr) 0 f (ProcPriorVertical4Linear.stage 2)=1 ∧
      ZkFormal.Chacha.cv (raw tr) 0 f first=1 ∧
      ZkFormal.Chacha.cv (raw tr) 0 f tau=ZkFormal.Chacha.cv (memory tr) 0 r ProcPriorMemoryTable.tau ∧
      bs.map UInt8.toNat=(es[ZkFormal.Chacha.cv (raw tr) 0 f vid]!).bytes ∧
      NearSpec.Bandwidth.State.decode bs=some st ∧
      ∀u,u<tr.height 0→ProcPriorVerticalLastWrite.Live (memory tr) 0 u→
        ZkFormal.Chacha.cv (memory tr) 0 u ProcPriorMemoryTable.query=0→
        ZkFormal.Chacha.cv (memory tr) 0 u ProcPriorMemoryTable.tau=ZkFormal.Chacha.cv (memory tr) 0 r ProcPriorMemoryTable.tau→
        ∃link:NearSpec.Bandwidth.LinkAllowance,
          st.links[ZkFormal.Chacha.cv (memory tr) 0 u ProcPriorMemoryTable.stamp]?=some link ∧
          ProcPriorSummary.low link.allowance=ZkFormal.Chacha.cv (memory tr) 0 u ProcPriorMemoryTable.lo ∧
          ProcPriorSummary.big link.allowance=decide (ZkFormal.Chacha.cv (memory tr) 0 u ProcPriorMemoryTable.hi=1) ∧
          ∀fair:Nat,(if ZkFormal.Chacha.cv (memory tr) 0 u ProcPriorMemoryTable.hi=1 then 4500000 else min (ZkFormal.Chacha.cv (memory tr) 0 u ProcPriorMemoryTable.lo+fair) 4500000)=
            min (min (link.allowance+fair) NearSpecV3.Scheduler.u64Max) 4500000 := by
  obtain ⟨f,bs,st,link,hfh,hfs,hff,htau,hbs,hd,_⟩:=ProcessRepairNativeMemoryWrite.row view hpubS hpubL hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubR hpubVP hpubW hr ha hq
  refine ⟨f,bs,st,hfh,hfs,hff,htau,hbs,hd,?_⟩
  intro u hu hua huq hut
  obtain ⟨g,cs,su,lu,hgh,hgs,hgf,hgt,hcs,hdu,hlu,hlo,hbig,hfair⟩:=ProcessRepairNativeMemoryWrite.row view hpubS hpubL hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubR hpubVP hpubW hu hua huq
  have hv:=ProcessRepairRawBytes.overlay_local view
  have hh:(raw tr).height 0≤2013265921:=by
    have h:tr.height 0≤2^22:=Nat.pow_le_pow_right (by decide) (ProcessRepairTrieViews.value_local view).log_le
    exact Nat.le_trans h (by decide)
  have hgf_eq:g=f:=ProcPriorRawTauUnique.first_unique hv hh hgh hfh hgs hfs hgf hff
    (hgt.trans (hut.trans htau.symm))
  have hbytes:cs.map UInt8.toNat=bs.map UInt8.toNat:=by rw [hcs,hbs,hgf_eq]
  have hstate:su=st:=ProcPriorDecodedIdentity.state cs bs su st hbytes hdu hd
  rw [hstate] at hlu
  exact ⟨lu,hlu,hlo,hbig,hfair⟩
end ZkFormal.NearV3.Candidates.ProcessRepairNativeWriteState
