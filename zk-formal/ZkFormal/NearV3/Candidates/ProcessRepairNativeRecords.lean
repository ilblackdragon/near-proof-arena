import ZkFormal.NearV3.Candidates.ProcessRepairDecodedRecords
namespace ZkFormal.NearV3.Candidates.ProcessRepairNativeRecords
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame
open ProcPriorRoutedRawSource (raw)
theorem records {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    (hf:ZkFormal.Chacha.cv (raw tr) 0 r first=1) (hp:ZkFormal.Chacha.cv (raw tr) 0 r present=1) :
    ∃bs:NearSpec.Bytes,∃st:NearSpec.Bandwidth.State,
      bs.map UInt8.toNat=(es[ZkFormal.Chacha.cv (raw tr) 0 r vid]!).bytes ∧
      NearSpec.Bandwidth.State.decode bs=some st ∧
      st.links.length=ZkFormal.Chacha.cv (raw tr) 0 r count ∧ st.sanityHash.length=32 ∧
      (∀k j,∀link:NearSpec.Bandwidth.LinkAllowance,st.links[k]?=some link→j<24→
        ZkFormal.Chacha.cv (raw tr) 0 (r+5+24*k+j) byte=(link.encode.getD j 0).toNat) ∧
      ∀j,j<32→ZkFormal.Chacha.cv (raw tr) 0 (r+5+24*ZkFormal.Chacha.cv (raw tr) 0 r count+j) byte=(st.sanityHash.getD j 0).toNat := by
  obtain ⟨bs,st,hbytes,hd,hc,hh⟩:=ProcessRepairNativeDecode.decode view hpubS hpubL hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubVP hr hs hf hp
  refine ⟨bs,st,hbytes,hd,hc,hh,?_,?_⟩
  · intro k j link hk hj
    exact ProcessRepairDecodedRecords.record_byte view hpubV hVW hV hr hs hf hp hbytes hd hc k j hk hj
  · intro j hj
    exact ProcessRepairDecodedRecords.sanity_byte view hpubV hVW hV hr hs hf hp hbytes hd hc j hj
end ZkFormal.NearV3.Candidates.ProcessRepairNativeRecords
