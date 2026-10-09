import ZkFormal.NearV3.Candidates.ProcPriorRecordPhysicalBytes
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordAuthenticatedWord
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRecordTable
open ProcPriorRoutedRawSource (raw)
theorem word_bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpubS:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (hpubR:∀msg,pubCount AP pub 75 true msg=0)
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
    (hs:ZkFormal.Chacha.cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (hf:ZkFormal.Chacha.cv (raw tr) 0 r firstLimb=1) :
    ZkFormal.Chacha.cv (raw tr) 0 r lo<16777216 ∧ ZkFormal.Chacha.cv (raw tr) 0 r mid<16777216 ∧
      ZkFormal.Chacha.cv (raw tr) 0 r hi<65536 ∧
      ZkFormal.Chacha.cv (raw tr) 0 r lo+16777216*ZkFormal.Chacha.cv (raw tr) 0 r mid+
        281474976710656*ZkFormal.Chacha.cv (raw tr) 0 r hi<18446744073709551616 := by
  have hbytes:=ProcPriorRoutedValueRange.bytes hH htables hpubS hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubVP
  exact ProcPriorRecordPhysicalBytes.word_bounds hH htables hpubV hpubR hVW hV hbytes hr hs hf
end ZkFormal.NearV3.Candidates.ProcPriorRecordAuthenticatedWord
