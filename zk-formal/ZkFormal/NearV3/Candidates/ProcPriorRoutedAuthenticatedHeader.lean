import ZkFormal.NearV3.Candidates.ProcPriorRoutedValueRange
import ZkFormal.NearV3.Candidates.ProcPriorRoutedHeaderDecode
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedAuthenticatedHeader
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame
open ProcPriorRoutedRawSource (raw)
theorem count_bytes {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpubS:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
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
    let bs:=(es[ZkFormal.Chacha.cv (raw tr) 0 r vid]!).bytes
    ZkFormal.Chacha.cv (raw tr) 0 r count=bs.getD 1 0+256*bs.getD 2 0+65536*bs.getD 3 0 ∧
      ZkFormal.Chacha.cv (raw tr) 0 r count<16777216 := by
  have hb:=ProcPriorRoutedValueRange.bytes hH htables hpubS hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubVP
  exact ProcPriorRoutedHeaderDecode.count_bytes hH htables hpubV hVW hV hb hr hs hf hp
end ZkFormal.NearV3.Candidates.ProcPriorRoutedAuthenticatedHeader
