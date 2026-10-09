import ZkFormal.NearV3.Candidates.ProcPriorRoutedKeySound
import ZkFormal.NearV3.Candidates.ProcPriorRoutedWalkBalance
import ZkFormal.NearV3.Candidates.ProcPriorRoutedNodeBytes
import ZkFormal.NearV3.Candidates.ProcPriorRoutedValueHash
import ZkFormal.NearV3.Link.NodeHash3
import ZkFormal.NearV3.Link.Dag3
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedForestLookup
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched
open Link3
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem lookup {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    (hHeadW:HeadWf hs) (hHead:TableTraffic HeadV3.interactions tr 1 pub (headTraffic hs))
    (hpubP:∀seg∈AP.pubSegs,seg.bus≠B_PARENT)
    (hpubVP:∀seg∈AP.pubSegs,seg.bus≠B_VPARENT)
    (hpubE:∀seg∈AP.pubSegs,seg.bus≠B_EDGE)
    (hpubBM:∀seg∈AP.pubSegs,seg.bus≠B_BMAP)
    (hpubKN:∀msg,pubCount AP pub B_KEYNIB true msg=0)
    {ws:List WalkR} (hW:WalkWf3 ws) (hWr:(ws.flatMap (·.steps)).length≤2^21)
    (hWT:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws))
    {wv:WalkR} (hwv:wv∈UpsRows.allWalks ws v) :
    ∃h∈hs,h.tau=wv.tau ∧
      (wv.fk=FK_VAL→(fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find wv.key3=
        some (some (valOf (valsOf3 vs es) (vpos (vid0 es) wv.k)))) ∧
      (wv.fk=FK_ABS→(fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find wv.key3=some none) := by
  have hpar:=ProcPriorRoutedParent.balance hH htables hpubP hN hHead
  have hvb:=ProcPriorRoutedVParent.balance hH htables hpubVP hN hV
  have hbytes:=ProcPriorRoutedNodeBytes.bytes hH htables hpubS hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hHeadW hHead hpubP
  have hE:=ProcPriorRoutedWalkBalance.balance hH htables (Or.inl rfl) hpubE hN hHead hWT hU
  have hBM:=ProcPriorRoutedWalkBalance.balance hH htables (Or.inr rfl) hpubBM hN hHead hWT hU
  have hKN:=ProcPriorRoutedKeySound.keynib_ok hH htables hpubKN hW hWT
  have G:=Render.UpsRelay.Extract.ups_walkHyp hNW hHeadW hVW hW hWr hw hpar hvb hE hBM hKN hbytes (valsOf3 vs es)
  exact Walk3.walk3_find_of G hwv
end ZkFormal.NearV3.Candidates.ProcPriorRoutedForestLookup
