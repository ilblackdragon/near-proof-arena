import ZkFormal.NearV3.Candidates.ProcessRepairParent
import ZkFormal.NearV3.Candidates.ProcessRepairVParent
import ZkFormal.NearV3.Candidates.ProcessRepairNodeBytes
import ZkFormal.NearV3.Candidates.ProcessRepairValueHash
import ZkFormal.NearV3.Link.NodeHash3
import ZkFormal.NearV3.Link.Dag3
namespace ZkFormal.NearV3.Candidates.ProcessRepairForestEncoding
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched
open Link3
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem encoding {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
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
    {h:HeadE} (hh:h∈hs) :
    ∀n,InInst (recsOf (vpos (vid0 es)) vs) h.tau n →∃hn:n<vs.length,
      nodeEnc (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) n)=Link3.toB (vs[n].v.ser false) ∧
      isNode (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) n)=true := by
  have hpar:=ProcessRepairParent.balance view hpubP hN hHead
  have hvb:=ProcessRepairVParent.balance view hpubVP hN hV
  have hbytes:=ProcessRepairNodeBytes.bytes view hpubS hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hHeadW hHead hpubP
  have hlen:=Link3.vlen_le hVW
  have hdag:=Link3.rootedDag3 hNW hHeadW hVW hpar hvb hlen hbytes hh
  apply Link3.enc_fullTree hdag hNW hbytes
  · intro q hq c l rr pre po hk
    obtain ⟨hc,bs,hbs,hhash⟩:=ProcessRepairKidHash.kid_hash view hpubS hpubV hpubD hpubB hpubC
      I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hHeadW hHead hpubP hq hk
    refine ⟨hc,?_⟩
    rw [←hbs,Link3.toB_toNat]
    exact hhash
  · intro q hq id len pre po written hv
    obtain ⟨hn,bs,hbs,hbl,hhash⟩:=ProcessRepairValueHash.value_hash view hpubS hpubV hpubD hpubB hpubC
      I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubVP hq hv
    obtain ⟨t,ht,hpos,hid,hl,hVt⟩:=Link3.val_pos hNW hVW hvb hlen hq hv
    have hti:t=id:=(Link3.vid_small hVW ht).symm.trans hid
    have hposId:vpos (vid0 es) id=id:=hpos.trans hti
    clear hpos
    subst t
    have he:valOf (valsOf3 vs es) (vpos (vid0 es) id)=bs:=by
      rw [hposId]
      have hh:valOf (valsOf3 vs es) id=Link3.toB es[id].bytes:=by simp [valOf,hVt]
      rw [hh,←hbs,Link3.toB_toNat]
    rw [he]
    exact ⟨hbl,hhash⟩
end ZkFormal.NearV3.Candidates.ProcessRepairForestEncoding
