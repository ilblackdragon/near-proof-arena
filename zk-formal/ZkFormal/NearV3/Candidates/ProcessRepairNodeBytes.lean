import ZkFormal.NearV3.Candidates.ProcessRepairParent
import ZkFormal.NearV3.Candidates.ProcessRepairVParent
import ZkFormal.NearV3.Candidates.ProcessRepairKidHash
namespace ZkFormal.NearV3.Candidates.ProcessRepairNodeBytes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem bytes {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    :∀s∈vs,∀x∈s.v.ser false,x<256 := by
  have hpar:=ProcessRepairParent.balance view hpubP hN hHead
  intro s hs' x hx
  obtain ⟨n,hn,rfl⟩:=List.getElem_of_mem hs'
  rcases Link3.sender_of hNW hHeadW hpar hn with ⟨h,hh,hr,-,-⟩ | ⟨q,hq,l,rr,pre,po,hk,-,-⟩
  · obtain ⟨hn',bs,hbytes,hhash⟩:=ProcessRepairHeadHash.head_hash view hpubS hpubV hpubD hpubB hpubC
      I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hHeadW hHead hpubP hh
    subst hr
    rw [←hbytes] at hx
    obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hx
    exact UInt8.toNat_lt b
  · obtain ⟨hn',bs,hbytes,hhash⟩:=ProcessRepairKidHash.kid_hash view hpubS hpubV hpubD hpubB hpubC
      I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hHeadW hHead hpubP hq hk
    rw [←hbytes] at hx
    obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hx
    exact UInt8.toNat_lt b
end ZkFormal.NearV3.Candidates.ProcessRepairNodeBytes
