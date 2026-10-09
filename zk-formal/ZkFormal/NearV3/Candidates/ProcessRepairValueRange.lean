import ZkFormal.NearV3.Candidates.ProcessRepairParent
import ZkFormal.NearV3.Candidates.ProcessRepairVParent
import ZkFormal.NearV3.Candidates.ProcessRepairValueHash
import ZkFormal.NearV3.Candidates.ProcessRepairVParent
import ZkFormal.NearV3.Candidates.ProcPriorRoutedValueNode
namespace ZkFormal.NearV3.Candidates.ProcessRepairValueRange
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem revealed {vs:List NodeS3} {es:List ValE}
    (hw:NodeWf3 vs) (hvw:ValWf es) (hb:Link3.VParentBal vs es)
    {t:Nat} (ht:t<es.length) :
    ∃n,∃hn:n<vs.length,∃pre po:List Nat,∃w:Bool,
      vs[n].v.value=some (es[t].vid,es[t].len,pre,po,w) := by
  have h1:0<Link3.cnt3 (valRecvs es B_VPARENT) (Msg.toFp [es[t].vid,es[t].len]):=by
    rw [Link3.cnt3,List.count_pos_iff,List.mem_map]
    refine ⟨[es[t].vid,es[t].len],?_,rfl⟩
    rw [Link3.vparentR,List.mem_map]
    exact ⟨es[t],List.getElem_mem ht,rfl⟩
  rw [←hb,Link3.cnt3,List.count_pos_iff,List.mem_map,Link3.vparentS] at h1
  obtain ⟨m,hm,he⟩:=h1
  rw [List.mem_flatMap] at hm
  obtain ⟨⟨sn,n⟩,hzn,hm⟩:=hm
  obtain ⟨hn,rfl⟩:=Link3.mem_zip_range hzn
  unfold Link3.vparMsg at hm
  cases hv:vs[n].v.value with
  | none => simp [hv] at hm
  | some v =>
    obtain ⟨id,len,pre,po,w⟩:=v
    simp only [hv,List.mem_singleton] at hm
    subst m
    obtain ⟨ri,rl⟩:=Link3.value_raw hv
    have cn:=hw.canon _ (List.getElem_mem hn)
    have ce:=hvw.canon _ (List.getElem_mem ht)
    simp only [Msg.toFp,List.map_cons,List.map_nil,List.cons.injEq,and_true] at he
    have hi:=Link3.ofNat_eq (cn id ri) ce.1 he.1
    have hl:=Link3.ofNat_eq (cn len rl) ce.2.1 he.2
    exact ⟨n,hn,pre,po,w,by simpa only [hi,hl] using hv⟩

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
    (hpubVP:∀seg∈AP.pubSegs,seg.bus≠B_VPARENT)
    :∀e∈es,∀x∈e.bytes,x<256 := by
  have hb:=ProcessRepairVParent.balance view hpubVP hN hV
  intro e he x hx
  obtain ⟨t,ht,rfl⟩:=List.getElem_of_mem he
  obtain ⟨n,hn,pre,po,w,hv⟩:=revealed hNW hVW hb ht
  have hid:=Link3.vid_small hVW ht
  rw [hid] at hv
  obtain ⟨ht',bs,hbytes,hbl,hhash⟩:=ProcessRepairValueHash.value_hash view hpubS hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubVP hn hv
  rw [←hbytes] at hx
  obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hx
  exact UInt8.toNat_lt b
end ZkFormal.NearV3.Candidates.ProcessRepairValueRange
