import ZkFormal.NearV3.Candidates.ProcPriorRoutedForestRequests
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedHeadHash
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem head_hash {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    {h:HeadE} (hh:h∈hs) :
    ∃hn:h.rid<vs.length,∃bs:NearSpec.Bytes,
      bs.map UInt8.toNat=vs[h.rid].v.ser false ∧ h.pre=(NearSpec.sha256 bs).map UInt8.toNat := by
  have hpar:=ProcPriorRoutedParent.balance hH htables hpubP hN hHead
  obtain ⟨hn,htau,hdepth,hlen,hres⟩:=Link3.head_link hNW hHeadW hpar hh
  have hlenP:(vs[h.rid].v.ser false).length<P:=by
    have:=Link3.ser_len_lt hNW hn;unfold P;omega
  rw [Nat.mod_eq_of_lt hlenP] at hlen
  have hmem:digMsg (msgId K_NPRE h.rid) h.rlen h.pre∈headRecvs hs B_DIGEST:=by
    simp only [headRecvs,ite_true,List.mem_flatMap]
    exact ⟨h,hh,by simp⟩
  obtain ⟨r,hr,i,hi,hb,hsend,he,hm⟩:=ProcPriorRoutedForestRequests.head htables hHead hmem
  have ht:1<AP.tables.length:=by rw [htables];decide +kernel
  have hjob:(i.msgVal tr 1 r pub)[0]! =Fp.ofNat (msgId K_NPRE h.rid):=by rw [he];rfl
  have hsize:(i.msgVal tr 1 r pub)[1]!.toNat=(vs[h.rid].v.ser false).length:=by
    rw [he]
    change (Fp.ofNat h.rlen).toNat=_
    rw [←hlen,Fp.toNat_ofNat,Nat.mod_eq_of_lt hlenP]
  obtain ⟨bs,hbytes,hhash⟩:=ProcPriorRoutedForestDigest.node_digest hH htables hpubS hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hn ht hr hi hb hsend hm hjob hsize
  have hdig:h.pre.map Fp.ofNat=(NearSpec.sha256 bs).map (fun x=>Fp.ofNat x.toNat):=by
    have hh:=congrArg (fun xs:List Fp=>xs.drop 2) (he.symm.trans hhash)
    simpa [Msg.toFp,digMsg] using hh
  have hnat:h.pre=(NearSpec.sha256 bs).map UInt8.toNat:=by
    apply ZkFormal.Near.Link.toFp_inj ((hHeadW.canon h hh).2.2.2.2.2.1)
    · intro x hx
      obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hx
      have:=UInt8.toNat_lt b;unfold P;omega
    · simpa only [Msg.toFp,List.map_map,Function.comp_def] using hdig
  exact ⟨hn,bs,hbytes,hnat⟩

theorem public_pre {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    (hpubP:∀seg∈AP.pubSegs,seg.bus≠B_PARENT) :
    ∃n:Nat,∃hn:n<vs.length,∃bs:NearSpec.Bytes,
      n=(headAt hs 0).rid ∧ bs.map UInt8.toNat=vs[n].v.ser false ∧
      r0=(NearSpec.sha256 bs).map UInt8.toNat := by
  have hh:headAt hs 0∈hs:=(hchain.head_mem 0 (by omega)).1
  obtain ⟨hn,bs,hbytes,hhash⟩:=head_hash hH htables hpubS hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hHeadW hHead hpubP hh
  exact ⟨(headAt hs 0).rid,hn,bs,rfl,hbytes,hchain.pre0.symm.trans hhash⟩
end ZkFormal.NearV3.Candidates.ProcPriorRoutedHeadHash
