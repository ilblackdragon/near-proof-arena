import ZkFormal.NearV3.Candidates.ProcPriorRoutedHeadHash
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedKidHash
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem kid_hash {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    {q:Nat} (hq:q<vs.length) {c l rr:Nat} {pre po:List Nat}
    (hk:(c,l,rr,pre,po)∈vs[q].v.revealed) :
    ∃hn:c<vs.length,∃bs:NearSpec.Bytes,
      bs.map UInt8.toNat=vs[c].v.ser false ∧ pre=(NearSpec.sha256 bs).map UInt8.toNat := by
  have hpar:=ProcPriorRoutedParent.balance hH htables hpubP hN hHead
  obtain ⟨hn,htau,hdepth,hlen,hres⟩:=Link3.kid_link hNW hpar hq hk
  have hlenP:(vs[c].v.ser false).length<P:=by
    have:=Link3.ser_len_lt hNW hn;unfold P;omega
  rw [Nat.mod_eq_of_lt hlenP] at hlen
  have hmem:digMsg (msgId K_NPRE c) l pre∈nodeRecvs3 vs B_DIGEST:=by
    unfold nodeRecvs3;rw [if_pos rfl,List.mem_flatMap]
    refine ⟨(vs[q],q),Link3.zip_range_mem vs hq,List.mem_append_left _ ?_⟩
    rw [List.mem_flatMap]
    exact ⟨(c,l,rr,pre,po),hk,by simp⟩
  obtain ⟨r,hr,i,hi,hb,hsend,he,hm⟩:=ProcPriorRoutedForestRequests.node htables hN hmem
  have ht:0<AP.tables.length:=by rw [htables];decide +kernel
  have hjob:(i.msgVal tr 0 r pub)[0]! =Fp.ofNat (msgId K_NPRE c):=by rw [he];rfl
  have hsize:(i.msgVal tr 0 r pub)[1]!.toNat=(vs[c].v.ser false).length:=by
    rw [he]
    change (Fp.ofNat l).toNat=_
    rw [←hlen,Fp.toNat_ofNat,Nat.mod_eq_of_lt hlenP]
  obtain ⟨bs,hbytes,hhash⟩:=ProcPriorRoutedForestDigest.node_digest hH htables hpubS hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hn ht hr hi hb hsend hm hjob hsize
  have hdig:pre.map Fp.ofNat=(NearSpec.sha256 bs).map (fun x=>Fp.ofNat x.toNat):=by
    have hh:=congrArg (fun xs:List Fp=>xs.drop 2) (he.symm.trans hhash)
    simpa [Msg.toFp,digMsg] using hh
  have hd:∀x∈pre,x<P:=by
    intro x hx;apply hNW.canon _ (List.getElem_mem hq)
    cases hv:vs[q].v with
    | leaf => rw [hv] at hk;simp [NodeV3.revealed] at hk
    | ext k kid m =>
      rw [hv] at hk;cases kid <;>simp [NodeV3.revealed] at hk
      obtain ⟨rfl,rfl,rfl,rfl,rfl⟩:=hk;simp [NodeV3.raw,NKid.raw,hx]
    | branch sv kids m =>
      rw [hv] at hk
      simp only [NodeV3.revealed,List.mem_filterMap] at hk
      obtain ⟨kd,hkd,he⟩:=hk
      cases kd with
      | none => simp at he
      | hash _ => simp at he
      | node c' l' r' pre' po' =>
        simp at he;obtain ⟨-,-,-,h4,-⟩:=he;subst h4
        simp only [NodeV3.raw,List.mem_append,List.mem_flatMap]
        exact Or.inl (Or.inr ⟨_,hkd,by simp [NKid.raw,hx]⟩)
  have hnat:pre=(NearSpec.sha256 bs).map UInt8.toNat:=by
    apply ZkFormal.Near.Link.toFp_inj hd
    · intro x hx
      obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hx
      have:=UInt8.toNat_lt b;unfold P;omega
    · simpa only [Msg.toFp,List.map_map,Function.comp_def] using hdig
  exact ⟨hn,bs,hbytes,hnat⟩
end ZkFormal.NearV3.Candidates.ProcPriorRoutedKidHash
