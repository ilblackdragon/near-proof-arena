import ZkFormal.NearV3.Candidates.ProcPriorRoutedGlobalForestBytes
import ZkFormal.NearV3.Candidates.ProcPriorForestPreimage
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedForestDigest
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem node_digest {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    {n:Nat} (hn:n<vs.length)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=B_DIGEST) (hsend:i.send=false)
    (hm:i.multNat tr t r pub≠0)
    (hjob:(i.msgVal tr t r pub)[0]! =Fp.ofNat (msgId K_NPRE n))
    (hsize:(i.msgVal tr t r pub)[1]!.toNat=(vs[n].v.ser false).length) :
    ∃bs:NearSpec.Bytes,bs.map UInt8.toNat=vs[n].v.ser false ∧
      i.msgVal tr t r pub=[Fp.ofNat (msgId K_NPRE n),Fp.ofNat bs.length]++
        (NearSpec.sha256 bs).map (fun x=>Fp.ofNat x.toNat) := by
  obtain ⟨id,bs,he,hbytes⟩:=ProcPriorRoutedShaByteSource.consumer hH htables hpubD hpubB ht hr hi hb hsend hm
  have hid:id=Fp.ofNat (msgId K_NPRE n):=by
    rw [he] at hjob
    exact hjob
  rw [hid] at he hbytes
  have hlen:(Fp.ofNat bs.length).toNat=(vs[n].v.ser false).length:=by
    rw [he] at hsize
    exact hsize
  have hprov:∀j,j<bs.length→ProcPriorForestByteIdentity.Provider (vs:=vs) (es:=es)
      [Fp.ofNat (msgId K_NPRE n),Fp.ofNat j,Fp.ofNat (bs.getD j 0).toNat] := by
    intro j hj
    obtain ⟨t',ht',r',hr',i',hi',hb',hs',he',hm'⟩:=hbytes j hj
    have htag:(Fp.ofNat (msgId K_NPRE n)).toNat%16=7:=
      (ProcPriorForestByteIdentity.node_id hNW hn (k:=K_NPRE) (by decide)).2
    exact ProcPriorRoutedGlobalForestBytes.provider hH htables hpubS hpubV hpubC I hprep fwd hrec
      hN hV hw hchain hK hU (Or.inl htag) ht' hr' hi' hb' hs' hm' he'
  exact ⟨bs,ProcPriorForestPreimage.node_pre hNW hVW hn hlen hprov,he⟩

theorem value_digest {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    {n:Nat} (hn:n<es.length)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=B_DIGEST) (hsend:i.send=false)
    (hm:i.multNat tr t r pub≠0)
    (hjob:(i.msgVal tr t r pub)[0]! =Fp.ofNat (msgId K_VPRE n))
    (hsize:(i.msgVal tr t r pub)[1]!.toNat=es[n].bytes.length) :
    ∃bs:NearSpec.Bytes,bs.map UInt8.toNat=es[n].bytes ∧
      i.msgVal tr t r pub=[Fp.ofNat (msgId K_VPRE n),Fp.ofNat bs.length]++
        (NearSpec.sha256 bs).map (fun x=>Fp.ofNat x.toNat) := by
  obtain ⟨id,bs,he,hbytes⟩:=ProcPriorRoutedShaByteSource.consumer hH htables hpubD hpubB ht hr hi hb hsend hm
  have hid:id=Fp.ofNat (msgId K_VPRE n):=by
    rw [he] at hjob
    exact hjob
  rw [hid] at he hbytes
  have hlen:(Fp.ofNat bs.length).toNat=es[n].bytes.length:=by
    rw [he] at hsize
    exact hsize
  have hprov:∀j,j<bs.length→ProcPriorForestByteIdentity.Provider (vs:=vs) (es:=es)
      [Fp.ofNat (msgId K_VPRE n),Fp.ofNat j,Fp.ofNat (bs.getD j 0).toNat] := by
    intro j hj
    obtain ⟨t',ht',r',hr',i',hi',hb',hs',he',hm'⟩:=hbytes j hj
    have htag:(Fp.ofNat (msgId K_VPRE n)).toNat%16=9:=
      (ProcPriorForestByteIdentity.value_id hVW hn).2.2
    exact ProcPriorRoutedGlobalForestBytes.provider hH htables hpubS hpubV hpubC I hprep fwd hrec
      hN hV hw hchain hK hU (Or.inr (Or.inr htag)) ht' hr' hi' hb' hs' hm' he'
  exact ⟨bs,ProcPriorForestPreimage.value_pre hNW hVW hn hlen hprov,he⟩
end ZkFormal.NearV3.Candidates.ProcPriorRoutedForestDigest
