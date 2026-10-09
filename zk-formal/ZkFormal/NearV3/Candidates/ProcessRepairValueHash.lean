import ZkFormal.NearV3.Candidates.ProcessRepairParent
import ZkFormal.NearV3.Candidates.ProcessRepairVParent
import ZkFormal.NearV3.Candidates.ProcessRepairHeadHash
import ZkFormal.NearV3.Candidates.ProcessRepairVParent
import ZkFormal.NearV3.Candidates.ProcPriorRoutedValueNode
namespace ZkFormal.NearV3.Candidates.ProcessRepairValueHash
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem value_hash {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    {q:Nat} (hq:q<vs.length) {id len:Nat} {pre po:List Nat} {written:Bool}
    (hv:vs[q].v.value=some (id,len,pre,po,written)) :
    ∃hn:id<es.length,∃bs:NearSpec.Bytes,
      bs.map UInt8.toNat=es[id].bytes ∧ bs.length=len ∧
      pre=(NearSpec.sha256 bs).map UInt8.toNat := by
  have hvb:=ProcessRepairVParent.balance view hpubVP hN hV
  obtain ⟨hn,hid,hlen⟩:=ProcPriorRoutedValueNode.node_entry hNW hVW hvb hq hv
  rw [getElem!_pos es id hn] at hid hlen
  have hbl:es[id].bytes.length=len:=by
    have hsh:=hVW.shape _ (List.getElem_mem hn)
    cases hz:es[id].vz
    · rw [(hsh.2 hz).1,hlen]
    · rw [(hsh.1 hz).2,←hlen,(hsh.1 hz).1];rfl
  have hlenP:es[id].bytes.length<P:=by
    have hc:=hVW.canon es[id] (List.getElem_mem hn)
    have hsh:=hVW.shape es[id] (List.getElem_mem hn)
    cases hz:es[id].vz with
    | true=>have:=hsh.1 hz;simp_all
    | false=>have:=(hsh.2 hz).1;omega
  have hmem:digMsg (msgId K_VPRE id) len pre∈nodeRecvs3 vs B_DIGEST:=by
    unfold nodeRecvs3;rw [if_pos rfl,List.mem_flatMap]
    refine ⟨(vs[q],q),Link3.zip_range_mem vs hq,List.mem_append_right _ ?_⟩
    simp [hv]
  obtain ⟨r,hr,i,hi,hb,hsend,he,hm⟩:=ProcessRepairForestRequests.node view hN hmem
  have ht:0<AP.tables.length:=by rw [view.length];decide +kernel
  have hjob:(i.msgVal tr 0 r pub)[0]! =Fp.ofNat (msgId K_VPRE id):=by rw [he];rfl
  have hsize:(i.msgVal tr 0 r pub)[1]!.toNat=es[id].bytes.length:=by
    rw [he]
    change (Fp.ofNat len).toNat=_
    rw [←hbl,Fp.toNat_ofNat,Nat.mod_eq_of_lt hlenP]
  obtain ⟨bs,hbytes,hhash⟩:=ProcessRepairForestDigest.value_digest view hpubS hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hn ht hr hi hb hsend hm hjob hsize
  have hdig:pre.map Fp.ofNat=(NearSpec.sha256 bs).map (fun x=>Fp.ofNat x.toNat):=by
    have hh:=congrArg (fun xs:List Fp=>xs.drop 2) (he.symm.trans hhash)
    simpa [Msg.toFp,digMsg] using hh
  have hd:∀x∈pre,x<P:=by
    intro x hx;apply hNW.canon _ (List.getElem_mem hq)
    cases hvv:vs[q].v with
    | leaf k sl m =>
      rw [hvv] at hv
      cases sl with
      | ref => simp [NodeV3.value] at hv
      | val lb i' l' pr p' w' =>
        simp [NodeV3.value] at hv;obtain ⟨-,-,rfl,-⟩:=hv
        simp [NodeV3.raw,NSlot3.raw,hx]
    | ext => rw [hvv] at hv;simp [NodeV3.value] at hv
    | branch sv kids m =>
      rw [hvv] at hv
      cases sv with
      | none => simp [NodeV3.value] at hv
      | some sl =>
        cases sl with
        | ref => simp [NodeV3.value] at hv
        | val lb i' l' pr p' w' =>
          simp [NodeV3.value] at hv;obtain ⟨-,-,rfl,-⟩:=hv
          simp [NodeV3.raw,NSlot3.raw,hx]
  have hnat:pre=(NearSpec.sha256 bs).map UInt8.toNat:=by
    apply ZkFormal.Near.Link.toFp_inj hd
    · intro x hx
      obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hx
      have:=UInt8.toNat_lt b;unfold P;omega
    · simpa only [Msg.toFp,List.map_map,Function.comp_def] using hdig
  have hbs:bs.length=len:=by have:=congrArg List.length hbytes;simp only [List.length_map] at this;omega
  exact ⟨hn,bs,hbytes,hbs,hnat⟩
end ZkFormal.NearV3.Candidates.ProcessRepairValueHash
