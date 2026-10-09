import ZkFormal.NearV3.Candidates.ProcessRepairReceiptStorage
import ZkFormal.NearV3.Candidates.ProcessRepairReceiptArithmetic
import ZkFormal.NearV3.Candidates.ProcessRepairAccountNative
import ZkFormal.NearV3.Candidates.ProcessRepairQueuePublic
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptNativeArithmetic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open ZkFormal.NearV3.Sched RcptV3Proof
theorem authenticated {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    (hpubM:∀seg∈AP.pubSegs,seg.bus≠B_MEM)
    (hpubBR:∀msg,pubCount AP pub B_BYTES false msg=0)
    (overhead:Nat) (hpublic:pub=ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead))
    : ∃as:List AcctV,(as=[] ∨ AcctV3Wf as) ∧
      TableTraffic AcctV3.interactions tr 6 pub (acctV3Traffic as) ∧
      ∃bs:List RcptV3Proof.ListBlock,∃e:Nat,
      RcptV3Proof.ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e ∧
    let rs:=flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))
    ∃toks:List Nat,toks.length=rs.length+1 ∧ toks.head?=some 0 ∧
      ∀r,(hr:r<rs.length)→
      let x:=rs[r]
      Bytes8 x.bef ∧ Bytes8 x.lk ∧ Bytes8 x.st ∧
      leN' x.aft=leN' x.bef+leN' x.dep ∧ leN' x.aft<NearSpec.Params.u128Max ∧
      leN' x.aft+leN' x.lk<NearSpec.Params.two128 ∧
      (NearSpec.Params.storageAmountPerByte*leN' x.st≤leN' x.aft+leN' x.lk ∨
        leN' x.st≤NearSpec.Params.zeroBalanceStorageLimit) ∧
      x.ge=decide (leN' (pubBytes pub PH_GP 16)≤leN' x.gp) ∧
      leN' x.burnt=(if x.sys then 0 else NearSpec.Params.G*min (leN' x.gp) (leN' (pubBytes pub PH_GP 16))) ∧
      (x.hr=true↔x.sys=false ∧ NearSpec.Params.G*(leN' x.gp-min (leN' x.gp) (leN' (pubBytes pub PH_GP 16)))≠0) ∧
      (x.hr=true→leN' x.ramt=NearSpec.Params.G*(leN' x.gp-min (leN' x.gp) (leN' (pubBytes pub PH_GP 16)))) ∧
      toks.getD (r+1) 0=toks.getD r 0+leN' x.burnt ∧ toks.getD (r+1) 0<NearSpec.Params.two128 :=by
  obtain ⟨as,hwa,ha⟩:=ProcessRepairAccountView.accounts view
  have valueBytes:=ProcessRepairValueRange.bytes view hpubS hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubVP
  have initial:∀a∈as,Bytes8 a.pre:=by
    intro a ham
    obtain ⟨ev,hev,_,_,heq⟩:=ProcessRepairAccountComplete.value view hpubV hVW hV hwa ha ham
    rw [←heq]
    exact valueBytes ev hev
  have bgp:Bytes8 (pubBytes pub PH_GP 16):=by
    intro b hb
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hb
    rw [hpublic]
    exact ProcessRepairQueuePublic.public_byte p overhead _
  have hL:=Assembly.ReceiptCandidateProof.repaired_local_base (ProcessRepairForeignByteTags.local_receipt view)
  obtain ⟨bs,e,hc⟩:=Assembly.ReceiptCandidateProof.extract_lists hL
  have hm:=ProcessRepairReceiptMemory.context view hpubM hpubV hVW hV hwa ha hc
  refine ⟨as,hwa,ha,bs,e,hc,?_⟩
  obtain ⟨toks,hlen,hhead,har⟩:=ProcessRepairReceiptArithmetic.arithmetic view hpubM hpubBR hc hm initial bgp
  refine ⟨toks,hlen,hhead,?_⟩
  intro r hr
  obtain ⟨hb,hl,hs,ha,hmax,hsum,hstorage,htail⟩:=har r hr
  refine ⟨hb,hl,hs,ha,hmax,hsum,?_,htail⟩
  obtain ⟨other,_,_,hwf,_⟩:=ProcessRepairReceiptWf.tokens view hpubM hc
  have after:∀q,(hq:q<((flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).map RcptE.toRcptV).length)→
      Bytes8 ((flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).map RcptE.toRcptV)[q].aft:=by
    intro q hq
    simpa only [List.getElem_map] using (hwf q (by simpa using hq)).aft8
  have hlenst:=(hwf r hr).lens.2.2.2.2.2.2.2.1
  have hcheck:=ProcessRepairReceiptStorage.native_check hm initial after
    (r:=r) (by simpa using hr) (by simpa only [List.getElem_map] using hlenst)
    (by simpa only [List.getElem_map] using hstorage)
  simpa only [List.getElem_map] using hcheck
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptNativeArithmetic
