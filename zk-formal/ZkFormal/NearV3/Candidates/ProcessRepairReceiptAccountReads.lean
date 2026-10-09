import ZkFormal.NearV3.Candidates.ProcessRepairReceiptLookup
import ZkFormal.NearV3.Candidates.ProcessRepairReceiptMemOrigin
import ZkFormal.NearV3.Candidates.ProcessRepairAccountNative
import ZkFormal.NearV3.Qv.Extract.NativeValueLookup
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptAccountReads
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open Sched Link3 RcptV3Proof

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
    (hHeadW:HeadWf hs) (hHead:TableTraffic HeadV3.interactions tr 1 pub (headTraffic hs))
    (hpubP:∀seg∈AP.pubSegs,seg.bus≠B_PARENT)
    (hpubVP:∀seg∈AP.pubSegs,seg.bus≠B_VPARENT)
    (hpubE:∀seg∈AP.pubSegs,seg.bus≠B_EDGE)
    (hpubBM:∀seg∈AP.pubSegs,seg.bus≠B_BMAP)
    (hpubKN:∀seg∈AP.pubSegs,seg.bus≠B_KEYNIB)
    (hpubF:∀msg,pubCount AP pub B_FINAL true msg=0)
    (hpubM:∀seg∈AP.pubSegs,seg.bus≠B_MEM)
    (overhead:Nat) (hpub:pub=ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)):
    ∃bs:List ListBlock,∃endRow:Nat,ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs endRow ∧
    ∃as:List AcctV,(as=[] ∨ AcctV3Wf as) ∧ TableTraffic AcctV3.interactions tr 6 pub (acctV3Traffic as) ∧
      ∀j,(hj:j<(bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)).length)→
      ∀k,(hk:k<(bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))[j].rs.length)→
      let x:=(bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))[j].rs[k]
      ∃a∈as,a.k=x.kslot ∧
        (Qv.Extract.queueTree vs es hs 0).find (NearSpec.accountKeyPath (toBytes x.v))=some (some (toBytes a.pre)) ∧
        NearSpec.Account.decode (toBytes a.pre)=some (Link.accOf a):=by
  have hL:=Assembly.ReceiptCandidateProof.repaired_local_base (ProcessRepairForeignByteTags.local_receipt view)
  obtain ⟨bs,endRow,hc⟩:=Assembly.ReceiptCandidateProof.extract_lists hL
  obtain ⟨ws,hW,hWr,hWT⟩:=ProcessRepairKeyView.walks view
  obtain ⟨as,haw,ha,hdecode⟩:=ProcessRepairAccountNative.authenticated view hpubS hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hHeadW hHead hpubP hpubVP
  refine ⟨bs,endRow,hc,as,haw,ha,?_⟩
  intro j hj k hk
  let ls:=bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)
  change k<ls[j].rs.length at hk
  let rn:=baseR ls j+k
  have hrn:rn<(flatR ls).length:=by
    have hh:=RcptLink.located_index_bound ls hj
    dsimp only [rn];omega
  have hget:(flatR ls)[rn]=ls[j].rs[k]:=by
    have he:=ProcessRepairReceiptKeyOwner.flat_lookup ls hj k hk
    change (flatR ls).getD rn default=ls[j].rs.getD k default at he
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hrn,
      List.getElem?_eq_getElem hk,Option.getD_some] using he
  obtain ⟨a,ham,hak⟩:=ProcessRepairReceiptMemOrigin.slots view hpubM haw ha hc rn hrn
  change a.k=(flatR ls)[rn].kslot at hak
  rw [hget] at hak
  obtain ⟨ve,hve,hvz,hvid,hbytes,_,hdec⟩:=hdecode a ham
  have hlookup:=ProcessRepairReceiptLookup.account view hpubS hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hHeadW hHead hpubP hpubVP hpubE hpubBM hpubKN
    hW hWr hWT hpubF hc overhead hpub j hj k hk
  change (Qv.Extract.queueTree vs es hs 0).find (NearSpec.accountKeyPath (toBytes ls[j].rs[k].v))=
    some (some (valOf (valsOf3 vs es) (vpos (vid0 es) ls[j].rs[k].kslot))) at hlookup
  rw [←hak,←hvid,Qv.Extract.native_value_at vs hVW hve,hbytes] at hlookup
  rw [hbytes] at hdec
  exact ⟨a,ham,hak,hlookup,hdec⟩
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptAccountReads
