import ZkFormal.NearV3.Candidates.ProcessRepairReceiptFinalFields
import ZkFormal.NearV3.Candidates.ProcessRepairForestLookup
import ZkFormal.NearV3.Qv.Extract.QueueRootRead
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptLookup
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open Sched Link3 RcptV3Proof

theorem account {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    {ws:List WalkR} (hW:WalkWf3 ws) (hWr:(ws.flatMap (·.steps)).length≤2^21)
    (hWT:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws))
    (hpubF:∀msg,pubCount AP pub B_FINAL true msg=0)
    {bs:List ListBlock} {endRow:Nat}
    (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs endRow)
    (overhead:Nat) (hpub:pub=ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead))
    (j:Nat) (hj:j<(bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)).length)
    (k:Nat) (hk:k<(bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))[j].rs.length):
    let x:=(bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))[j].rs[k]
    (Qv.Extract.queueTree vs es hs 0).find (NearSpec.accountKeyPath (toBytes x.v))=
      some (some (valOf (valsOf3 vs es) (vpos (vid0 es) x.kslot))) := by
  let ls:=bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)
  change k<ls[j].rs.length at hk
  let x:=ls[j].rs[k]
  let rn:=baseR ls j+k
  have hx:x∈flatR ls:=List.mem_flatMap.mpr ⟨ls[j],List.getElem_mem hj,List.getElem_mem hk⟩
  have hrn:rn<(flatR ls).length:=by
    have hh:=RcptLink.located_index_bound ls hj
    dsimp only [rn];omega
  have hcount:(flatR ls).length≤W_AK:=by
    have hn:=(ProcessRepairQueuePublic.receipt_count hprep overhead (hpub ▸ view) hc).2
    simpa [ls,flatR,List.flatMap_map,ListBlock.view,ListBlock.viewReceipts,List.length_flatMap,List.map_map] using hn
  have hmsg: [rn,0,FK_VAL,x.kslot]∈rcptRecvs3 ls B_FINAL:=ProcessRepairReceiptFinalFields.member ls hj hk
  obtain ⟨w,hwm,hfinal⟩:=ProcessRepairReceiptFinal.record view hpubF hWT hc hmsg
  have hslot:=(ProcessRepairReceiptReceiverShape.receiver view hc hx).2.2.2
  obtain ⟨hwid,hwtau,hwfk,hwslot⟩:=ProcessRepairReceiptFinalFields.fields hW hwm
    (show rn<P by unfold W_AK P at *;omega) hslot hfinal
  have hkey:=ProcessRepairReceiptNativeKey.prepared view hpubKN hprep overhead hpub hc hW hWT hwm
    (show w.w<(flatR ls).length by rw [hwid];exact hrn)
  have hget:(flatR ls).getD w.w default=x:=by
    rw [hwid]
    dsimp only [rn,x]
    rw [ProcessRepairReceiptKeyOwner.flat_lookup ls hj k hk]
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk]
  change w.key3=NearSpec.accountKeyPath (toBytes ((flatR ls).getD w.w default).v) at hkey
  rw [hget] at hkey
  obtain ⟨head,hhead,htau,hval,_⟩:=ProcessRepairForestLookup.lookup view hpubS hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hHeadW hHead hpubP hpubVP hpubE hpubBM
    (fun msg=>ZkFormal.Chacha.pubCount_zero (fun seg hseg hb=>absurd hb (hpubKN seg hseg)) msg) hW hWr hWT
    (List.mem_append_left _ hwm)
  have hheadEq:head=headAt hs 0:=by
    have he:=(hchain.head_all head hhead).2
    rwa [htau,hwtau] at he
  have hread:=hval hwfk
  rw [hheadEq,hkey,hwslot] at hread
  exact hread
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptLookup
