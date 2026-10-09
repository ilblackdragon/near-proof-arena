import ZkFormal.NearV3.Candidates.ProcessRepairForestLookup
import ZkFormal.NearV3.Candidates.ProcessRepairFinalSource
import ZkFormal.NearV3.Qv.Extract.QueueRootRead
namespace ZkFormal.NearV3.Candidates.ProcessRepairFinalLookup
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open Sched Link3

theorem received {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    (hpubKN:∀msg,pubCount AP pub B_KEYNIB true msg=0)
    {ws:List WalkR} (hW:WalkWf3 ws) (hWr:(ws.flatMap (·.steps)).length≤2^21)
    (hWT:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws))
    (hpubF:∀msg,pubCount AP pub B_FINAL true msg=0)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=B_FINAL) (hsend:i.send=false)
    (hm:i.multNat tr t r pub≠0) :
    ∃w∈ws,Msg.toFp [w.w,w.tau,w.fk,w.k]=i.msgVal tr t r pub ∧
      (w.fk=FK_VAL→(Qv.Extract.queueTree vs es hs w.tau).find w.key3=
        some (some (valOf (valsOf3 vs es) (vpos (vid0 es) w.k)))) ∧
      (w.fk=FK_ABS→(Qv.Extract.queueTree vs es hs w.tau).find w.key3=some none) := by
  obtain ⟨w,hwmem,hmsg⟩:=ProcessRepairFinalSource.received view hpubF hWT ht hr hi hb hsend hm
  have hwall:w∈UpsRows.allWalks ws v:=by
    exact List.mem_append_left _ hwmem
  obtain ⟨head,hhead,htau,hval,habs⟩:=ProcessRepairForestLookup.lookup view hpubS hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hHeadW hHead hpubP hpubVP hpubE hpubBM hpubKN
    hW hWr hWT hwall
  have hheadEq:head=headAt hs w.tau:=by
    have h:=(hchain.head_all head hhead).2
    rwa [htau] at h
  subst head
  exact ⟨w,hwmem,hmsg,hval,habs⟩
end ZkFormal.NearV3.Candidates.ProcessRepairFinalLookup
