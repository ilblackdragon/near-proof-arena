import ZkFormal.NearV3.Candidates.ProcessRepairNativeQueueReads
import ZkFormal.NearV3.Candidates.ProcessRepairForestRoot
namespace ZkFormal.NearV3.Candidates.ProcessRepairNativeQueueState
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open Sched Link3 Qv Qv.Extract
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
    (hpubQ:∀seg∈AP.pubSegs,seg.bus≠B_QSH)
    (hpubQC:∀seg∈AP.pubSegs,seg.bus≠Qv.Candidates.ValueTable.B_QVC)
    (overhead:Nat) (hpub:pub=ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) :
    (queueTree vs es hs 0).wf=true ∧
    (queueTree vs es hs 0).hashOf.map UInt8.toNat=r0 ∧
    ∃mv:MainValues,mv.Valid ∧ mv.Reads (queueTree vs es hs 0) (queueTree vs es hs 0) (queueTree vs es hs 0) ∧
      ∀t,1≤t→t≤p.hdr.K→(missingRequest (queueTree vs es hs t)).Holds (queueTree vs es hs t) := by
  obtain ⟨hwf,hroot⟩:=ProcessRepairForestRoot.pre view hpubS hpubV hpubD hpubB hpubC I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hHeadW hHead hpubP hpubVP
  exact ⟨hwf,hroot,ProcessRepairNativeQueueReads.authenticated view hpubS hpubV hpubD hpubB hpubC I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hHeadW hHead hpubP hpubVP hpubE hpubBM hpubKN hpubF hpubQ hpubQC overhead hpub⟩
end ZkFormal.NearV3.Candidates.ProcessRepairNativeQueueState
