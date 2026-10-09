import ZkFormal.NearV3.Candidates.ProcessRepairRecordAuthenticatedTop
import ZkFormal.NearV3.Candidates.ProcPriorRecordBackwardBoundary
namespace ZkFormal.NearV3.Candidates.ProcessRepairRecordWriteSummary
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRecordTable
open ProcPriorRoutedRawSource (raw)
theorem write_summary {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpubS:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (hpubR:∀msg,pubCount AP pub 75 true msg=0)
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
    {r:Nat} (hr:r<tr.height 0)
    (hs:ZkFormal.Chacha.cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (hwrite:ZkFormal.Chacha.cv (raw tr) 0 r writeGate=1) :
    ∃q,r=q+2 ∧ q<tr.height 0 ∧
      ZkFormal.Chacha.cv (raw tr) 0 q (ProcPriorVertical4Linear.stage 3)=1 ∧
      ZkFormal.Chacha.cv (raw tr) 0 q firstLimb=1 ∧
    ProcPriorSummary.low (ProcPriorRecordSummarySound.word (raw tr) 0 q)=ZkFormal.Chacha.cv (raw tr) 0 r lo ∧
      ProcPriorSummary.big (ProcPriorRecordSummarySound.word (raw tr) 0 q)=decide (ZkFormal.Chacha.cv (raw tr) 0 r big=1) ∧
      ∀fair:Nat,(if ZkFormal.Chacha.cv (raw tr) 0 r big=1 then 4500000
        else min (ZkFormal.Chacha.cv (raw tr) 0 r lo+fair) 4500000)=
        min (min (ProcPriorRecordSummarySound.word (raw tr) 0 q+fair) NearSpecV3.Scheduler.u64Max) 4500000 := by
  have hv:=ProcessRepairRawBytes.overlay_local view
  obtain ⟨_,htop,_,_⟩:=ProcPriorRecordSound.write_flags hv hr hs hwrite
  obtain ⟨q,heq,hq,hsq,hfq⟩:=ProcPriorRecordBackwardBoundary.top_origin hv hr hs htop
  have hsummary:=ProcessRepairRecordAuthenticatedTop.top_summary view hpubS hpubR hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubVP hq hsq hfq
  refine ⟨q,heq,hq,hsq,hfq,?_⟩
  simpa only [←heq] using hsummary
end ZkFormal.NearV3.Candidates.ProcessRepairRecordWriteSummary
