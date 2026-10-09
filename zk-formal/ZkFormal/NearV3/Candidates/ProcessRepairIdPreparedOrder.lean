import ZkFormal.NearV3.Candidates.ProcessRepairIdGlobalOrder
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdPreparedOrder
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame
open ProcPriorRoutedRawSource (raw)
set_option maxRecDepth 32768
theorem ordered {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub40:∀seg∈AP.pubSegs,seg.bus≠40)
    (hpubS:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (hpubL:∀msg,pubCount AP pub 73 true msg=0)
    (hpubV:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    (hpubD:∀msg,pubCount AP pub B_DIGEST true msg=0)
    (hpubB:∀msg,pubCount AP pub B_BYTES true msg=0)
    (hpubC:∀seg∈AP.pubSegs,seg.bus≠64 ∧ seg.bus≠65 ∧ seg.bus≠66)
    (I:PubIdx AP pub Fp.ofNat) {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hprep:NearSpecV3.prepD0 cb hint=.ok p)
    (sp:NearSpecV3.Scheduler.SchedPub) (hsp:sp∈p.sched) (fwd:List (Nat×Nat))
    (h70:∀msg,pubCount AP pub 70 true msg=0)
    (hdl:I.recs B_SDL true=(render (p.sched.map instOf) fwd).dlSend)
    (hrec:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    {vs:List NodeS3} {es:List ValE}
    (hNW:NodeWf3 vs) (hVW:ValWf es)
    (hN:TableTraffic NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub (nodeTraffic3 vs))
    (hV:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    {v:List UpsSeg} (hw:Render.UpsRelay.Extract.Wf v) {hs:List HeadE} {K:Nat} {r0 rK:List Nat}
    (hchain:RootChain hs (v.map UpsRows.upsE) K r0 rK) (hK:K<33)
    (hU:TableTraffic Render.UpsRelay.compactInteractions (ProcPriorRoutedUpsView.ups tr) 0 pub (upsTraffic v))
    (hpubR:∀msg,pubCount AP pub 75 true msg=0)
    (hpub76:∀msg,pubCount AP pub 76 true msg=0)
    (hpub71:∀msg,pubCount AP pub 71 true msg=0)
    (hpubVP:∀seg∈AP.pubSegs,seg.bus≠B_VPARENT)
    {a b:Nat} (hab:a≤b) (hb:b<tr.height 0)
    (ha:ProcessRepairIdOrder.Live (raw tr) a) (hs:ProcessRepairIdOrder.Live (raw tr) b) :
    ProcessRepairIdLexOrder.Lex (raw tr) a b := by
  apply ProcessRepairIdGlobalOrder.ordered view hpub40 ?_ hab hb ha hs
  intro r hr hactive
  exact ProcessRepairIdRowBounds.active view hpubS hpubL hpubV hpubD hpubB hpubC I hprep sp hsp fwd h70 hdl hrec
    hNW hVW hN hV hw hchain hK hU hpubR hpub76 hpub71 hpubVP hr hactive.1 hactive.2
end ZkFormal.NearV3.Candidates.ProcessRepairIdPreparedOrder
