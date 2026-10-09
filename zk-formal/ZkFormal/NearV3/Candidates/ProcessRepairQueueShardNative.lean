import ZkFormal.NearV3.Candidates.ProcessRepairQueueShardBalance
import ZkFormal.NearV3.Candidates.ProcessRepairValueRange
namespace ZkFormal.NearV3.Candidates.ProcessRepairQueueShardNative
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open Qv Qv.Extract Qv.Candidates.ValueTable Sched
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
    (hpubQ:∀seg∈AP.pubSegs,seg.bus≠B_QSH)
    (q:WalkChain (ProcPriorRoutedKeyView.key tr) 0)
    (pc:ParserChain (ProcPriorRoutedKeyView.key tr) 0 (segEnd 0 q.segs))
 :
    ∃shards:Nat×Nat→List Nat,
      (∀p∈pc.segs,(ProcPriorRoutedKeyView.key tr).cell 0 p.1 mBuffer=1→
        ∃e∈es,e.vz=false ∧ e.vid=cv (ProcPriorRoutedKeyView.key tr) 0 p.1 vid ∧ e.len=p.2 ∧
          BufferedValue (some (toBytes e.bytes)) (shards p)) ∧
      ((List.range (segEnd 0 q.segs)).flatMap
        (fun r=>rowTraffic Qv.Candidates.CombinedTable.interactions (ProcPriorRoutedKeyView.key tr) 0 r pub B_QSH false)).Perm (
        pc.segs.flatMap (fun p=>if (ProcPriorRoutedKeyView.key tr).cell 0 p.1 mBuffer=1 then
          Parser.nativeShardMessages ((ProcPriorRoutedKeyView.key tr).cell 0 p.1 tau) (shards p) else [])) := by
  have hb:=ProcessRepairValueRange.bytes view hpubS hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubVP
  exact ProcessRepairQueueShardBalance.balance view hpubV hpubQ hVW hV hb q pc
end ZkFormal.NearV3.Candidates.ProcessRepairQueueShardNative
