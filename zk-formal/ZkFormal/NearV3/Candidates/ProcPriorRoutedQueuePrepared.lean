import ZkFormal.NearV3.Candidates.ProcPriorRoutedQueueLookup
import ZkFormal.NearV3.Candidates.ProcPriorRoutedQueuePublic
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedQueuePrepared
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched
open Link3
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem lookup {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    (hHeadW:HeadWf hs) (hHead:TableTraffic HeadV3.interactions tr 1 pub (headTraffic hs))
    (hpubP:∀seg∈AP.pubSegs,seg.bus≠B_PARENT)
    (hpubVP:∀seg∈AP.pubSegs,seg.bus≠B_VPARENT)
    (hpubE:∀seg∈AP.pubSegs,seg.bus≠B_EDGE)
    (hpubBM:∀seg∈AP.pubSegs,seg.bus≠B_BMAP)
    (hpubKN:∀seg∈AP.pubSegs,seg.bus≠B_KEYNIB)
    {ws:List WalkR} (hW:WalkWf3 ws) (hWr:(ws.flatMap (·.steps)).length≤2^21)
    (hWT:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws))
    (hpubF:∀msg,pubCount AP pub B_FINAL true msg=0)
    {bs:List RcptV3Proof.ListBlock} {e:Nat}
    (hc:RcptV3Proof.ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e)
    (overhead:Nat) (hpub:pub=ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead))
    (q:Qv.Extract.WalkChain (ProcPriorRoutedKeyView.key tr) 0) (i:Nat) (hi:i<q.segs.length) :
    let src:=ProcPriorRoutedKeyView.key tr
    let r:=q.segs[i].1
    ∃h∈hs,h.tau=ZkFormal.Chacha.cv src 0 r Qv.Candidates.ValueTable.tau ∧
      (ZkFormal.Chacha.cv src 0 r Qv.Candidates.CombinedTable.absent=FK_VAL→
        (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find
          (NearSpec.nibbles (Qv.Extract.physicalWalkBytes src 0 q.segs[i]))=
        some (some (valOf (valsOf3 vs es) (vpos (vid0 es) (ZkFormal.Chacha.cv src 0 r Qv.Candidates.ValueTable.vid))))) ∧
      (ZkFormal.Chacha.cv src 0 r Qv.Candidates.CombinedTable.absent=FK_ABS→
        (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find
          (NearSpec.nibbles (Qv.Extract.physicalWalkBytes src 0 q.segs[i]))=some none) := by
  subst pub
  have hn:=(ProcPriorRoutedQueuePublic.receipt_count hprep overhead hH htables hc).2
  have hk:=ProcPriorRoutedQueuePublic.queue_count hprep overhead (ProcPriorRoutedKeyView.key tr) 0 0
  have hqk:(Qv.Candidates.CombinedTable.kPublic.eval (ProcPriorRoutedKeyView.key tr) 0 0
      (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead))).toNat<64:=by rw [hk.1];exact hk.2
  exact ProcPriorRoutedQueueLookup.lookup hH htables hpubS hpubV hpubD hpubB hpubC I hprep fwd hrec
    hNW hVW hN hV hw hchain hK hU hHeadW hHead hpubP hpubVP hpubE hpubBM hpubKN hW hWr hWT
    hpubF hc hn hqk q i hi
end ZkFormal.NearV3.Candidates.ProcPriorRoutedQueuePrepared
