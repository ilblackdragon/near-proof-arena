import ZkFormal.NearV3.Candidates.ProcessRepairQueuePrepared
import ZkFormal.NearV3.Qv.Extract.QueueRootRead
namespace ZkFormal.NearV3.Candidates.ProcessRepairQueueCanonicalRead
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open Sched Link3 Qv.Extract
theorem read {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    {bs:List RcptV3Proof.ListBlock} {e:Nat}
    (hc:RcptV3Proof.ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e)
    (overhead:Nat) (hpub:pub=ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead))
    (q:Qv.Extract.WalkChain (ProcPriorRoutedKeyView.key tr) 0) (i:Nat) (hi:i<q.segs.length) :
    (queueTree vs es hs (cv (ProcPriorRoutedKeyView.key tr) 0 q.segs[i].1 Qv.Candidates.ValueTable.tau)).find
      (NearSpec.nibbles (physicalWalkBytes (ProcPriorRoutedKeyView.key tr) 0 q.segs[i]))=
      some (queueValue vs es (ProcPriorRoutedKeyView.key tr) 0 q.segs[i].1) := by
  obtain ⟨head,hh,ht,hval,habs⟩:=ProcessRepairQueuePrepared.lookup view hpubS hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hHeadW hHead hpubP hpubVP hpubE hpubBM hpubKN
    hW hWr hWT hpubF hc overhead hpub q i hi
  have he:=(hchain.head_all head hh).2
  rw [ht] at he
  rw [he] at hval habs
  have hl:=Qv.Candidates.KeyTrafficRepair.local_to_base (ProcessRepairKeyView.local_key view)
  have hb:=isBool hl (q.start_lt i hi) (x:=Qv.Candidates.CombinedTable.absent) (by simp [walkBools])
  rcases hb with hb|hb
  · have ha:cv (ProcPriorRoutedKeyView.key tr) 0 q.segs[i].1 Qv.Candidates.CombinedTable.absent=0:=by
      simp only [cv,hb];decide
    simp only [queueValue,ha,ite_true]
    simpa only [queueTree,cv,Chacha.cv,PubVal.val] using hval ha
  · have ha:cv (ProcPriorRoutedKeyView.key tr) 0 q.segs[i].1 Qv.Candidates.CombinedTable.absent=1:=by
      simp only [cv,hb];decide
    simp only [queueValue,ha,show ¬(1:Nat)=0 by decide,ite_false]
    simpa only [queueTree,cv,Chacha.cv,PubVal.val] using habs ha
theorem main_fixed {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    {bs:List RcptV3Proof.ListBlock} {e:Nat}
    (hc:RcptV3Proof.ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e)
    (overhead:Nat) (hpub:pub=ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead))
    (q:Qv.Extract.WalkChain (ProcPriorRoutedKeyView.key tr) 0) (i:Nat) (hi:i<q.segs.length)
    (hm:(ProcPriorRoutedKeyView.key tr).cell 0 q.segs[i].1 Qv.Candidates.CombinedTable.main=1)
    (hsmall:i<3) :
    (queueTree vs es hs 0).find (if i=0 then NearSpecV3.keyDelayedIdx else
      if i=1 then NearSpecV3.keyBufferedIdx else NearSpecV3.keyYieldIdx)=
      some (queueValue vs es (ProcPriorRoutedKeyView.key tr) 0 q.segs[i].1) := by
  have hr:=read view hpubS hpubV hpubD hpubB hpubC I hprep fwd hrec hNW hVW hN hV
    hw hchain hK hU hHeadW hHead hpubP hpubVP hpubE hpubBM hpubKN hW hWr hWT hpubF hc overhead hpub q i hi
  exact main_fixed_root_read (Qv.Candidates.KeyTrafficRepair.local_to_base
    (ProcessRepairKeyView.local_key view)) q i hi hm hsmall hr
end ZkFormal.NearV3.Candidates.ProcessRepairQueueCanonicalRead
