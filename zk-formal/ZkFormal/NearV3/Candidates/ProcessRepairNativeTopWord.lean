import ZkFormal.NearV3.Candidates.ProcessRepairNativeWriteField
import ZkFormal.NearV3.Candidates.ProcessRepairRecordAuthenticatedWord
namespace ZkFormal.NearV3.Candidates.ProcessRepairNativeTopWord
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame
open ProcPriorRoutedRawSource (raw)
theorem limbs {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpubS:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (hpubL:∀msg,pubCount AP pub 73 true msg=0)
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
    (hpubR:∀msg,pubCount AP pub 75 true msg=0)
    (hpubVP:∀seg∈AP.pubSegs,seg.bus≠B_VPARENT)
    {r:Nat} (hr:r<tr.height 0)
    (hs:ZkFormal.Chacha.cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (htop:ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.topLimb=1) :
    ∃f,∃bs:NearSpec.Bytes,∃st:NearSpec.Bandwidth.State,∃link:NearSpec.Bandwidth.LinkAllowance,
      f<tr.height 0 ∧ ZkFormal.Chacha.cv (raw tr) 0 f first=1 ∧
      ZkFormal.Chacha.cv (raw tr) 0 f tau=ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.tau ∧
      bs.map UInt8.toNat=(es[ZkFormal.Chacha.cv (raw tr) 0 f vid]!).bytes ∧
      NearSpec.Bandwidth.State.decode bs=some st ∧
      st.links[ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.record]?=some link ∧
      ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.lo=ProcPriorIdLimbs.lo (ProcPriorRecordNativeField.selected (raw tr) 0 r link) ∧
      ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.mid=ProcPriorIdLimbs.mid (ProcPriorRecordNativeField.selected (raw tr) 0 r link) ∧
      ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.hi=ProcPriorIdLimbs.hi (ProcPriorRecordNativeField.selected (raw tr) 0 r link) := by
  have hv:=ProcessRepairRawBytes.overlay_local view
  obtain ⟨q,heq,hq,hsq,hfq⟩:=ProcPriorRecordBackwardBoundary.top_origin hv hr hs htop
  obtain ⟨f,bs,st,link,hfh,hff,htau,hbs,hd,hlink,hword,_⟩:=ProcessRepairNativeWord.word view
    hpubS hpubL hpubV hpubD hpubB hpubC I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubR hpubVP hq hsq hfq
  have hid:=ProcPriorRecordWordIdentity.limb_identity hv hq hsq hfq 2 (by decide)
  have hfields:=(ProcPriorRecordTopSummary.fields hv hq hsq hfq).2.2.2
  rw [←heq] at hid hfields
  have heSelected:ProcPriorRecordNativeField.selected (raw tr) 0 r link=ProcPriorRecordNativeField.selected (raw tr) 0 q link:=by
    unfold ProcPriorRecordNativeField.selected
    rw [hfields ProcPriorRecordTable.sender (by simp),hfields ProcPriorRecordTable.receiver (by simp)]
  have hb:=ProcessRepairRecordAuthenticatedWord.word_bounds view hpubS hpubR hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubVP hq hsq hfq
  have hdigits:ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.lo=ProcPriorIdLimbs.lo (ProcPriorRecordNativeField.selected (raw tr) 0 q link) ∧
      ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.mid=ProcPriorIdLimbs.mid (ProcPriorRecordNativeField.selected (raw tr) 0 q link) ∧
      ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.hi=ProcPriorIdLimbs.hi (ProcPriorRecordNativeField.selected (raw tr) 0 q link):=by
    unfold ProcPriorRecordSummarySound.word at hword
    unfold ProcPriorIdLimbs.lo ProcPriorIdLimbs.mid ProcPriorIdLimbs.hi
    omega
  refine ⟨f,bs,st,link,hfh,hff,htau.trans hid.1.symm,hbs,hd,?_,?_,?_,?_⟩
  · rw [hid.2];exact hlink
  · rw [hfields ProcPriorRecordTable.lo (by simp),heSelected];exact hdigits.1
  · rw [hfields ProcPriorRecordTable.mid (by simp),heSelected];exact hdigits.2.1
  · rw [hfields ProcPriorRecordTable.hi (by simp),heSelected];exact hdigits.2.2
end ZkFormal.NearV3.Candidates.ProcessRepairNativeTopWord
